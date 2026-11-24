-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageRead
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Kernel.FrameU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow Softmax

private theorem bld_sites : allSites.all (fun s => [false,true].all fun b =>
    (List.finRange 16).all fun j => s.pc != (Site.bld b j).pc || s == .bld b j) = true := by
  decide +kernel

/-- Identify the control state at a trace read by its decoded bias-load PC. -/
theorem bias_state_at {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (b : Bool) (j : Fin 16)
    (he : X.get (g,i) = some ⟨(Site.bld b j).pc,.rd a bs⟩) :
    ∃ v k acc n, Frame.stateAt (thread p L) X g i =
      some (some (SmWarp.sinj p L g ⟨.bld b j,v,k,acc⟩ n)) := by
  have hub : ∀ f, (⟨(Site.bld b j).pc,.rd a bs⟩ : Event).kind ≠ .ub f := by intro _ h; cases h
  rcases SmWarp.open_ev hp hX hf hw he hub with ⟨_,_,_,_,_,hi,ev⟩ | ⟨d,n,hs,_⟩
  · exact (start_mem ev hi.2 trivial).elim
  have pcEq : d.site.pc = (Site.bld b j).pc :=
    (Frame.event_pcU (fun _ hg => thread_sound hp hg) hX he hs hub).symm
  have h := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp bld_sites d.site (mem_allSites _)) b (by cases b <;> simp))
    j (List.mem_finRange j)
  have eq : d.site = .bld b j := by simpa only [pcEq, bne_self_eq_false, Bool.false_or,
    beq_iff_eq] using h
  obtain ⟨site,v,k,acc⟩ := d
  change site = _ at eq
  subst site
  exact ⟨_,_,_,_,hs⟩

/-- The stage, row and credit of a traced bias read at one of the packed load PCs. -/
theorem soft_bias_read_at {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (b : Bool) (j : Fin 16)
    (he : X.get (g,i) = some ⟨(Site.bld b j).pc,.rd a bs⟩) :
    okPolls (sobj L g 320) ((X.tr g).take i) =
      ((X.tr g).take i).countP (Execution.isBarId (stageId (Prologue.warpIndex L g / 4))) + 1 ∧
      a.size = 4 ∧ a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ a.loc.addr % 4 = 0 ∧
      ∃ q : Fin 2, a.loc.addr / 128 =
        (L.sharedBase + 128 * (g % L.block % 128) + 32768 * (Prologue.warpIndex L g / 4) +
          166912 + 16384 * q.val) / 128 := by
  obtain ⟨v,k,acc,n,hs⟩ := bias_state_at hp hX hf hw b j he
  exact (soft_bias_read hp hX hf he hs (by rfl) rfl).2.2

end PTX.Kernels.TmlFa4Fwd.Proof
