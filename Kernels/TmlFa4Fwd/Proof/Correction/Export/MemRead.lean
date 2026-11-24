-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemWrite
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Lib.LoadAt

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine

@[expose] public section

/-! # Where the correction warps' statistics loads read

A correction lane reads the statistics words of its row: the sum word (368) at a rescale and at the
final pass, the maximum word (1392) at the final pass, of stage 0 and of stage 1 (512 further):
`stat_rd`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxRecDepth 100000 in
theorem statW_words : ∀ i < 512, (shl (andi (BitVec.ofNat 64 i) 127) 2).toNat = 4 * (i % 128) := by
  decide +kernel

theorem statW_val (hp : Pre p L m) : (statW L g).toNat = L.sharedBase + 4 * rowN L g := by
  have hs := hp.shared.2.1
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have h := statW_words _ hi
  rw [← tidW_eq hp] at h
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have h3 := iv_add32 (iv_sb hp) (y := shl (rowW L g) 2) ⟨h.ge, h.le⟩ (by omega)
  unfold Iv at h3
  simp only [statW, rowN] at h3 ⊢
  omega

/-- The word a statistics site reads: the sum (`0`) or the maximum (`1`), and its stage. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.statRd : Site → Option (Fin 2 × Fin 2)
  | .rscale st => some (0, st)
  | .fsum st => some (0, st)
  | .fmax st => some (1, st)
  | _ => none

/-- The bytes of a statistics load from its offset. -/
theorem statRd_of (hp : Pre p L m) {n st : Fin 2} {off : Int} {acc : Acc}
    (ho : off = ((368 + 1024 * n.val + 512 * st.val : Nat) : Int))
    (hl : acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 (statW L g) + BitVec.ofInt 64 off)).toNat + 4 * 0⟩)
    (hz : acc.size = 4) : acc.size = 4 ∧ acc.loc = ⟨.shared, g / L.block,
      L.sharedBase + 368 + 1024 * n.val + 4 * (128 * st.val + rowN L g)⟩ := by
  have hsb := hp.shared
  have hv := statW_val (g := g) hp
  have hr : rowN L g < 128 := Nat.mod_lt _ (by decide)
  have hn := n.isLt
  have hst := st.isLt
  subst ho
  rw [eff_shared (by omega)] at hl
  refine ⟨hz, hl.trans ?_⟩
  simp only [Loc.mk.injEq, true_and]
  omega

set_option maxHeartbeats 4000000 in
/-- **What a statistics load of the correction warps reads.** -/
theorem stat_rd (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t) (hi : (Control.code p L g).inv d)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    {n st : Fin 2} (hs : d.site.statRd = some (n, st)) {acc : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .rd acc bs) : acc.size = 4 ∧ acc.loc = ⟨.shared, g / L.block,
      L.sharedBase + 368 + 1024 * n.val + 4 * (128 * st.val + rowN L g)⟩ := by
  have hreg : ∀ r ∈ Control.live d, t.regs r = some (Control.valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = 0 := by
    have h0 : d.k = 0 := by
      rcases hi with hi | hi
      · exact hi
      · exfalso
        revert hs hi
        cases d.site <;> simp [Site.statRd, Site.midOk]
    rw [h.2.1]
    exact congrArg Fin.val h0
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  cases site
  case rscale st' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    fin_cases st' <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      obtain ⟨h1, h2⟩ := ldShared_rd rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) hf hk
      rw [hsub] at h1
      exact statRd_of hp rfl h1 h2
  case fsum st' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    fin_cases st' <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      obtain ⟨h1, h2⟩ := ldShared_rd rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) hf hk
      rw [hsub] at h1
      exact statRd_of hp rfl h1 h2
  case fmax st' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    fin_cases st' <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      obtain ⟨h1, h2⟩ := ldShared_rd rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) hf hk
      rw [hsub] at h1
      exact statRd_of hp rfl h1 h2
  all_goals cases hs

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
