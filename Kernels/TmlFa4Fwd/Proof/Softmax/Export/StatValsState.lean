-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StoreVals
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatValsIndex
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataFiring
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Lemmas.Order.OrderWaits
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Flow PTX.Proof

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i pc : Nat} {a : Acc}
  {bs : List Byte}

theorem stat_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    (he : X.get (g,i) = some ⟨pc,.wr a bs⟩) (hbefore : Values.LoadsBefore L X (g,i)) :
    ∃ (d : D), ∃ n c rb rp, Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.softmax,d⟩,n)) ∧
      d.site.pc = pc ∧ RefQ p L g (Control.erase d).scheduler c rb rp ∧
      SmWarp.SFits p L g (Control.erase d).scheduler (n .shfl) (n .vote) ∧
      Values.wordState p L X g (c .sst) = some d ∧
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) i = c (.acquire 80) := by
  rcases SmWarp.open_ev hp hX hf hw he (by intro f h; cases h) with
    ⟨_,_,_,_,_,hi,ev⟩ | ⟨d,n,hctl,h0,href,_,_⟩
  · exact (start_mem ev hi.2 trivial).elim
  obtain ⟨v,hs,rfl⟩ := SmWarp.lift_state hp hctl (SmWarp.alive_of_prefix_reads hp hX hw hb he (by
    rintro j hj b xs sh hl
    obtain rfl := (soft_ld hp hX hf hw hl).1
    obtain ⟨pc',hl'⟩ := hl
    exact hbefore _ _ _ ⟨pc',hl'⟩ rfl (.single (.inl (.single (.inl
      (po_of_source_not_access (e := (g,j)) (f := (g,i)) rfl hj (len_of_get he)
        (by rw [hl']; rfl))))))))
  obtain ⟨⟨c,⟨⟨rb,rp,hQ⟩⟩,linked⟩,hfit⟩ := href.2 h0
  have pcEq := Frame.event_pc (fun _ hg => threadD_sound hp hg) hX he hs
  refine ⟨v,n,c,rb,rp,hs,pcEq.symm,hQ,hfit,?_,(tm_counts hw hctl).1.trans (linked _ rfl).symm⟩
  have hc := (count_at (c := .sst) hw hctl rfl).trans (linked _ rfl).symm
  rw [Values.wordState, ← hc, nthEv_eq he (by rfl), Values.softState, hs]

private theorem stat_pc_table : allSites.all (fun s =>
    [Site.stat false, .stat true, .fin 0, .fin 1].all fun w => s.pc != w.pc || s == w) = true := by
  decide +kernel

theorem stat_site_of_pc {s w : Site} (hm : w ∈ [.stat false,.stat true,.fin 0,.fin 1])
    (heq : s.pc = w.pc) : s = w := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp stat_pc_table s (mem_allSites s)) w hm
  simpa only [heq, bne_self_eq_false, Bool.false_or, beq_iff_eq] using h

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
