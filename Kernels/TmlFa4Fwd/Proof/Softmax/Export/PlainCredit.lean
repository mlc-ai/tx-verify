-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageBar
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemSite
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

private theorem plain_points (b : Bool) (q : Fin 4) :
    (ptsOf b (.acquire 80)).countP (Softmax.before (.pst .plain q))=2 ∧
    (ptsOf b (.acquire 80)).countP inBias=1 ∧ (ptsOf b (.acquire 80)).countP inPlain=1 := by
  cases b <;> fin_cases q <;> decide +kernel

/-- The credit of an actual plain-round P store comes after all rounds with bias reads. -/
theorem soft_plain_credit {p L m X g i e q v k acc u} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hw : Prologue.warpIndex L g<8)
    (he : X.get (g,i) = some e) (hs : softState p L X g i = some ⟨.pst .plain q,v,k,acc⟩)
    (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1) :
    ∃ B, StageRounds p L g B ∧ B<u := by
  unfold softState at hs
  split at hs
  · rename_i d n hd
    obtain rfl := Option.some.inj hs
    have hc := control_of_data hp hd
    obtain ⟨⟨c,⟨⟨rb,rp,hQ⟩⟩,link⟩,fit⟩ :=
      ((SmWarp.good hp hX hw (Frame.lt_of_get hX he) rfl i).2 _ hc).2 (ub_zero hX he hc)
    obtain ⟨ef,uk⟩ := fit
    simp only [SmWarp.toE,Epilogue.Fits,Control.D.scheduler,SmWarp.epi] at ef
    obtain ⟨R,bal,chosen,h0,h1⟩ := ef
    obtain ⟨fixed,_⟩ := nBP chosen h0 h1 (uk (by rfl))
    have region : inPlain (Site.pst .plain q).pos = true := by fin_cases q <;> decide
    obtain ⟨_,_,_,done⟩ := hQ.plain region
    have count := hQ.cnt (.acquire 80) rfl
    obtain ⟨first,bias,plain⟩ := plain_points (lz L g) q
    change c (.acquire 80) = passed _ (.pst .plain q) rb rp at count
    simp only [passed,first,bias,plain,Nat.mul_one] at count
    rw [(link (.acquire 80) rfl)] at count
    refine ⟨rb,⟨R,bal,chosen.1,?_⟩,?_⟩
    · rw [← fixed]
      have nat_of_done {r : Nat} {n : Int} (h : Done r n) : n.toNat = r := by
        rcases h with h | ⟨rfl,h⟩ <;> omega
      exact nat_of_done done
    · have polls := (tm_counts hw hc).1
      omega
  · cases hs

end PTX.Kernels.TmlFa4Fwd.Proof.Values
