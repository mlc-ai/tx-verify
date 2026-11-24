-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
import Kernels.TmlFa4Fwd.Proof.Common.DataTrace
import Kernels.TmlFa4Fwd.Proof.Softmax.Data.SumPos
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The row sum of a softmax lane's row data is nonnegative -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The row sum is nonnegative** at a data state of a softmax lane. -/
theorem softState_rs_nonneg (hp : Pre p L m) {i : Nat} {d : Softmax.D} (hi : i ≤ (X.tr g).length)
    (hs : softState p L X g i = some d) : 0 ≤ d.v.rs := by
  unfold softState at hs
  split at hs
  · rename_i d' n hst
    cases hs
    refine role_induct (r := .softmax) (Q := fun _ (d : Softmax.D) => 0 ≤ d.v.rs)
      (fun _ => le_refl (0 : ℝ)) (fun {i d d' n e} _ _ h hn => ?_) hi hst
    change (SmWarp.codeT p L g).next d e = _ at hn
    rw [SmWarp.next_eq (SmWarp.numSteps hp)] at hn
    rcases Softmax.Data.succ_rs hn with h' | ⟨r, h'⟩
    · rw [h']; exact h
    · rw [h']; exact Softmax.Data.sumAfter_nonneg hp g h r
  · cases hs

/-- **The row sum of a lane's row data is nonnegative.** -/
theorem softRow_rs_nonneg (hp : Pre p L m) : 0 ≤ (softRow p L X g).rs := by
  change 0 ≤ ((wordState p L X g (softRounds p L g - 1)).map (·.v.rs)).getD 0
  cases h : wordState p L X g (softRounds p L g - 1) with
  | none => exact le_rfl
  | some d =>
    refine softState_rs_nonneg hp ?_ h
    unfold nthEv
    split
    · rename_i hex
      obtain ⟨e, he, -⟩ := Classical.choose_spec hex
      exact (List.getElem?_eq_some_iff.mp he).1.le
    · exact le_rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
