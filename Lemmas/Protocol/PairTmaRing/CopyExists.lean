-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.RingFacts

@[expose] public section

/-! # Every copy of an observed use exists

A proof tool over `Hyp` (as the production GEMM's `copy_exists`, for any slot). Consumer `b`'s
successful full poll for use `r` observed every item of use `r` (`consumer_observes`), so for each
producer `a` and index `j < n` producer `a` issued the copy on the full barrier with `n r + j`
earlier ones there (`copy_exists`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

/-- **Every copy of an observed use exists.** -/
theorem copy_exists (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {r : Nat}
    (hr : r < okPolls S.full (X.tr (S.cons b))) (a : Fin 2) {j : Nat} (hj : j < S.n) :
    ∃ k pc al sp, X.get (S.prod a, k) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
      ((X.tr (S.prod a)).take k).countP (issuesTo S.full) = S.n * r + j := by
  have hk := copyKind_ne a j hj
  obtain ⟨hx, -, -⟩ := consumer_observes hX H hr (copyKind S.n a j hj)
  obtain ⟨-, ⟨e, he, hpe, hcnt⟩, -⟩ := SF_op H hx
  simp only [opF_ne hk, kOwner_copyKind, kPred_ne hk, kIdx_copyKind] at he hpe hcnt
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | tensorIssue al sp =>
    simp only [issuesTo, decide_eq_true_eq] at hpe
    exact ⟨_, pc, al, sp, he, hpe, hcnt⟩
  | _ => simp [issuesTo] at hpe

end
end PTX.PairTmaRing
