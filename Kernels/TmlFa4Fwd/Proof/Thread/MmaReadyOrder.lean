-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow
open Observation (readyObject)

noncomputable section

/-- Failed retries, other events and a truncated trace leave every ready ordinal unchanged. -/
theorem readyCountsUnchanged {l : Launch} {X : Execution} {g index : Nat}
    (hNone : ∀ slot parity acquire scope, ¬ ReadyPoll l X g index slot parity acquire scope)
    (i : Fin 3) :
    (atPrefix l X g (index + 1)).kvAcquires i = (atPrefix l X g index).kvAcquires i := by
  cases he : X.get (g, index) with
  | none =>
    change (X.tr g)[index]? = none at he
    have hTake : (X.tr g).take (index + 1) = (X.tr g).take index := by
      simp [List.take_add_one, he]
    simp [atPrefix, hTake]
  | some e =>
    have hFalse : okPoll (readyObject l g i) e = false := by
      unfold okPoll sourceWaitSuccess
      split
      · rename_i target parity acquire scope hKind
        apply decide_eq_false
        intro hTarget
        subst target
        exact hNone i parity acquire scope ⟨e, he, hKind⟩
      · rfl
    rw [prefixStep he]
    simp [advance, Observation.tick, hFalse]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
