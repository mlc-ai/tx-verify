-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedRoundContinuation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX

noncomputable section

/-- Event offset of the first P notification after the first three stores complete. -/
def Repeated.probabilityCreditOffset : Repeated → Nat
  | .biased => 5
  | .unbiased => 4

/-- The first P notification publishes the early packet on this barrier. -/
def Repeated.earlySignal : Repeated → Fin 8
  | .biased => 4
  | .unbiased => 6

theorem Repeated.probabilityStoreOfRound {l : Launch} {X : Execution}
    (r : Repeated) (stage : Fin 2) {g j : Nat} {weights : Nat → ℝ}
    (hEvents : ∀ i : Fin (r.probabilityEvents l g stage weights).length,
      X.get (g,j+i.val) = (r.probabilityEvents l g stage weights)[i.val]?)
    (q : Fin 4) :
    X.get (g,j+r.probabilityStoreOffset q) =
      some (repeatedStoreEvent l g stage r.round q weights) := by
  cases r <;> fin_cases q
  · exact hEvents ⟨1,by change 1 < 7; decide⟩
  · exact hEvents ⟨2,by change 2 < 7; decide⟩
  · exact hEvents ⟨3,by change 3 < 7; decide⟩
  · exact hEvents ⟨6,by change 6 < 7; decide⟩
  · exact hEvents ⟨0,by change 0 < 6; decide⟩
  · exact hEvents ⟨1,by change 1 < 6; decide⟩
  · exact hEvents ⟨2,by change 2 < 6; decide⟩
  · exact hEvents ⟨5,by change 5 < 6; decide⟩

theorem Repeated.probabilityCreditOfRound {l : Launch} {X : Execution}
    (r : Repeated) (stage : Fin 2) {g j : Nat} {weights : Nat → ℝ}
    (hEvents : ∀ i : Fin (r.probabilityEvents l g stage weights).length,
      X.get (g,j+i.val) = (r.probabilityEvents l g stage weights)[i.val]?) :
    X.get (g,j+r.probabilityCreditOffset) = some ⟨(signalSite r.earlySignal).pc,
      .arrive (signalLoc l g stage r.earlySignal) 0 1 true .cta⟩ := by
  cases r
  · exact hEvents ⟨5,by change 5 < 7; decide⟩
  · exact hEvents ⟨4,by change 4 < 6; decide⟩

/-- The tail warp barrier follows the last store's own completion wait. -/
def Repeated.probabilityTailBarrierOffset : Repeated → Nat
  | .biased => 8
  | .unbiased => 7

theorem Repeated.probabilityTailBarrierOffset_eq (r : Repeated) (l : Launch) (g : Nat)
    (stage : Fin 2) (weights : Nat → ℝ) :
    r.probabilityTailBarrierOffset = (r.probabilityEvents l g stage weights).length+1 := by
  cases r <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Softmax
