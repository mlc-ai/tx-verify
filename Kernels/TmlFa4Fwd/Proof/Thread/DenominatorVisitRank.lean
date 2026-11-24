-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Thread.Scores

/-- A recorded numerical continuation strictly precedes its lane's terminal event. -/
theorem denominatorRunIndex_lt {l : Launch} {X : Execution} {g j : Nat} {s : TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop j) none) :
    j < (X.tr g).length := by
  by_contra! h
  rw [List.drop_eq_nil_iff.mpr h] at hRun
  cases hRun

/-- An exact single publication advances the stage's observed packet rank. -/
theorem probabilityRankOfRepeatedVisit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j e : Nat} (stage : Fin 2) (hWarp : warpIndex l g < 8)
    (hStage : warpIndex l g/4 = stage.val)
    (hj : j < (X.tr g).length) {s : TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop e) none)
    (hCount : ((X.tr g).take e).countP earlyProbabilityMark =
      ((X.tr g).take j).countP earlyProbabilityMark + 1) :
    probabilityOrdinal l X (g/l.block) stage 0 (g,e) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,j) + 1 := by
  rwa [earlyProbabilityCount hp hX stage hWarp hStage (denominatorRunIndex_lt hRun),
    earlyProbabilityCount hp hX stage hWarp hStage hj] at hCount

end PTX.Kernels.TmlFa4Fwd.Softmax
