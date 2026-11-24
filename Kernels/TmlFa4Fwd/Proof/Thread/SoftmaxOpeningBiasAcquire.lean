-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningLoads
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasFirstVisit
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningWaitHistory
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (stage : Fin 2) (hStage : warpIndex l g / 4 = stage.val)
    {F : List (Nat × Value)} {ending : Option TState} (c : OpeningLaneCursor l X g 3498 F ending)
    (hBase : (2771,b32 (waitLoc l g stage 2).addr) ∈ F) (hParity : (2770,b32 0) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 9752)
    (hReady : okPolls (Thread.Loader.biasReadyObject l (g/l.block) stage) (X.tr g) = 0 →
      OpeningPollReady X (waitLoc l g stage 2) 0)
include hp hMax hg hw stage hStage c hBase hParity hFresh hReady

/-- The pending first Bias poll consumes its opening delivery in a maximal execution
and keeps the decoded register frame through the success branch. -/
theorem openingBiasAcquireOfCursorWithTcCount :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      ∃ after : OpeningLaneCursor l X g 3501 F ending, after.pos = j + 1 ∧
        ((X.tr g).take after.pos).countP isTcColl = ((X.tr g).take c.pos).countP isTcColl := by
  obtain ⟨retry,after,ready,he,hPast,hTail,hLocal,hAt,hCount⟩ :=
    waitOfMaximalWithTcCount hp hMax hg stage 2 (phase := 0) (by decide) hFresh hBase hParity
      (fun hr hl ht => hReady (noBiasAtOpeningCursor hp hMax.1 hr hl ht.1 stage hw hStage))
      c.positive c.bounded c.released c.checkpoint c.recorded c.continuation c.localSteps
  exact ⟨c.pos+retry,he,⟨c.pos+retry+1,after,ready,Nat.succ_pos _,len_of_get he,
    releasedIfLast he (by intro h; cases h),hPast,hTail,hLocal,hAt⟩,rfl,hCount⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
