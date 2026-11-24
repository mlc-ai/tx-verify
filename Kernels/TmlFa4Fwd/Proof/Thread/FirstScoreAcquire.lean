-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Order.WarpBarOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Assumption PTX.AsyncCopy PTX.MBarrier Prologue Softmax

/-- The first successful score acquire, at the entry to the producer's softmax loop. -/
@[no_expose] def FirstScoreAcquire (l : Launch) (X : Execution) (i : EvId) (stage : Fin 2) :
    Prop :=
  X.get i = some ⟨3425,.wait (scoreReadyObject l (i.1/l.block) stage) 0 true true .cta⟩

theorem FirstScoreAcquire.ofDecoded {l : Launch} {X : Execution}
    {i : EvId} {stage : Fin 2}
    (he : X.get i = some ⟨3425,.wait (scoreReadyObject l (i.1/l.block) stage)
      0 true true .cta⟩) : FirstScoreAcquire l X i stage :=
  he

/-- The abstract opening acquire has the checked instruction and parity. -/
theorem FirstScoreAcquire.decoded {l : Launch} {X : Execution} {i : EvId} {stage : Fin 2}
    (hi : FirstScoreAcquire l X i stage) :
    X.get i = some ⟨3425,.wait (scoreReadyObject l (i.1/l.block) stage)
      0 true true .cta⟩ :=
  hi

/-- The opening acquire uses the score object of its actual softmax warp. -/
theorem FirstScoreAcquire.role {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {i : EvId} {stage : Fin 2} (hi : FirstScoreAcquire l X i stage)
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    warpIndex l i.1 < 8 ∧ warpIndex l i.1/4 = stage.val := by
  rcases i with ⟨g,j⟩
  obtain ⟨hWarp,hLoc⟩ := scoreReadyWaitStage hp hX hi (by decide)
  have hEqual := congrArg Loc.addr hLoc
  change l.sharedBase+(80+8*stage.val) = l.sharedBase+(80+8*(warpIndex l g/4)) at hEqual
  change warpIndex l g < 8 ∧ warpIndex l g/4 = stage.val
  exact ⟨hWarp,by omega⟩

/-- An actual opening acquire's record and physical observed generation. -/
theorem FirstScoreAcquire.observation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {i : EvId} {stage : Fin 2} (hi : FirstScoreAcquire l X i stage)
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    let log := X.objects (scoreReadyObject l (i.1/l.block) stage)
    ∃ (k phase : Nat) (poll : Record Ref), log[k]? = some poll ∧ poll.id = .thread i ∧
      poll.reply.waited = some true ∧ observedAt log k = some phase := by
  unfold FirstScoreAcquire at hi
  obtain ⟨k,poll,hRecord,hId,hAct,_,hOk⟩ := actualPollRecordClean hp hX hi
  obtain ⟨st,n,hState,hA,hParity,hFinished⟩ :=
    (X.objects_checked hX (scoreReadyObject l (i.1/l.block) stage)).okPoll hRecord hOk
  have hZero : n = 0 := (Action.pollParity.inj (hA.symm.trans hAct)).1
  have hPos : 0 < st.phase := by omega
  refine ⟨k,st.phase-1,poll,hRecord,hId,hOk,?_⟩
  simp only [observedAt,hRecord,Option.bind_some,hFinished,ite_eq_left hPos]

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
