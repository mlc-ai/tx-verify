-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ScoreLoadSources
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemReadConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.TmemInitialScoreStore
import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Tcgen05.TmemLatestSource
import Lemmas.Order.OrderBaseCausality
import Lemmas.Flow.CountTake
import Lemmas.Tcgen05.TcMmaResultLayout
import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma PTX.Flow Thread Thread.Scores Protocol.Scores
open PTX.Kernels.TmlFa4Fwd.Mma (qkStage initialQkBlock)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem scoreLoadBeforeLaterWriter (hJoint : CorrectionJointGuards l X) {load writer : EvId}
    {cell : Cell} {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage)
    (seen : ScoreLoadScore l X load stage) (hWriter : X.MmaCell writer cell)
    (hLater : seen.commit.2 ≤ writer.2) :
    WaitBefore l X .waitLd load writer := by
  obtain ⟨block,frag,d,op,acc,mask,hStage,hQk,hScope⟩ := hLoad.mmaWriter hp hX hWriter
  let hIssue : X.MmaIssue writer d op acc mask := ⟨_,hQk.decoded⟩
  have hRepeat : 2 ≤ block.val := by
    by_contra! hFirst
    have hBank : block = initialQkBlock stage := by
      have h := congrArg Fin.val hStage
      change block.val%2 = stage.val at h
      apply Fin.ext
      change block.val = stage.val
      omega
    exact (Nat.not_lt_of_ge hLater) (initialScoreIssueBeforeCommit hp hX stage
      (hBank ▸ hQk) seen.score hScope.2.2)
  obtain ⟨wait,hWait⟩ := hQk.recurringProbabilityAcquire hp hX hRepeat 0
  have hAcquire : MmaProbabilityAcquire l X writer stage 0 wait := hStage ▸ hWait
  exact scoreLoadBeforeGuardedMma hp hX hJoint hLoad seen hIssue hScope hLater hAcquire

private theorem scoreLoadMmaOrder (hJoint : CorrectionJointGuards l X) {load writer : EvId}
    {cell : Cell} {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage)
    (seen : ScoreLoadScore l X load stage) (hWriter : X.MmaCell writer cell) :
    DoneBefore l X writer load ∨ WaitBefore l X .waitLd load writer := by
  obtain ⟨block,frag,d,op,acc,mask,hStage,hQk,hScope⟩ := hLoad.mmaWriter hp hX hWriter
  let hIssue : X.MmaIssue writer d op acc mask := ⟨_,hQk.decoded⟩
  by_cases hPast : writer.2 < seen.commit.2
  · exact .inl (seen.doneBeforeEarlierMma hp hX hIssue hScope hPast)
  · exact .inr (scoreLoadBeforeLaterWriter hp hX hJoint hLoad seen hWriter
      (Nat.le_of_not_lt hPast))

/-- Every actual score load has a stable writer in the live score allocation. -/
theorem scoreLoadReadSource (hCuQ : Epilogue.DrainCuQProtected p X) {load : EvId} {cell : Cell}
    {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage) :
    ∃ source, ReadSource l X .ld source load cell := by
  have hWrites := tensorWritesSafeOfCuQ hp hX hCuQ
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨seen⟩ := scoreLoadObservesScore hp hX hJoint hLoad
  obtain ⟨source,_,_,_,_,hIssue,hCell,hCta,hEarlier⟩ := hLoad.qkCandidate hp hX seen.score
  have hDone := seen.doneBeforeEarlierMma hp hX hIssue hCta hEarlier
  obtain ⟨col,hGeometry⟩ := hLoad.geometry hp hX
  have hOwner : cell.cta = load.1/l.block := congrArg Cell.cta hGeometry
  apply readSourceOfCandidate hX hGuard hWrites (candidate := source) _ _
    (.inl hCell) (.inl (.inl hDone))
  · intro other hOther
    rcases hOther with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · rcases scoreLoadMmaOrder hp hX hJoint hLoad seen hMma with h | h
      · exact .inl (.inl (.inl h))
      · exact .inr (.inl h)
    · exact scoreLoadStoreOrdered hp hX hLoad hStore
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim
  · intro _ _ _ c r hr hCover release hRelease
    obtain ⟨hReleaseOwner,hDealloc⟩ := allocationReleaseInOwnerCta hX hr hRelease
    obtain ⟨_,_,_,hCellCta,_,_,_⟩ := hCover
    exact .inl (tensorOperationsCompletedBeforeRelease hp hX hCuQ
      (hOwner.symm.trans (hCellCta.trans hReleaseOwner.symm)) hDealloc)

private theorem earlierCommitBeforeSelectedQk {source earlier later : EvId} {cta : Nat}
    {stage : Fin 2} {oldSpec spec : TcCommit.Spec} {oldRank rank : Fin 16}
    (hOld : ScoreCommit l X earlier cta stage oldSpec oldRank)
    (hNew : ScoreCommit l X later cta stage spec rank)
    (hOrder : scoreCommitOrdinal l X cta stage earlier < scoreCommitOrdinal l X cta stage later)
    (hAdjacent : source.2+2 = later.2) : earlier.2 ≤ source.2 := by
  have hLane := scoreCommitSameIssuer hp hX hOld hNew
  have hBefore : earlier.2 < later.2 := by
    by_contra! h
    have hm := countP_take_mono (scoreCommitOn (scoreReadyObject l cta stage)) (X.tr later.1) h
    unfold scoreCommitOrdinal at hOrder
    rw [hLane] at hOrder
    omega
  obtain ⟨block,_,hCommit⟩ := scoreCommitSite hp hX hNew
  by_contra! h
  have hIdx : earlier.2 = later.2-1 := by omega
  obtain ⟨_,inst,leader,hElect,_⟩ := Mma.scoreCommitLeader hp hX block hCommit
  obtain ⟨_,hEarlier⟩ := hOld.1
  rw [show earlier = (later.1,later.2-1) from Prod.ext hLane hIdx] at hEarlier
  change X.get (later.1,later.2-1) = some ⟨_,.elect _ inst leader⟩ at hElect
  rw [hEarlier] at hElect
  cases congrArg Event.kind (Option.some.inj hElect)

private theorem selectedQkAfterPriorProbabilityStore (hJoint : CorrectionJointGuards l X)
    {load source store : EvId} {cell : Cell} {stage : Fin 2} {block : Fin 4} {d : Nat}
    {op : OperandSpec} {acc : Bool} {mask : List Nat} (hLoad : ScoreLoadCell l X load cell stage)
    (seen : ScoreLoadScore l X load stage) (hQk : QkInstruction X source block 7 d op acc mask)
    (hStage : qkStage block = stage) (hCell : X.MmaCell source cell)
    (hCta : SameCta l source.1 load.1) (hAdjacent : source.2+2 = seen.commit.2)
    (hStore : StoreCell l X store cell) (hBefore : store.2 < load.2) :
    StoreDoneBefore l X store source := by
  obtain ⟨hLane,⟨hFoot⟩⟩ := scoreLoadStoreScope hp hX hLoad hStore
  obtain ⟨old,hCursor⟩ := probabilityStoreObservesLatestScore hp hX hJoint stage hStore hFoot
  have hCount := scoreLoadStoreCursor hp hX hLoad hStore hBefore
  have hOwner := congrArg (· / l.block) hLane
  dsimp only at hCount
  rw [← hOwner,← hCursor,hOwner] at hCount
  have hScoreCount := hLoad.pollCursor hp hX
  rw [← seen.generation] at hScoreCount
  rw [hScoreCount] at hCount
  have hOrder : scoreCommitOrdinal l X (load.1/l.block) stage old.commit <
      scoreCommitOrdinal l X (load.1/l.block) stage seen.commit := by omega
  have hOld : ScoreCommit l X old.commit (load.1/l.block) stage old.spec old.rank :=
    hOwner ▸ old.score
  have hOlder := earlierCommitBeforeSelectedQk hp hX hOld seen.score hOrder hAdjacent
  have hRecurring : 2 ≤ block.val := by
    by_contra! hn
    have hb : block = initialQkBlock stage := by
      have he := congrArg Fin.val hStage
      change block.val%2 = stage.val at he
      apply Fin.ext
      change block.val = stage.val
      omega
    exact (Nat.not_lt_of_ge hOlder)
      (initialScoreIssueBeforeCommit hp hX stage (hb ▸ hQk) hOld hCta.2.2)
  have hGuard (packet : Fin 2) : ∃ w, MmaProbabilityAcquire l X source stage packet w :=
    hStage ▸ hQk.recurringProbabilityAcquire hp hX hRecurring packet
  obtain ⟨_,_,_,_,_,_,hIssue,hWrite⟩ := hCell
  have hOn := mmaAccumulatorOnStoreTile hp hX hFoot hIssue (writeCell_resultCell hWrite)
  exact probabilityStoreReuseOrder hp hX hJoint stage hStore hFoot hOn old hOlder hGuard

/-- Every score cell reads the final QK fragment of the commit it observes. Earlier
probability stores have completed before that fragment, including on aliased columns. -/
theorem scoreLoadSelectsQk (hCuQ : Epilogue.DrainCuQProtected p X) {load : EvId} {cell : Cell}
    {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage) :
    ∃ (seen : ScoreLoadScore l X load stage), ∃ source block d op acc mask,
      qkStage block = stage ∧ QkInstruction X source block 7 d op acc mask ∧
      source.1 = seen.commit.1 ∧ source.2+2 = seen.commit.2 ∧
      DoneBefore l X source load ∧ ReadSource l X .ld source load cell := by
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨seen⟩ := scoreLoadObservesScore hp hX hJoint hLoad
  obtain ⟨source,block,d,op,acc,mask,hStage,hQk,hCell,hCta,hLane,hAdjacent,hLatest⟩ :=
    hLoad.qkCandidateAdjacent hp hX seen.score
  let hIssue : X.MmaIssue source d op acc mask := ⟨_,hQk.decoded⟩
  have hDone := seen.doneBeforeEarlierMma hp hX hIssue hCta (by omega)
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  have hNe : source ≠ load := fun h => tcStep_acyclic hX hGuard load (h ▸ hDone.tcStep)
  refine ⟨seen,source,block,d,op,acc,mask,hStage,hQk,hLane,hAdjacent,hDone,
    hNe,.inl hCell,.inl (.inl hDone),?_,?_⟩
  · intro other hOther
    by_cases hEq : other = source
    · exact .inl hEq
    rcases hOther with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · obtain ⟨_,_,d',op',acc',mask',_,hOther,hSame⟩ := hLoad.mmaWriter hp hX hMma
      let hOtherIssue : X.MmaIssue other d' op' acc' mask' := ⟨_,hOther.decoded⟩
      by_cases hPast : other.2 < seen.commit.2
      · have hActor := mmaAndScoreCommitSameThread hp hX hOtherIssue seen.score hSame.2.2
        have hSameLane : other.1 = source.1 := hActor.trans hLane.symm
        have hOrder : other.2 < source.2 := lt_of_le_of_ne
          (hLatest hOtherIssue hActor hPast) (fun hn => hEq (Prod.ext hSameLane hn))
        rcases overlappingMmaOutputPipeline hp hX hMma hCell hEq with h | h
        · exact .inr (.inl (.inl (.inr h)))
        · have hpast := po_of_not_access hSameLane hOrder (len_of_get hQk.decoded)
            (by rw [hQk.decoded]; rfl)
          exact (tcStep_acyclic hX hGuard other
            ((Relation.TransGen.single (.inl (.single (.inl hpast)))).trans h.tcBefore.tcStep)).elim
      · exact .inr (.inr (.inl (scoreLoadBeforeLaterWriter hp hX hJoint hLoad seen hMma
          (Nat.le_of_not_lt hPast))))
    · by_cases hBefore : other.2 < load.2
      · exact .inr (.inl (.inr (.inl (selectedQkAfterPriorProbabilityStore hp hX hJoint
          hLoad seen hQk hStage hCell hCta hAdjacent hStore hBefore))))
      · exact .inr (.inr (scoreLoadBeforeLaterProbabilityStore hp hX hLoad hStore
          (Nat.le_of_not_lt hBefore)))
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim
  · intro c r hr hCover release hRelease
    obtain ⟨hReleaseOwner,hDealloc⟩ := allocationReleaseInOwnerCta hX hr hRelease
    obtain ⟨_,_,_,hCellCta,_,_,_⟩ := hCover
    obtain ⟨_,hGeometry⟩ := hLoad.geometry hp hX
    have hOwner := congrArg Cell.cta hGeometry
    exact .inl (tensorOperationsCompletedBeforeRelease hp hX hCuQ
      (hOwner.symm.trans (hCellCta.trans hReleaseOwner.symm)) hDealloc)

/-- Actual stable score-load sources carry a completed result or a recorded store value. -/
theorem scoreLoadSourceValue (hCuQ : Epilogue.DrainCuQProtected p X)
    (hValues : ∀ i, CompletedValues l Assumptions.all X i) {load : EvId} {cell : Cell}
    {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage) :
    ∃ source value, ReadSource l X .ld source load cell ∧
      Wrote l Assumptions.all X source cell value := by
  obtain ⟨source,hSource⟩ := scoreLoadReadSource hp hX hCuQ hLoad
  rcases hSource.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
  · have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
    obtain ⟨seen⟩ := scoreLoadObservesScore hp hX hJoint hLoad
    rcases scoreLoadMmaOrder hp hX hJoint hLoad seen hMma with h | h
    · obtain ⟨v,hV⟩ := hValues source (h.done hX.tcCommit) cell hMma
      exact ⟨source,v,hSource,.inl hV⟩
    · have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
      exact (tcStep_acyclic hX hGuard source (hSource.2.2.1.tcStep.trans h.tcStep)).elim
  · obtain ⟨a,vs,shape,j,hStore,hJ,hCell⟩ := hStore
    exact ⟨source,vs[j],hSource,.inr (.inl
      ⟨a,vs,shape,j,hStore,List.getElem?_eq_some_iff.mpr ⟨hJ,rfl⟩,hCell⟩)⟩
  · exact (noTensorCopyOperandIssue hX hCopy).elim
  · exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Safety
