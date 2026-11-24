-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasBoxes
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstCacheAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondQueryProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleLoaderRelease
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReady
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryFaults
import Kernels.TmlFa4Fwd.Proof.InputActualSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier Prologue Thread.Output

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem performedQueryNote (hX : Consistent l kernel Assumptions.all m X) {issue : EvId}
    {spec : TensorCopy.Spec} {stage plane : Fin 2} {cta : Nat}
    (hBox : Thread.Loader.QuerySubbox p l X issue stage plane spec) (hOwner : issue.1/l.block = cta)
    (hDone : (X.tensor issue).any (fun o => o.effects.notified) = true) :
    ∃ r ∈ X.objects (queryObject l cta stage), r.id = .async issue (.notify .load) ∧
      r.action = .completeTx 16384 := by
  let loc := queryObject l cta stage
  have hBytes := actualTensorInputTxBytes hp hX hBox.1
  obtain ⟨_,hEvent⟩ := hBox.1
  have hMbar : spec.mbar = loc := by simpa only [loc,hOwner] using hBox.2.1
  cases hObservation : X.tensor issue with
  | none => simp [hObservation] at hDone
  | some o =>
    have hNotified : o.effects.notified = true := by simpa [hObservation] using hDone
    have hAction : objectAction X X.async loc (.async issue (.notify .load)) =
        some (.completeTx 16384) := by
      simp [objectAction,hEvent,hObservation,hMbar,hNotified,hBytes,bind,Option.bind]
    obtain ⟨r,hr,hId⟩ := (hX.tma.2.2.1 loc).2.2 _ _ hAction
    have ha := ((hX.tma.2.2.1 loc).2.1 r hr).1
    rw [hId,hAction] at ha
    exact ⟨r,hr,hId,(Option.some.inj ha).symm⟩

private theorem queryReadyPhaseOfDelivered (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (stage : Fin 2) {credit : EvId}
    (hCredit : X.Arrive credit (queryObject l (g/l.block) stage) 32768 1 true .cta)
    (hBoxes : ∀ plane : Fin 2, ∃ issue spec,
      issue.1/l.block = g/l.block ∧ Thread.Loader.QuerySubbox p l X issue stage plane spec ∧
      (X.tensor issue).any (fun o => o.effects.notified) = true) :
    let log := X.objects (queryObject l (g/l.block) stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  obtain ⟨left,s,hLeft,hBoxL,hDoneL⟩ := hBoxes 0
  obtain ⟨right,t,hRight,hBoxR,hDoneR⟩ := hBoxes 1
  obtain ⟨r,hr,hId,ha⟩ := performedQueryNote hp hX hBoxL hLeft hDoneL
  obtain ⟨r',hr',hId',ha'⟩ := performedQueryNote hp hX hBoxR hRight hDoneR
  have hNe : r ≠ r' := by
    intro h
    have hSame := hId.symm.trans ((congrArg Record.id h).trans hId')
    have hi := (Ref.async.inj hSame).1
    subst right
    obtain ⟨_,he⟩ := hBoxL.1
    obtain ⟨_,hf⟩ := hBoxR.1
    have hEq := Kind.tensorIssue.inj
      (congrArg Event.kind (Option.some.inj (he.symm.trans hf)))
    have hl := hBoxL.2.2.1
    have hr := hBoxR.2.2.1
    rw [hEq.2] at hl
    have heq := congrArg Loc.addr (hl.symm.trans hr)
    change Mma.qStart l stage+16384*0 = Mma.qStart l stage+16384*1 at heq
    omega
  let loc := queryObject l (g/l.block) stage
  obtain ⟨_,he⟩ := hCredit
  have hAction : objectAction X X.async loc (.thread credit) = some (.arrive 1 32768) := by
    simp [objectAction,he,loc]
  obtain ⟨expected,hExpected,hIdExpected⟩ := (hX.tma.2.2.1 loc).2.2 _ _ hAction
  have hA := ((hX.tma.2.2.1 loc).2.1 expected hExpected).1
  rw [hIdExpected,hAction] at hA
  fin_cases stage
  · exact Protocol.Query.queryStageZeroPhaseOfCredits hp hX hExpected
      (Option.some.inj hA).symm hr hr' hNe ha ha'
  · exact Protocol.Query.queryStageOnePhaseOfCredits hp hX hExpected
      (Option.some.inj hA).symm hr hr' hNe ha ha'

/-- The selected request's first Q boxes establish phase one before the first MMA acquire. -/
theorem selectedQueryReadyPhaseOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hBefore : ¬ ∃ r ∈ X.objects (queryObject l (g/l.block) 0), r.reply.waited = some true) :
    let log := X.objects (queryObject l (g/l.block) 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  obtain ⟨⟨credit,hCredit⟩,hBoxes⟩ :=
    selectedQueryPacketDeliveredOfMaximal hp hMax hFrame hg hw hb hLo hHi hBefore
  apply queryReadyPhaseOfDelivered hp hMax.1 0 hCredit
  intro plane
  obtain ⟨issue,spec,hOwner,hBox,_,hDone⟩ := hBoxes plane
  exact ⟨issue,spec,hOwner,hBox,hDone⟩

/-- Before its first successful acquire, the second query still has its initial empty phase. -/
theorem openingSecondQueryEmptyPhase (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat}
    (hCta : cta < l.grid)
    (hBefore : ¬ ∃ r ∈ X.objects (queryObject l cta 1), r.reply.waited = some true) :
    let log := X.objects (Thread.Loader.secondQueryEmpty l cta)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 :=
  Protocol.Loader.releasePhaseZeroOfNoUpdates hp hMax hCta .secondQuery
    (fun _ hr hUpdate => hBefore (Loader.secondQueryReturnRequiresAcquisition hp hMax.1 hr hUpdate))

/-- The opening Q1 expectation and both delivered Q1 boxes establish the exact ready phase. -/
theorem openingSecondQueryReadyOfDelivered (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    {credit : EvId} (hCredit : Thread.Loader.StageOneExpectation l X (g / l.block) credit false)
    (hBoxes : ∀ plane : Fin 2, ∃ issue spec, issue.1 / l.block = g / l.block ∧
      Thread.Loader.QuerySubbox p l X issue 1 plane spec ∧
      (X.tensor issue).any (fun o => o.effects.notified) = true) :
    let log := X.objects (queryObject l (g / l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 :=
  queryReadyPhaseOfDelivered hp hX 1 ⟨_,hCredit⟩ hBoxes

/-- Once the selected loader has issued the first Bias packet, it delivers its opening Q1
expectation and both exact boxes before an unrecorded first MMA acquisition. -/
theorem openingSecondQueryReadyFromCursorOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hSh : 10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1 < shuffles)
    {ends : Nat → Option TState}
    (hStart : Loader.OpeningSecondQueryReached l X g shuffles votes ends)
    (hBefore : ¬ ∃ r ∈ X.objects (queryObject l (g / l.block) 1), r.reply.waited = some true) :
    let log := X.objects (queryObject l (g / l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  have hEmpty := openingSecondQueryEmptyPhase hp hMax (NamedBar.cta_lt hg) hBefore
  obtain ⟨hEntry,credit,hCredit⟩ :=
    Loader.openingSecondQueryExpectedOfMaximal hp hMax hg hStart hEmpty
  have hBoxes := Loader.selectedSecondQueryBoxesOfMaximal hp hMax
    (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hg hw hb hLo hHi hSh hEntry
  apply openingSecondQueryReadyOfDelivered hp hMax.1 hCredit
  intro plane
  obtain ⟨issue,spec,hOwner,hBox,_⟩ := hBoxes plane
  refine ⟨issue,spec,hOwner,hBox,?_⟩
  by_contra! hPending
  have hFalse : (X.tensor issue).any (fun o => o.effects.notified) = false := by
    cases h : (X.tensor issue).any (fun o => o.effects.notified) <;> simp_all
  exact hMax.not_grows (Protocol.LoaderReady.pendingTensorInput hp hMax.1 hFrame hBox.1 hFalse)
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg hw hb hLo hHi

/-- Every active request's loader issues its first Bias expectation and both halves before
reaching the second query cursor. -/
theorem selectedOpeningBiasPacketWithRankOfMaximal :
    ∃ votes ends, Loader.OpeningSecondQueryReached l X g
        (Loader.primingSearchShuffleCount batch+32) votes ends ∧
      (∃ issue, Thread.Loader.OpeningBiasExpectation l X issue (g/l.block)) ∧
      let coords := Epilogue.assignedCoordinates p batch (g/l.block)
      ∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
        X.TensorIssue issue p.biasMapAddress
          (biasInputSpec p (1152+64*half.val) (p.qOffset batch+256*coords.1) coords.2
            ⟨.shared,g/l.block,l.sharedBase+(166912+16384*half.val)⟩
            (Thread.Loader.biasReadyObject l (g/l.block) 0) false) := by
  obtain ⟨votes,ends,hQuery,_⟩ :=
    selectedQueryBoxesReachedWithRankOfMaximal hp hMax hFrame hg hw hb hLo hHi
  have hSh : 10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 <
      Loader.primingSearchShuffleCount batch+32 := by
    unfold Loader.primingSearchShuffleCount
    omega
  have writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc :=
    fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame
  have hBias := (Loader.selectedOpeningBiasEntryOfMaximal hp hMax writes
    hg hw hb hLo hHi hSh hQuery).1
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨hBiasBoxes,hExpected⟩ := Loader.openingBiasExpectedAtSiteOfMaximal hp hMax hg hBias
    (fun lane hl hBlocked => by
      have hSame := (Step.sameWarp_lane hBlock hg hl).1
      have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
      rw [hSame.1.2.2]
      exact Protocol.Bias.openingBiasEmptyPhase hp hMax hSame.1.2.1 hWarp hBlocked)
  obtain ⟨hNext,hBoxes⟩ :=
    Loader.openingBiasBoxesOfMaximal hp hMax writes hg hw hb hLo hHi hSh hBiasBoxes
  exact ⟨votes,ends,hNext,hExpected,hBoxes⟩

/-- Every active request's loader issues its first Bias expectation and both halves before
reaching the second query cursor. -/
theorem selectedOpeningBiasPacketOfMaximal :
    ∃ shuffles votes ends,
      10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 < shuffles ∧
      Loader.OpeningSecondQueryReached l X g shuffles votes ends ∧
      (∃ issue, X.Arrive issue
        (Thread.Loader.biasReadyObject l (g/l.block) 0) 32768 1 true .cta) ∧
      let coords := Epilogue.assignedCoordinates p batch (g/l.block)
      ∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
        X.TensorIssue issue p.biasMapAddress
          (biasInputSpec p (1152+64*half.val) (p.qOffset batch+256*coords.1) coords.2
            ⟨.shared,g/l.block,l.sharedBase+(166912+16384*half.val)⟩
            (Thread.Loader.biasReadyObject l (g/l.block) 0) false) := by
  obtain ⟨votes,ends,hNext,hExpect,hBoxes⟩ :=
    selectedOpeningBiasPacketWithRankOfMaximal hp hMax hFrame hg hw hb hLo hHi
  obtain ⟨issue,he⟩ := hExpect
  exact ⟨_,votes,ends,by unfold Loader.primingSearchShuffleCount; omega,hNext,
    ⟨issue,he.arrive⟩,hBoxes⟩

/-- Every active request's loader reaches the second query after issuing its initial
query and Bias packets. This also applies when other lanes already consumed those packets. -/
theorem selectedOpeningSecondQueryReachedOfMaximal :
    ∃ shuffles votes ends,
      10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 < shuffles ∧
      Loader.OpeningSecondQueryReached l X g shuffles votes ends := by
  obtain ⟨shuffles,votes,ends,hSh,hNext,_,_⟩ :=
    selectedOpeningBiasPacketOfMaximal hp hMax hFrame hg hw hb hLo hHi
  exact ⟨shuffles,votes,ends,hSh,hNext⟩

/-- The selected loader delivers the opening Q1 packet before an unrecorded Q1 acquire. -/
theorem selectedSecondQueryReadyPhaseOfMaximal
    (hBefore : ¬ ∃ r ∈ X.objects (queryObject l (g/l.block) 1), r.reply.waited = some true) :
    let log := X.objects (queryObject l (g/l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  obtain ⟨_,_,_,hSh,hStart⟩ :=
    selectedOpeningSecondQueryReachedOfMaximal hp hMax hFrame hg hw hb hLo hHi
  exact openingSecondQueryReadyFromCursorOfMaximal hp hMax hFrame
    hg hw hb hLo hHi hSh hStart hBefore

end PTX.Kernels.TmlFa4Fwd.Progress
