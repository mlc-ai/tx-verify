-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadRendezvous
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasWriteReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasExpectationFaults
import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasReadReuse
import Kernels.TmlFa4Fwd.Proof.Thread.WaitMode
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.CtaMemoryOrder
import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.MbarRingRound
import Lemmas.Protocol.StagingHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier PTX.Proof Thread Thread.Scores Thread.Loader
open Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The ready observation of a Bias read is an actual acquire preceding the read in
the same lane, at a phase no smaller than its stage rendezvous cursor. -/
theorem biasReadReadyObservation (stage : Fin 2) {read : EvId} {repeated : Bool} {v : Fin 16}
    {a : Acc} {bytes : List (Option Byte)} (hRead : BiasVectorRead X read repeated v a bytes)
    (hWarp : warpIndex l read.1 < 8) (hStage : warpIndex l read.1/4 = stage.val) :
    let log := X.objects (biasReadyObject l (read.1/l.block) stage)
    ∃ (wait index phase : Nat) (r : Record Ref),
      log[index]? = some r ∧ r.id = .thread (read.1,wait) ∧
      r.reply.waited = some true ∧ observedAt log index = some phase ∧
      observedBarrierOrdinal X read (11+stage.val) ≤ phase ∧
      TraceBefore X (read.1,wait) read := by
  obtain ⟨g,j⟩ := read
  let loc := biasReadyObject l (g/l.block) stage
  let n := observedBarrierOrdinal X (g,j) (11+stage.val)
  have hPrefix : n < okPolls loc ((X.tr g).take j) := biasReadReadyBudget hp hX stage hRead
    hWarp hStage
  have hExtent : n < okPolls loc (X.tr g) :=
    hPrefix.trans_le (List.take_sublist _ _).countP_le
  let wait := MbarRing.Poll.nth X loc g n
  have hWait : wait < j := MbarRing.Poll.nth_lt hPrefix
  have hClean : ∀ r ∈ X.objects loc, (∃ q ok, r.action = .pollParity q ok) → r.fault = none :=
    fun _ hR hq => actualInitOrPollClean hp hX hR (.inr hq)
  obtain ⟨index,r,_,hGet,hId,_,hSuccess,_,hOrdinal⟩ :=
    MbarRing.Poll.record hX hClean hExtent
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hAlt := Thread.Softmax.biasReadySelectedAlternates hp hX stage hWarp rfl hStage hClean
  have hSelected := objectThreadSelected_iff.mpr ⟨_,hId⟩
  have hChecked := X.objects_checked hX loc
  obtain ⟨st,hSt,hLower,_⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g)
      (by decide) hAlt hGet hSelected hSuccess
  rw [hOrdinal] at hLower
  have hPos : 0 < st.phase := by omega
  obtain ⟨u,q,hu,_,_,hCompleted⟩ := hChecked.okPoll hGet hSuccess
  rw [hSt] at hu
  obtain rfl := Option.some.inj hu
  have hPhase : observedAt (X.objects loc) index = some (st.phase-1) := by
    change ((X.objects loc)[index]?).bind (·.reply.completed) = _
    rw [hGet,Option.bind_some,hCompleted,ite_eq_left hPos]
  exact ⟨wait,index,st.phase-1,r,hGet,hId,hSuccess,hPhase,by omega,
    rfl,hWait,len_of_get hRead⟩

omit hp hX in
private theorem biasReleaseObservation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {rel wait : EvId} {loc : Loc}
    {tx count : Nat} (hRelease : X.Arrive rel loc tx count true .cta)
    (hObs : MbarObserved X (.thread rel) (.thread wait)) :
    WaitObserves X (.thread rel) wait loc true .cta := by
  obtain ⟨_,_,observed,acq,scope,hId,hWait,_⟩ := hObs
  obtain rfl := Ref.thread.inj hId
  obtain ⟨_,_,hEvent⟩ := hWait.1
  have hMode := Thread.actualPollAcquires hX hEvent
  have hScope := actualPollScope hX hEvent
  subst acq scope
  obtain ⟨_,_,rec,_,_,hr,hRecId,_,_⟩ := hWait.2
  have hAction := ((hX.tma.2.2.1 observed).2.1 rec (List.mem_of_getElem? hr)).1
  obtain ⟨_,hArrive⟩ := hRelease
  rw [hRecId] at hAction
  have hEq : loc = observed := by
    by_contra hNe
    simp [objectAction,hArrive,hNe] at hAction
  subst observed
  exact hWait

private theorem earlierExpectationGuard (stage : Fin 2) {cta n : Nat} {expect : EvId}
    (hExpect : X.Arrive expect (biasReadyObject l cta stage) 32768 1 true .cta)
    (hBefore : n+1 ≤ biasArrivalOrdinal X (biasReadyObject l cta stage) expect) :
    ∃ earlier release guard, earlier ≤ expect.2 ∧
      X.Arrive release (biasEmptyObject l cta stage) 0 1 true .cta ∧
      biasArrivalOrdinal X (biasEmptyObject l cta stage) release = n ∧
      MbarObserved X (.thread release) (.thread (expect.1,guard)) ∧
      Resumes kernel X (expect.1,guard) (expect.1,earlier) := by
  obtain ⟨loader,atExpect⟩ := expect
  let loc := biasReadyObject l cta stage
  let past := (X.tr loader).take (atExpect+1)
  obtain ⟨_,he⟩ := hExpect
  have hSize : n+1+1 ≤ past.countP (arrivesOn loc) := by
    change (X.tr loader)[atExpect]? = _ at he
    dsimp only [past]
    rw [List.take_add_one,he,Option.toList_some,List.countP_append]
    have hh := Nat.add_le_add_right hBefore 1
    simpa [arrivesOn,sourceArrive,biasArrivalOrdinal,Flow.arrivals,loc] using hh
  obtain ⟨k,e,hGet,hMark,hCount⟩ := MbarRing.Slot.exists_nth_countP (arrivesOn loc) hSize
  have hLen := (List.getElem?_eq_some_iff.mp hGet).1
  change k < past.length at hLen
  simp only [past,List.length_take] at hLen
  have hLe : k ≤ atExpect := by omega
  have hEv : X.get (loader,k) = some e := by
    rw [List.getElem?_take_of_lt (show k < atExpect+1 by omega)] at hGet
    exact hGet
  rw [List.take_take, Nat.min_eq_left (show k ≤ atExpect+1 by omega)] at hCount
  obtain ⟨_,kind⟩ := e
  obtain ⟨tx,units,rel,scope,hKind⟩ := arrivesOn_form hMark
  change kind = _ at hKind
  subst kind
  have hArrive : X.Arrive (loader,k) loc tx units rel scope := ⟨_,hEv⟩
  obtain ⟨rfl,rfl,rfl,rfl⟩ := biasOrdinaryCredit hp hX stage hArrive
  have hAct : objectAction X X.async loc (.thread (loader,k)) = some (.arrive 1 32768) := by
    simp [objectAction,hEv]
  obtain ⟨r,hr,hId⟩ := (hX.tma.2.2.1 loc).2.2 _ _ hAct
  have hAction := ((hX.tma.2.2.1 loc).2.1 r hr).1
  rw [hId,hAct] at hAction
  have hShape := (Option.some.inj hAction).symm
  obtain ⟨index,hRecord⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨st,_,hPhase,_,hGuard⟩ :=
    biasExpectationStateWithGuard hp hX stage hRecord hId hArrive hShape
  change biasArrivalOrdinal X loc (loader,k) = n+1 at hCount
  rw [hCount] at hPhase
  obtain ⟨release,guard,hRet,hOrdinal,hObserve,hResume⟩ := hGuard (by omega)
  exact ⟨k,release,guard,hLe,hRet,by omega,hObserve,hResume⟩

/-- Every older Bias write is observed upstream of the current read. Its next
generation's expectation carries that observation to the reader's own acquire. -/
theorem earlierBiasWriteBeforeRead (stage half : Fin 2) {tensor wait read : EvId}
    {spec : TensorCopy.Spec} (hIssue : BiasSubbox p l X tensor stage half spec)
    (hCta : tensor.1/l.block = wait.1/l.block) {index phase : Nat} {record : Record Ref}
    (hRecord : (X.objects (biasReadyObject l (wait.1/l.block) stage))[index]? = some record)
    (hId : record.id = .thread wait) (hOk : record.reply.waited = some true)
    (hObserved : observedAt (X.objects (biasReadyObject l (wait.1/l.block) stage)) index =
      some phase) (hOlder : biasTensorOrdinal l X stage half tensor < phase)
    (hLater : TraceBefore X wait read) {x y byte : Nat} {loc : Loc}
    (hCover : AsyncCovers X tensor (.write (.load x y byte)) loc) :
    modelCausality l X loc (.async tensor (.write (.load x y byte))) (.thread read) := by
  let cta := wait.1/l.block
  let n := biasTensorOrdinal l X stage half tensor
  obtain ⟨expect,hExpect,hExpectObs,hExpectOrd⟩ :=
    biasObservedExpectation hp hX stage hRecord hOk hObserved
  rw [hId] at hExpectObs
  have hLe : n+1 ≤
      biasArrivalOrdinal X (biasReadyObject l cta stage) expect :=
    hOlder.trans_le hExpectOrd
  obtain ⟨earlier,release,guard,hBefore,hRelease,hReleaseOrd,hReleaseObs,hResumes⟩ :=
    earlierExpectationGuard hp hX stage hExpect hLe
  obtain ⟨ready,k,previous,hPrevious,hPrevId,hPrevOk,hPrevObserved,hResumeReady⟩ :=
    biasReturnObservedReadyExact hp hX stage hRelease
  rw [hReleaseOrd] at hPrevObserved
  obtain ⟨actual,older,hOwner,hOlderIssue,hOrdinal,hSeen⟩ :=
    biasReadyObservedHalfOwner hp hX stage half hPrevious hPrevOk hPrevObserved
  have hEq := biasTensorOrdinalInjective hp hX hOlderIssue hIssue
    (hOwner.trans hCta.symm) hOrdinal
  subst actual
  rw [hPrevId] at hSeen
  have hObserve := biasTensorObservedAtCTA hX hSeen
  have hReleaseSeen := biasReleaseObservation hX hRelease hReleaseObs
  have hExpectSeen := biasReleaseObservation hX hExpect hExpectObs
  obtain ⟨_,hIssueEvent⟩ := hIssue.1
  have ⟨_,hReturnEvent⟩ := hRelease
  have ⟨_,hExpectEvent⟩ := hExpect
  have hIssueThread := event_thread_lt hX hIssueEvent
  have hReturnThread := event_thread_lt hX hReturnEvent
  have hExpectThread := event_thread_lt hX hExpectEvent
  have hWaitThread : wait.1 < l.threads := by
    obtain ⟨_,_,he⟩ := hExpectSeen.1
    exact event_thread_lt hX he
  have hReleaseAddr : release.1/l.block = cta := by
    obtain ⟨_,_,rec,_,_,hr,hRecId,_,_⟩ := hReleaseSeen.2
    have hOwner := mbarRecordOwner hp hX (List.mem_of_getElem? hr)
    rw [hRecId] at hOwner
    exact hOwner.symm
  have hExpectOwner : expect.1/l.block = cta := by
    rcases expect with ⟨g,j⟩
    exact (Thread.Loader.biasExpectationOwner hp hX stage hExpect).symm
  have hDone : AsyncFinished l X tensor (.write (.load x y byte)) (release.1,ready) :=
    .inr ⟨.cta,hObserve,MbarRing.Unit.Gate.scopesMeet
      ⟨hIssueThread,hReturnThread,hCta.trans hReleaseAddr.symm⟩ .cluster .cta⟩
  have hReadyReturn : baseCausality l X (release.1,ready) release := .single (.inl
    (po_of_not_access hResumeReady.1.1 hResumeReady.1.2.1 hResumeReady.1.2.2
      (by rw [hReturnEvent]; rfl)))
  have hReturnEarlier : baseCausality l X release (expect.1,earlier) :=
    Staging.baseCausality_of_handoff ⟨0,1,hRelease⟩ hReleaseSeen
      (ScopesMeet.of_sameCta ⟨hReturnThread,hExpectThread,
        hReleaseAddr.trans hExpectOwner.symm⟩) ⟨rfl,le_rfl⟩ hResumes.1
  have hEarlierRead : baseCausality l X (expect.1,earlier) read :=
    Staging.baseCausality_of_handoff ⟨32768,1,hExpect⟩ hExpectSeen
      (ScopesMeet.of_sameCta ⟨hExpectThread,hWaitThread,hExpectOwner⟩)
      ⟨rfl,hBefore⟩ hLater
  exact ⟨hCover,_,hDone,.inl (hReadyReturn.trans (hReturnEarlier.trans hEarlierRead))⟩

/-- A later generation's real Bias-empty acquire protects the generic read from a
later tensor write to that lane's stage. -/
theorem biasReadBeforeLaterWrite (stage half : Fin 2) {read tensor : EvId} {repeated : Bool}
    {v : Fin 16} {a : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X read repeated v a bytes) (hWarp : warpIndex l read.1 < 8)
    (hStage : warpIndex l read.1/4 = stage.val) {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X tensor stage half spec) (hSame : tensor.1/l.block = read.1/l.block)
    (hLater : observedBarrierOrdinal X read (11+stage.val) <
      biasTensorOrdinal l X stage half tensor) {part : Part} {loc : Loc}
    (hShared : loc.space = .shared) (hLocal : loc.cta = read.1/l.block)
    (hCover : AsyncCovers X tensor part loc) :
    modelCausality l X loc (.thread read) (.async tensor part) := by
  obtain ⟨loader,index⟩ := tensor
  obtain ⟨empty,k,hEmpty,hOwner,_,hGeneration,hObserve,hResume⟩ :=
    biasTensorReuseOfConsumerWarp hp hX (0 : Fin 4) hIssue (by omega)
  rw [hSame] at hGeneration
  have hCount : observedBarrierOrdinal X read (11+stage.val) ≤
      arrivals (biasEmptyObject l (read.1/l.block) stage) ((X.tr empty.1).take empty.2) := by
    change arrivals (biasEmptyObject l (read.1/l.block) stage) ((X.tr empty.1).take empty.2)
      + 1 = _ at hGeneration
    omega
  obtain ⟨fence,hFence,hReader,hBefore,hAfter⟩ :=
    biasReadFenceBeforeReturn hp hX stage hRead hWarp hStage (hSame ▸ hEmpty)
      (hSame.symm.trans hOwner.symm) hCount
  have hWaited := reuseWaitObservesAtCTA hp hX hIssue hEmpty hObserve
  obtain ⟨_,hT⟩ := hIssue.1
  have ⟨_,hE⟩ := hEmpty
  have hLoader := event_thread_lt hX hT
  have hEmptyThread := event_thread_lt hX hE
  have hScope : ScopesMeet l .cta empty.1 .cta loader :=
    ScopesMeet.of_sameCta ⟨hEmptyThread,hLoader,hOwner⟩
  have hReuse := Staging.baseCausality_of_handoff (e := empty) (f := (loader,index))
    ⟨0,1,hEmpty⟩ hWaited hScope ⟨rfl,le_rfl⟩ hResume.1
  have hCluster : SameCluster l read.1 loader :=
    ⟨hReader,hLoader,congrArg l.clusterOfCta hSame.symm⟩
  exact ⟨hCover,.inl ⟨(read.1,fence),_,_,hFence,hReader,⟨hShared,hLocal⟩,hCluster,
    hBefore,hAfter.trans hReuse⟩⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
