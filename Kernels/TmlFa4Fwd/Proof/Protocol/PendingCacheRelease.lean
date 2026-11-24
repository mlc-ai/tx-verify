-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingEarlier
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheCopyOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open Thread.Loader (EmptyAcquire OrderedGuardedReuse recurringUseBefore recurringVectorEvent)
open Thread.Mma (EmptyReleaseAt)
open Thread.Mma.Observation (emptyObject)
open Loader (kvUseStage kvUseStage_val kvEmptyPhase)

private theorem seenReleasePoll {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {slot : Fin 3} {parity g k : Nat}
    (hWait : EmptyAcquire l X wait slot parity)
    (release : EmptyReleaseAt l X (emptyObject l wait.1 slot) g k)
    (hSeen : MbarObserved X release.record.id (.thread wait)) :
    ∃ (j : Nat) (r : Record Ref),
      (X.objects (emptyObject l wait.1 slot))[j]? = some r ∧ r.id = .thread wait ∧
      r.reply.waited = some true ∧
      observedAt (X.objects (emptyObject l wait.1 slot)) j = some release.ordinal := by
  obtain ⟨_,w,object,_,_,hw,⟨⟨_,_,he⟩,hUpdate⟩,_⟩ := hSeen
  have hWaitId : w = wait := Ref.thread.inj hw.symm
  subst w
  obtain ⟨ev,hGet,hKind⟩ := hWait
  rw [← Option.some.inj (he.symm.trans hGet)] at hKind
  obtain rfl : object = emptyObject l wait.1 slot := (Kind.wait.inj hKind).1
  obtain ⟨i,j,r,poll,phase,hi,hr,hClean,hj,hId,_,hOk,_,hPhase,hObserved,_⟩ := hUpdate
  have hIndex := ObjectInit.checked_record_index_eq
    (X.objects_checked hX (emptyObject l wait.1 slot)) hi release.atIndex hr
  subst i
  have hrEq := Option.some.inj (hi.symm.trans release.atIndex)
  have hOrdinal := (phaseAlignment hp hX (actualEmptyGuardLower hp hX wait.1 slot) phase).2
    k g release (hrEq ▸ hClean) hPhase
  exact ⟨j,poll,hj,hId,hOk,hOrdinal.symm ▸ hObserved⟩

private theorem laterGuardObserves {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {old wait : EvId} {slot : Fin 3} {position earlier : Nat} {r : Record Ref}
    (hBefore : Resumes kernel X old wait)
    (hOld : (X.objects (emptyObject l wait.1 slot))[position]? = some r)
    (hOldId : r.id = .thread old) (hOldSuccess : r.reply.waited = some true)
    (hEarlier : observedAt (X.objects (emptyObject l wait.1 slot)) position = some earlier)
    {q : Nat} (hWait : EmptyAcquire l X wait slot (if (q+2) % 2 = 0 then 1 else 0))
    (hp : Pre p l m) (hRank : earlier = q) :
    ∃ (j phase : Nat) (poll : Record Ref),
      (X.objects (emptyObject l wait.1 slot))[j]? = some poll ∧
      poll.id = .thread wait ∧ poll.reply.waited = some true ∧
      observedAt (X.objects (emptyObject l wait.1 slot)) j = some phase ∧ q+1 ≤ phase := by
  let loc := emptyObject l wait.1 slot
  let hChecked := X.objects_checked hX loc
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨j,poll,hRecord,hId,hAction,_,hSuccess⟩ := hWait.record hp hX
  have hOrder : position ≤ j := by
    by_contra! hReverse
    exact Round.Slot.not_before_of_reach hX
      (.single (DepStep.of_resumes l hBefore)) ⟨j,position,poll,r,hRecord,hId,hOld,hOldId,hReverse⟩
  obtain ⟨oldState,hOldState,hOldPhase⟩ :=
    hChecked.observed_phase hOld hOldSuccess hEarlier
  have hj : j ≤ (X.objects loc).length := (List.getElem?_eq_some_iff.mp hRecord).1.le
  obtain ⟨state,hState,hPhaseLower⟩ := hChecked.phase_mono hNoInval hOrder hj hOldState
  obtain ⟨next,phaseWord,hNext,hWord,hParity,hCompleted⟩ := hChecked.okPoll hRecord hSuccess
  have hStateEq := Option.some.inj (hNext.symm.trans hState)
  subst next
  obtain rfl := (Action.pollParity.inj (hWord.symm.trans hAction)).1
  have hPhase : q+2 ≤ state.phase := by
    have hLower : q+1 ≤ state.phase := by omega
    by_contra! hShort
    have hEq : state.phase = q+1 := by omega
    rw [hEq] at hParity
    split at hParity <;> omega
  have hObserved : observedAt (X.objects loc) j = some (state.phase-1) := by
    change ((X.objects loc)[j]?.bind (·.reply.completed)) = _
    change (X.objects loc)[j]? = some poll at hRecord
    rw [hRecord,Option.bind_some,hCompleted,ite_eq_left (show 0 < state.phase by omega)]
  exact ⟨j,state.phase-1,poll,hRecord,hId,hSuccess,hObserved,by omega⟩

/-- The successful guard of a later-generation recurring copy observes at least
its preceding empty phase, even before the copy's arrive-on is issued. -/
theorem pendingCacheGuardObservedLower {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hCopy : recurringVectorEvent e) (hPositive : 0 < recurringUseBefore X (g,index) / 3) :
    ∃ (wait : EvId) (j phase : Nat) (poll : Record Ref),
      let use := recurringUseBefore X (g,index)
      let slot := kvUseStage use
      let loc := emptyObject l wait.1 slot
      EmptyAcquire l X wait slot (if kvEmptyPhase use then 1 else 0) ∧
      Resumes kernel X wait (g,index) ∧
      (X.objects loc)[j]? = some poll ∧ poll.id = .thread wait ∧
      poll.reply.waited = some true ∧ observedAt (X.objects loc) j = some phase ∧
      use/3 - 1 ≤ phase := by
  obtain ⟨wait,hWait,hResume,hPrior⟩ :=
    Thread.Loader.earlierPublicationBeforePendingCopyGuard hp hX he hCopy
  let use := recurringUseBefore X (g,index)
  let slot := kvUseStage use
  let generation := use / 3
  change 0 < generation at hPositive
  change EmptyAcquire l X wait slot (if kvEmptyPhase use then 1 else 0) at hWait
  have hParity (n : Nat) (hn : generation = n) :
      (if kvEmptyPhase use then 1 else 0) = (if n % 2 = 0 then 1 else 0) := by
    unfold kvEmptyPhase Mma.kvParity
    change (if (generation % 2 == 0) = true then 1 else 0) = _
    simp only [hn,beq_iff_eq]
  by_cases hFirst : generation = 1
  · have hZero : EmptyAcquire l X wait slot 0 :=
      Eq.mp (congrArg (EmptyAcquire l X wait slot) (hParity 1 hFirst)) hWait
    obtain ⟨j,phase,poll,hRecord,hId,hSuccess,hObs⟩ :=
      observedPhaseOfZeroEmptyAcquire hp hX hZero
    exact ⟨wait,j,phase,poll,hWait,hResume,hRecord,hId,hSuccess,hObs,by omega⟩
  · let q := generation-2
    have hGen : generation = q+2 := by unfold q; omega
    have hBack : 2 ≤ use-3 ∧ use-3 < use := by dsimp [generation] at hGen; omega
    obtain ⟨index',hBefore,hPub,hRank⟩ := hPrior (use-3) hBack.1 hBack.2
    have hSlot : kvUseStage (use-3) = slot := Fin.ext (by
      change (use-3) % 3 = use % 3
      omega)
    rw [hSlot] at hPub hRank
    have hRank' : LoaderReady.generation l X (g,index') slot = q+1 := by
      unfold LoaderReady.generation
      rw [hRank]
      dsimp [q,generation]
      omega
    obtain ⟨guard,issuer,k,release,hOrdinal,hSeen⟩ :=
      actualReleaseForNextPublicationExact hp hX hPub hRank'
    obtain ⟨oldPosition,oldPoll,hOld,hOldId,hOldSuccess,hOldObs⟩ :=
      seenReleasePoll hp hX guard.empty release hSeen
    have hThread : guard.acquire.1 = wait.1 := guard.issuer.trans hBefore.1
    have hObject : emptyObject l guard.acquire.1 slot = emptyObject l wait.1 slot := by
      rw [hThread]
    rw [hOrdinal,hObject] at hOldObs
    rw [hObject] at hOld
    have hEarlier : Resumes kernel X guard.acquire wait :=
      guard.toGuardedReuse.resumesOfTraceBefore
        ⟨hThread,guard.before.trans hBefore.2.1,hBefore.2.2⟩
    obtain ⟨j,phase,poll,hRecord,hId,hSuccess,hObs,hBound⟩ :=
      laterGuardObserves hX hEarlier hOld hOldId hOldSuccess hOldObs
        (hParity (q+2) hGen ▸ hWait) hp rfl
    exact ⟨wait,j,phase,poll,hWait,hResume,hRecord,hId,hSuccess,hObs,by omega⟩

/-- A positive-generation recurring copy is guarded by a delivered release
of at least the preceding generation, including when its packet is open. -/
theorem pendingCacheGuardObservedRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hCopy : recurringVectorEvent e) (hPositive : 0 < recurringUseBefore X (g,index) / 3) :
    ∃ (wait : EvId) (issuer position : Nat),
      let use := recurringUseBefore X (g,index)
      let slot := kvUseStage use
      ∃ release : EmptyReleaseAt l X (emptyObject l wait.1 slot) issuer position,
        EmptyAcquire l X wait slot (if kvEmptyPhase use then 1 else 0) ∧
        Resumes kernel X wait (g,index) ∧ use/3 - 1 ≤ release.ordinal ∧
        MbarObserved X release.record.id (.thread wait) := by
  obtain ⟨wait,j,phase,poll,hWait,hResume,hRecord,hId,hSuccess,hObs,hLower⟩ :=
    pendingCacheGuardObservedLower hp hX he hCopy hPositive
  let slot := kvUseStage (recurringUseBefore X (g,index))
  let loc := emptyObject l wait.1 slot
  obtain ⟨k,r,hAt,hAction,hClean,hPhase⟩ :=
    Thread.Mma.emptyUnitThroughObservedPhase hp hX hRecord hSuccess hObs (Nat.le_refl _)
  obtain ⟨issuer,⟨release⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hAt hAction
  have hSame := Option.some.inj (hAt.symm.trans release.atIndex)
  have hOrdinal := (phaseAlignment hp hX (actualEmptyGuardLower hp hX wait.1 slot) phase).2
    k issuer release (hSame ▸ hClean) hPhase
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hSeen := hX.observed_of_phase hNoInval hAt hClean
    (by rw [hAction]; trivial) hRecord hSuccess hPhase hObs
  rw [hSame,hId] at hSeen
  exact ⟨wait,issuer,k,release,hWait,hResume,hOrdinal.symm ▸ hLower,hSeen⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
