-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaLatestReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyToFinalRelease
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Kernels.TmlFa4Fwd.Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A fragment between a recurring key release's acquire and issue uses that
release's logical slot and generation. The notification may still be pending. -/
theorem recurringKeyUseOfReleaseMatch (stage : Fin 2) {g index d : Nat} {step : Fin 8}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {target : Loc} {release : Nat}
    {form : ReleaseForm}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    (matched : ReleaseMatch l X g release form target) (hForm : form = .loopKey)
    (hAfter : TraceBefore X (g,matched.wait) (g,index))
    (hBefore : TraceBefore X (g,index) (g,release)) :
    (atPrefix l X g index).kvAcquires 0 + (atPrefix l X g index).kvAcquires 1 +
      (atPrefix l X g index).kvAcquires 2 - 1 =
      3 * (atPrefix l X g matched.wait).kvAcquires matched.slot + matched.slot.val := by
  obtain ⟨wait,selected,parity,hObs,hPoll,_,hRank,hCount,hNoLater⟩ :=
    recurringKeyLatestReadyOccurrence hp hX stage hKey
  let mark := readyAtSite (releaseIndex .loopKey)
  have hMatched : ReleaseReadyObservation X g matched.wait .loopKey
      (Observation.readyObject l g matched.slot) matched.parity :=
    hForm ▸ matched.readyForm
  have hMatchRank : readyOccurrence X g matched.wait .loopKey =
      releaseOccurrence X g release .loopKey := hForm ▸ matched.ordinal
  have hLower : matched.wait ≤ wait := by
    by_contra! h
    exact hNoLater h hAfter.2.1 matched.ready
  have hBeforeElection : index ≤ release-1 := by
    have := hBefore.2.1
    omega
  have hElectionMono :=
    (List.take_sublist_take_left (l := X.tr g) hBeforeElection).countP_le
      (p := releaseAtSite (releaseIndex .loopKey))
  change releaseElections X g index .loopKey ≤ releaseOccurrence X g release .loopKey
    at hElectionMono
  have hSameWait : wait = matched.wait := by
    by_contra hNe
    have hLt : matched.wait + 1 ≤ wait := by omega
    have hMono := (List.take_sublist_take_left (l := X.tr g) hLt).countP_le (p := mark)
    change (X.tr g)[matched.wait]? = _ at hMatched
    rw [List.take_add_one,hMatched] at hMono
    rw [List.countP_append] at hMono
    change readyOccurrence X g matched.wait .loopKey + 1 ≤
      readyOccurrence X g wait .loopKey at hMono
    omega
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hKey.decoded⟩
  have hWarp := (mmaIssueElection hp hX hMma).1
  have hg : g < l.threads := PTX.Proof.event_thread_lt hX hKey.decoded
  let total := fun n => (atPrefix l X g n).kvAcquires 0 +
    (atPrefix l X g n).kvAcquires 1 + (atPrefix l X g n).kvAcquires 2
  have hProjection (n : Nat) : (((X.tr g).take n).filterMap readyEvent).length = total n :=
    readyUsesAtPrefix hp hX hg hWarp n
  rw [hSameWait,hProjection,hProjection] at hCount
  have hRelease := matched.ready.exactOccurrence hp hX hWarp
  change matched.slot.val = total matched.wait % 3 ∧
    (atPrefix l X g matched.wait).kvAcquires matched.slot = total matched.wait / 3 ∧ _
    at hRelease
  change total index-1 = _
  omega

/-- The key descriptor selects the physical slot of its actual release match. -/
theorem recurringKeyDescriptorOfReleaseMatch (stage : Fin 2) {g index d : Nat} {step : Fin 8}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {target : Loc} {release : Nat}
    {form : ReleaseForm}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    (matched : ReleaseMatch l X g release form target) (hForm : form = .loopKey)
    (hAfter : TraceBefore X (g,matched.wait) (g,index))
    (hBefore : TraceBefore X (g,index) (g,release)) :
    op.b = sharedDescriptor (kvStart l matched.slot.val + qkFragment step) 16 := by
  have hUse := recurringKeyUseOfReleaseMatch hp hX stage hKey matched hForm hAfter hBefore
  have hDescriptor := hKey.recurringKeyOperandOfReadyUse hp hX stage
  dsimp only at hDescriptor
  rw [hUse] at hDescriptor
  have hSlot (n : Nat) : (3 * n + matched.slot.val) % 3 = matched.slot.val % 3 := by omega
  simpa only [kvStart,kvSlot,hSlot] using hDescriptor

/-- A positive even ready use before the actual final output commit has the
matching recurring key release issue on the same lane. -/
theorem keyReadyMatchBeforeFinal {g wait final use : Nat} {output : TcCommit.Spec} {slot : Fin 3}
    {parity : Nat} (hFinal : SecondOutputCommit X (g,final) output)
    (hReady : ReadyPoll l X g wait slot parity true .cta) (hUse : readyCount X g wait = use)
    (hPositive : 0 < use) (hEven : use % 2 = 0) (hBefore : TraceBefore X (g,wait) (g,final)) :
    ∃ (index : Nat) (spec : TcCommit.Spec)
        (matched : ReleaseMatch l X g index .loopKey (Observation.emptyObject l g slot)),
      ReleaseIssue X g index .loopKey spec ∧ matched.wait = wait ∧ matched.slot = slot ∧
      TraceBefore X (g,index) (g,final) := by
  obtain ⟨index,form,spec,hRelease,hObs,hOrdinal,hAfter,hEarlier⟩ :=
    readyReleaseIssueBeforeFinal hp hX hFinal hReady hBefore
  obtain ⟨site,hGet,hGate⟩ := hReady.useSite hp hX (hFinal.issuerWarp hp hX)
  change ReadyUseSite (readyCount X g wait) site at hGate
  rw [hUse] at hGate
  have hSite : (slotWait (releaseIndex form)).pc = site :=
    congrArg Event.pc (Option.some.inj (hObs.symm.trans hGet))
  have hKey : site = readyHead 2 := by
    rcases hGate with ⟨_,hZero⟩ | ⟨hKey,_,_⟩ | ⟨_,hOdd⟩
    · omega
    · exact hKey
    · omega
  have hCheck (f : ReleaseForm) :
      (slotWait (releaseIndex f)).pc = readyHead 2 → f = .loopKey := by
    cases f <;> decide
  obtain rfl := hCheck form (hSite.trans hKey)
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX hGet
  have hResumes : Resumes kernel X (g,wait) (g,index) := by
    refine ⟨hAfter,?_⟩
    simp only [hGet,Option.map_some,Kind.resume]
    exact ⟨_,exit,_,parity,true,.cta,hGet,hSpin,hAfter⟩
  exact ⟨index,spec,⟨wait,slot,parity,hAfter.2.1,hReady,hObs,rfl,hOrdinal,hResumes⟩,
    hRelease,rfl,rfl,hEarlier⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
