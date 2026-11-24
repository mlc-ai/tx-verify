-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseMatch
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.AsyncCopy PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd.Mma (fixedMmaCommitOffset mmaFixedCommitExactAddress)
open Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The issuer of a K/V release is an MMA lane. -/
theorem ReleaseIssue.issuerWarp {g index : Nat} {form : ReleaseForm} {spec : TcCommit.Spec}
    (he : ReleaseIssue X g index form spec) : Prologue.warpIndex l g = 12 := by
  have hRange : ∀ i : Fin 4, let site := (Mma.commitSite (Mma.releaseCommitSite i)).pc
      2145 ≤ site ∧ site < 2768 ∧ site ∉ registerHintSites := by decide
  let site := (Mma.commitSite (Mma.releaseCommitSite (releaseIndex form))).pc
  obtain ⟨hLo, hHi, hHint⟩ : 2145 ≤ site ∧ site < 2768 ∧ site ∉ registerHintSites :=
    hRange (releaseIndex form)
  have hBody : roleBodyPc (Prologue.warpIndex l g) site :=
    roleBodyPcOfEvent hp hX he (show 173 < site by omega) hHint
  rcases hBody with h | h
  · omega
  · split_ifs at h <;> omega

/-- Each CTA has one actual issuer of K/V release notifications. -/
theorem ReleaseIssue.sameIssuer {g h i j : Nat} {form form' : ReleaseForm}
    {spec spec' : TcCommit.Spec} (ha : ReleaseIssue X g i form spec)
    (hb : ReleaseIssue X h j form' spec') (hCta : g / l.block = h / l.block) : g = h := by
  have hWarp : SameWarp l g h :=
    ⟨⟨Step.CtaBar.thread_lt_of_get hX ha, Step.CtaBar.thread_lt_of_get hX hb, hCta⟩,
      (ha.issuerWarp hp hX).trans (hb.issuerWarp hp hX).symm⟩
  obtain ⟨_, _, lead, hElect, hLead⟩ := Mma.readyReleaseLeader hp hX (releaseIndex form) ha
  obtain ⟨_, _, lead', hElect', hLead'⟩ := Mma.readyReleaseLeader hp hX (releaseIndex form') hb
  exact sameWarp_eq_of_lane_eq hWarp (hLead.trans ((Mma.sameLeader hX hWarp hElect hElect').trans
    hLead'.symm))

/-- A pending or performed commit targeting a K/V-empty object is a release of that slot. -/
theorem releaseOfEmptyTarget {owner g index : Nat} {slot : Fin 3} {rank : Fin 16}
    {spec : TcCommit.Spec} (hi : X.Commit (g, index) spec)
    (hTarget : TcCommit.target spec rank = some (emptyObject l owner slot)) :
    ∃ form : ReleaseForm, ReleaseIssue X g index form spec := by
  obtain ⟨pc, he⟩ := hi
  have hLoc : emptyObject l owner slot =
      ⟨.shared, owner / l.block, l.sharedBase + 8 * slot.val + 56⟩ :=
    Loader.emptySlot_address l (owner / l.block) slot
  rcases inCommitSites hX he with hFixed | hRing
  · have hExact := mmaFixedCommitExactAddress hp hX he hFixed hTarget
    have hOffset := congrArg Loc.addr (hLoc.symm.trans hExact)
    simp only at hOffset
    have hSlot := slot.isLt
    have hFirst : pc = 2274 := by
      simp only [fixedCommits, List.mem_cons, List.not_mem_nil, or_false] at hFixed
      rcases hFixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [fixedMmaCommitOffset] at hOffset ⊢ <;> omega
    rw [hFirst] at he
    exact ⟨.firstKey, he⟩
  · simp only [ringCommits, List.mem_cons, List.not_mem_nil, or_false] at hRing
    rcases hRing with rfl | rfl | rfl
    · exact ⟨.loopValue, he⟩
    · exact ⟨.loopKey, he⟩
    · exact ⟨.tailValue, he⟩

/-- An actual notification on a KV-empty object came from a release of that K/V buffer. -/
theorem releaseOfEmptyNotification {owner g index : Nat} {slot : Fin 3} {rank : Fin 16}
    {r : Record Ref} (hRecord : r ∈ X.objects (emptyObject l owner slot))
    (hId : r.id = .async (g, index) (.tcNotify rank)) :
    ∃ (form : ReleaseForm) (spec : TcCommit.Spec), ReleaseIssue X g index form spec ∧
      TcCommit.target spec rank = some (emptyObject l owner slot) := by
  cases record_source hX.tma.2.2.1 hRecord with
  | @commit issue pc spec otherRank hActual he hTarget _ =>
    obtain ⟨rfl, hRank⟩ := Ref.async.inj (hActual.symm.trans hId)
    have hr : otherRank = rank := Part.tcNotify.inj hRank
    subst otherRank
    obtain ⟨form, hIssue⟩ := releaseOfEmptyTarget hp hX ⟨_, he⟩ hTarget
    exact ⟨form, spec, hIssue, hTarget⟩
  | _ => grind

/-- Every counter update of a KV-empty object is one arrival unit from a release. -/
theorem emptyUpdateArrival {owner : Nat} {slot : Fin 3} {r : Record Ref}
    (hRecord : r ∈ X.objects (emptyObject l owner slot)) (hUpdate : CounterUpdate r.action) :
    ∃ (g index : Nat) (rank : Fin 16), r.id = .async (g, index) (.tcNotify rank) ∧
      r.action = .arrive 1 0 := by
  let loc := emptyObject l owner slot
  have hLoc : loc = ⟨.shared, owner / l.block, l.sharedBase + 8 * slot.val + 56⟩ :=
    Loader.emptySlot_address l (owner / l.block) slot
  have offsetEq {off own : Nat}
      (h : loc = ⟨.shared, own, l.sharedBase + off⟩) : 8 * slot.val + 56 = off := by
    have hAddr := congrArg Loc.addr (hLoc.symm.trans h)
    simp only at hAddr
    omega
  have hRange := slot.isLt
  cases record_source hX.tma.2.2.1 hRecord with
  | init _ _ h | inval _ _ h | wait _ _ h =>
    rw [h] at hUpdate
    exact hUpdate.elim
  | arrive _ he _ =>
    obtain ⟨off, hOff, hAt⟩ := actualArriveOffsetIn hp hX he
    have hEq := offsetEq hAt
    simp only [ordinaryArriveOffsets, List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega
  | increment _ he _ =>
    exact (Loader.noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hTarget _ =>
    obtain ⟨site, rfl⟩ := Loader.actualInputIssuePc hX he
    obtain ⟨off, hOff, hAt⟩ := Loader.loaderTensorAddress hp hX site he
    have hEq := offsetEq (hTarget.symm.trans hAt)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega
  | arriveOn _ he hTarget _ _ =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := Loader.actualAsyncArrival hX he
    have hSite : ∀ j : Fin 6, Loader.copyCommitPc j + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] :=
      by decide
    obtain ⟨off, hOff, hAt⟩ := Loader.loaderAsyncAddress hp hX he (hSite site)
    have hEq := offsetEq (hTarget.symm.trans hAt)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    omega
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit hId _ _ hAction => exact ⟨_, _, _, hId, hAction⟩
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- Every counter update of a KV-empty object comes from a K/V release notification. -/
theorem emptyUpdateSource {owner : Nat} {slot : Fin 3} {r : Record Ref}
    (hRecord : r ∈ X.objects (emptyObject l owner slot)) (hUpdate : CounterUpdate r.action) :
    ∃ (g index : Nat) (rank : Fin 16), r.id = .async (g, index) (.tcNotify rank) := by
  obtain ⟨g, index, rank, hId, _⟩ := emptyUpdateArrival hp hX hRecord hUpdate
  exact ⟨g, index, rank, hId⟩

/-- Each phase completed before a record holds one unit release on the empty slot. -/
theorem emptyUnitOfPriorPhase {owner j phase : Nat} {slot : Fin 3} {event : Record Ref}
    {state : State} (hAt : (X.objects (emptyObject l owner slot))[j]? = some event)
    (hState : stateBefore (X.objects (emptyObject l owner slot)) j = some state)
    (hBefore : phase < state.phase) :
    ∃ (k : Nat) (r : Record Ref), (X.objects (emptyObject l owner slot))[k]? = some r ∧
      r.action = .arrive 1 0 ∧ r.fault = none ∧
      phaseAt (X.objects (emptyObject l owner slot)) k = some phase := by
  classical
  let loc := emptyObject l owner slot
  have hInit : PairTmaRing.InitFirst X loc 1 := by
    have hCount : ∀ s : Fin 3, (Prologue.initSite (Loader.emptySlot s)).count = 1 := by decide
    rw [← hCount slot]
    exact (activeObjectHistory hp hX (Loader.emptySlot slot) (List.mem_of_getElem? hAt)).1
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have update {r : Record Ref} (hMem : r ∈ X.objects loc) (h : CounterUpdate r.action) :=
    emptyUpdateArrival hp hX hMem h
  have hNoIncrement : incrementsBefore (X.objects loc) (X.objects loc).length = 0 :=
    incrementsBefore_length_of _ fun r hMem hAction => by
      obtain ⟨_, _, _, _, hArrival⟩ := update hMem (by rw [hAction]; trivial)
      rw [hAction] at hArrival
      cases hArrival
  have hChecked := X.objects_checked hX loc
  have hUnits := hChecked.card_unit_arrivals_phase hNoInval (n := 1) (q := phase)
    (fun _ r count tx hRecord _ hAction => by
      obtain ⟨_, _, _, _, hUnit⟩ := update (List.mem_of_getElem? hRecord)
        (by rw [hAction]; trivial)
      rw [hAction] at hUnit
      exact (Action.arrive.inj hUnit).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNoInval h) hNoIncrement
    (List.getElem?_eq_some_iff.mp hAt).1.le hState hBefore
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < _ from hUnits.symm ▸ Nat.zero_lt_one)
  obtain ⟨_, r, tx, hRecord, hAction, hClean, hAt⟩ := Finset.mem_filter.mp hk
  obtain ⟨_, _, _, _, hUnit⟩ := update (List.mem_of_getElem? hRecord)
    (by rw [hAction]; trivial)
  exact ⟨k, r, hRecord, hUnit, hClean, hAt⟩

/-- Every phase through a completed empty observation holds its one unit release record. -/
theorem emptyUnitThroughObservedPhase {owner j phase observed : Nat} {slot : Fin 3}
    {poll : Record Ref} (hPoll : (X.objects (emptyObject l owner slot))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (emptyObject l owner slot)) j = some observed)
    (hThrough : phase ≤ observed) :
    ∃ (k : Nat) (r : Record Ref), (X.objects (emptyObject l owner slot))[k]? = some r ∧
      r.action = .arrive 1 0 ∧ r.fault = none ∧
      phaseAt (X.objects (emptyObject l owner slot)) k = some phase := by
  obtain ⟨st, hState, hPhase⟩ := (X.objects_checked hX (emptyObject l owner slot)).observed_phase
    hPoll hSuccess hObserved
  exact emptyUnitOfPriorPhase hp hX hPoll hState (by omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
