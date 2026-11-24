-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketFacts
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyCoverage
public import Kernels.TmlFa4Fwd.Proof.InputActualSources
public import Kernels.TmlFa4Fwd.Proof.LoaderCopySize
public import Kernels.TmlFa4Fwd.Proof.LoaderProgress
public import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader (readySlot)

noncomputable section
open Classical

/-- The physical thread representing a logical producer lane. -/
abbrev producer (l : Launch) (cta : Nat) (lane : Fin 64) : Nat :=
  PTX.Kernels.TmlFa4Fwd.Loader.readyProducer l cta lane

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An actual ready publication identifies one logical loader lane of that CTA. -/
theorem publicationProducer {owner : Nat} {slot : Fin 3} {i : EvId}
    (hIssue : X.AsyncArrive i (readyObject l owner slot) true) :
    ∃ lane : Fin 64, i.1 = producer l (owner / l.block) lane := by
  obtain ⟨_, he⟩ := hIssue
  exact Loader.readyArrivalProducer hp hX slot he

omit hp hX in
/-- A successful CTA acquire of a ready object in the consumer's CTA. -/
def ReadyAcquire (l : Launch) (X : Execution) (wait : EvId) (slot : Fin 3) : Prop :=
  ∃ e parity, X.get wait = some e ∧ e.kind = .wait (readyObject l wait.1 slot) parity true true .cta

/-- Any actual record identifies the initialized ready history of its physical slot. -/
theorem readyHistory {g : Nat} {slot : Fin 3} {k : Nat} {r : Record Ref}
    (hr : (X.objects (readyObject l g slot))[k]? = some r) :
    NoIncObject X (readyObject l g slot) 64 :=
  PTX.Kernels.TmlFa4Fwd.Loader.actualReadyHistoryObject hp hX slot
    (List.mem_iff_getElem?.mpr ⟨k, hr⟩)

/-- The role observation supplies initialization and a checked successful poll record. -/
theorem ReadyAcquire.record {wait : EvId} {slot : Fin 3} (h : ReadyAcquire l X wait slot) :
    let loc := readyObject l wait.1 slot
    NoIncObject X loc 64 ∧ ∃ (j : Nat) (poll : Record Ref), (X.objects loc)[j]? = some poll ∧
      poll.id = .thread wait ∧ poll.reply.waited = some true := by
  obtain ⟨⟨pc, kind⟩, parity, he, hk⟩ := h
  cases hk
  exact PTX.Kernels.TmlFa4Fwd.Loader.actualReadyAcquireRecord hp hX slot he

/-- The observed phase contains 64 arrivals, each publishing a packet whose tracked writes
are visible to the successful CTA acquire. -/
theorem ReadyAcquire.packets {wait : EvId} {slot : Fin 3} (h : ReadyAcquire l X wait slot)
    {j phase : Nat} {poll : Record Ref} (hObj : NoIncObject X (readyObject l wait.1 slot) 64)
    (hRecord : (X.objects (readyObject l wait.1 slot))[j]? = some poll)
    (hPoll : poll.id = .thread wait) (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (readyObject l wait.1 slot)) j = some phase) :
    let loc := readyObject l wait.1 slot
    let positions := (Finset.range (X.objects loc).length).filter
      (UnitArrivalIn (X.objects loc) phase)
    positions.card = 64 ∧ ∀ k ∈ positions, k < j ∧
      ∃ (issue : EvId) (pub : Publication), loc = readyObject l issue.1 pub.slot ∧
        (atPrefix l X issue.1 (issue.2 + 1)).published =
          pub :: (atPrefix l X issue.1 issue.2).published ∧
        ∀ copy, TracksCpAsync X copy issue → AsyncFinished l X copy (.write .copy) wait := by
  obtain ⟨⟨pc, kind⟩, parity, he, hk⟩ := h
  cases hk
  obtain ⟨hCount, hPackets⟩ :=
    PTX.Kernels.TmlFa4Fwd.Loader.readyPhaseObserved hX slot rfl he hObj hRecord hPoll hSuccess
      hObserved
  refine ⟨hCount, fun k hm => ?_⟩
  obtain ⟨hk, issue, _, hi, _, hVisible⟩ := hPackets k hm
  obtain ⟨pub, _, hLoc, hStep⟩ := readyStep hp hX hi rfl
  exact ⟨hk, issue, pub, hLoc, hStep, hVisible⟩

section
variable {wait : EvId} {slot : Fin 3} {j phase : Nat} {poll : Record Ref}
    (hObj : NoIncObject X (readyObject l wait.1 slot) 64)
    (hRecord : (X.objects (readyObject l wait.1 slot))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (readyObject l wait.1 slot)) j = some phase)
    (hCap : let loc := readyObject l wait.1 slot
      ∀ q ≤ phase, ∀ k r issue, (X.objects loc)[k]? = some r → r.fault = none →
        r.action = .arrive 1 0 → phaseAt (X.objects loc) k = some q →
        r.id = .async issue .arriveOn →
        (atPrefix l X issue.1 issue.2).published.countP (fun pub => pub.slot == slot) ≤ q)
include hObj hRecord hSuccess hObserved hCap

/-- Ready phases have one publication per producer and generation when no lane is ahead of
the phase to which its unit record was added. The cap is expressed in the role state. -/
theorem readyCoverageByOrdinal :
    let loc := readyObject l wait.1 slot
    ∀ q ≤ phase, ∀ lane : Fin 64, ∃ (k : Nat) (r : Record Ref) (issue : EvId), k < j ∧
      (X.objects loc)[k]? = some r ∧ r.fault = none ∧ r.action = .arrive 1 0 ∧
      phaseAt (X.objects loc) k = some q ∧ r.id = .async issue .arriveOn ∧
      issue.1 = producer l (wait.1 / l.block) lane ∧ X.AsyncArrive issue loc true ∧
      (atPrefix l X issue.1 issue.2).published.countP (fun pub => pub.slot == slot) = q := by
  have hOrd (q : Nat) (hq : q ≤ phase) (k : Nat) (r : Record Ref) (issue : EvId)
      (hr : (X.objects (readyObject l wait.1 slot))[k]? = some r) (hClean : r.fault = none)
      (hAct : r.action = .arrive 1 0) (hPhase : phaseAt (X.objects (readyObject l wait.1 slot)) k =
        some q) (hId : r.id = .async issue .arriveOn) :
      PTX.Kernels.TmlFa4Fwd.Loader.readyOrdinal X (readyObject l wait.1 slot) issue ≤ q := by
    obtain ⟨_, _, actual, hActual, ⟨pc, he⟩, _⟩ := hObj.arrive_source hr hAct
    have heq := congrArg Loc.cta (readyObservation hp hX he rfl).choose_spec.2.1
    change wait.1 / l.block = actual.1 / l.block at heq
    have hEq : actual = issue := by
      rw [hId] at hActual
      exact (Ref.async.inj hActual).1.symm
    subst actual
    have h := publicationOrdinal hp hX issue.1 issue.2 slot
    rw [show readyObject l issue.1 slot = readyObject l wait.1 slot from
      congrArg (fun cta => Prologue.initObject l cta (readySlot slot)) heq.symm] at h
    exact h ▸ hCap q hq k r issue hr hClean hAct hPhase hId
  dsimp only
  intro q hq lane
  obtain ⟨k, r, pc, hk, hr, hClean, hAct, hPhase, hId, he⟩ :=
    PTX.Kernels.TmlFa4Fwd.Loader.readyPhaseCoverage hp hX slot hObj hRecord hSuccess hObserved
      hOrd q hq lane
  let loc := readyObject l wait.1 slot
  let issue := PTX.Kernels.TmlFa4Fwd.Loader.readyIssue X loc (producer l (wait.1 / l.block) lane) q
  change X.get issue = some _ at he
  have hCTA := congrArg Loc.cta (readyObservation hp hX he rfl).choose_spec.2.1
  change wait.1 / l.block = issue.1 / l.block at hCTA
  have hOrdinal := publicationOrdinal hp hX issue.1 issue.2 slot
  rw [show readyObject l issue.1 slot = loc from
    congrArg (fun cta => Prologue.initObject l cta (readySlot slot)) hCTA.symm] at hOrdinal
  exact ⟨k, r, issue, hk, hr, hClean, hAct, hPhase, hId, rfl, ⟨pc, he⟩,
    hOrdinal.trans (PTX.Kernels.TmlFa4Fwd.Loader.ordinalOfReadyIssue he)⟩

end

/-- The ready acquire sees ordinary copies from a named publication of the observed phase. -/
theorem ReadyAcquire.seesCopies {wait issue : EvId} {slot : Fin 3} {j k phase : Nat}
    {poll arrival : Record Ref} (h : ReadyAcquire l X wait slot)
    (hPoll : (X.objects (readyObject l wait.1 slot))[j]? = some poll)
    (hPollId : poll.id = .thread wait) (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (readyObject l wait.1 slot)) j = some phase)
    (hArrival : (X.objects (readyObject l wait.1 slot))[k]? = some arrival)
    (hClean : arrival.fault = none) (hAction : arrival.action = .arrive 1 0)
    (hId : arrival.id = .async issue .arriveOn)
    (hPhase : phaseAt (X.objects (readyObject l wait.1 slot)) k = some phase)
    (hPub : X.AsyncArrive issue (readyObject l wait.1 slot) true) :
    ∀ copy, TracksCpAsync X copy issue → AsyncFinished l X copy (.write .copy) wait := by
  obtain ⟨o, _⟩ := h.record hp hX
  obtain ⟨⟨site, kind⟩, parity, hWait, hKind⟩ := h
  dsimp only at hKind
  subst kind
  obtain ⟨_, he⟩ := hPub
  have hCta := congrArg Loc.cta (readyObservation hp hX he rfl).choose_spec.2.1
  change wait.1 / l.block = issue.1 / l.block at hCta
  intro copy hTracks
  have hScope : ScopesMeet l .cluster copy.1 .cta wait.1 := by
    rw [hTracks.1]
    have hi := Step.CtaBar.thread_lt_of_get hX he
    have hw := Step.CtaBar.thread_lt_of_get hX hWait
    exact ⟨⟨hi, hw, congrArg l.clusterOfCta hCta.symm⟩, ⟨hw, hi, hCta⟩⟩
  exact o.observes_copy hX hArrival hClean hAction hId hPoll hPollId hSuccess
    hPhase hObserved hWait hTracks hScope

omit hp hX in
/-- Ordinary loader copies have the fixed vector layout and use mbarrier completion. -/
theorem linearCopyOperands {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {spec : AsyncCopy.Spec}
    (he : X.Copy i spec) :
    OrdinaryCopyShape spec 16 ∧
      ∀ k w, ¬ GroupWaitsFor X k i w :=
  ⟨PTX.Kernels.TmlFa4Fwd.actualCopyShape hX he,
    PTX.Kernels.TmlFa4Fwd.Loader.noCopyGroupWait hX he⟩

omit hp hX in
/-- An event with a tensor issue observation is a semantic tensor issue. -/
theorem tensorIssue {X : Execution} {i : EvId} {e : Event} {a : Nat} {spec : TensorCopy.Spec}
    (he : X.get i = some e) (hk : e.kind = .tensorIssue a spec) :
    X.TensorIssue i a spec := by
  obtain ⟨pc, kind⟩ := e
  cases hk
  exact ⟨pc, he⟩

/-- Each tensor issue in the loader has a legal, backed input source. -/
theorem tensorInputOperands (hFrame : OutputFootprint p X) : TensorSources l m X := by
  intro j addr s hj
  obtain ⟨hRoute, hValid, hSize, hSrc⟩ := actualTensorInputSource hp hX hj
  refine ⟨hRoute, hValid, hSize, ?_⟩
  intro slot a hGlobal
  obtain ⟨region, hRegion, hContains, byte, hByte⟩ := hSrc slot a hGlobal
  exact ⟨byte, hByte, fun _ _ _ hw => hFrame.input_unwritten hp hRegion hContains hw⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
