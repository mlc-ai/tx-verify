-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.MmaReadyConsumer
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderEmptyReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyExactOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Lemmas.Protocol.ObjectSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open Thread.Loader (readyObject AlternatesEmptyThrough emptyOrdinal OrderedGuardedReuse)
open Thread.Mma (EmptyReleaseAt ReadyPoll)
open Thread.Mma.Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem readyObservedLower (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index parity : Nat} {slot : Fin 3} (hWarp : Prologue.warpIndex l g = 12)
    (h : ReadyPoll l X g index slot parity true .cta) :
    ∃ (j phase : Nat) (r : Record Ref), (X.objects (readyObject l g slot))[j]? = some r ∧
      r.id = .thread (g, index) ∧ r.reply.waited = some true ∧
      observedAt (X.objects (readyObject l g slot)) j = some phase ∧
      (Thread.Mma.atPrefix l X g index).kvAcquires slot ≤ phase := by
  let loc := readyObject l g slot
  obtain ⟨o, j, r, hj, hId, hSuccess⟩ :=
    (Thread.Loader.acquireOfMmaPoll h).record hp hX
  have hClean := PairTmaRing.poll_clean hX o.init o.noInval
  have hCount := Poll.count_before hX hj hId hClean
  have hAlt : SelectedAlternates (objectThreadSelected g) (X.objects loc) 0 :=
    Poll.alternates hX hClean fun i _ q acq scope he => by
      have hParity := (MmaReady.followsRing hp hX hWarp).alternates
        (slot := slot) (parity := q) (index := i) (acquire := acq) (scope := scope)
        ⟨_, he, rfl⟩
      simpa only [Thread.Mma.atPrefix, Thread.Mma.kvAcquireCount, Nat.add_zero, loc,
        readyObject] using hParity
  have hSel := objectThreadSelected_iff.mpr ⟨index, hId⟩
  have hChecked := X.objects_checked hX loc
  obtain ⟨st, hState, hFloor, _⟩ :=
    hChecked.selected_poll_phase_ge o.noInval (objectThreadSelected g) (by decide) hAlt
      hj hSel hSuccess
  obtain ⟨s, hs, _, hObserved⟩ := Poll.observed_some hChecked o.noInval (by decide)
    hAlt hj hSel hSuccess (Nat.zero_le _)
  rw [hState] at hs
  cases hs
  change selectedBefore (objectThreadSelected g) (X.objects loc) j =
    Flow.okPolls loc ((X.tr g).take index) at hCount
  rw [hCount] at hFloor
  have hBound : (Thread.Mma.atPrefix l X g index).kvAcquires slot ≤ st.phase - 1 := by
    simp only [Thread.Mma.atPrefix, Thread.Mma.kvAcquireCount]
    change Flow.okPolls loc ((X.tr g).take index) ≤ st.phase - 1
    change Flow.okPolls loc ((X.tr g).take index) + 1 ≤ st.phase at hFloor
    omega
  exact ⟨j, st.phase - 1, r, hj, hId, hSuccess, hObserved, hBound⟩

private theorem recordBeforeObservation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {loc : Loc} {i j q r : Nat} {a b : Record Ref}
    (ha : (X.objects loc)[i]? = some a) (hb : (X.objects loc)[j]? = some b)
    (hq : phaseAt (X.objects loc) i = some q) (hs : b.reply.waited = some true)
    (hr : observedAt (X.objects loc) j = some r) (hPhase : q ≤ r) :
    MBarrier.Before (X.objects loc) a.id b.id := by
  have hChecked := X.objects_checked hX loc
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨st, hState, hR⟩ := hChecked.observed_phase hb hs hr
  have hBefore : i < j := by
    by_contra! hAfter
    obtain ⟨s, hS, hLe⟩ := hChecked.phase_mono hNoInval hAfter
      (List.getElem?_eq_some_iff.mp ha).1.le hState
    have hQ : s.phase = q := by simpa [phaseAt, hS] using hq
    omega
  exact ⟨i, j, a, b, ha, rfl, hb, rfl, hBefore⟩

/-- A published packet targets a ready object in the loader's own CTA. -/
theorem publicationCta (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {owner : Nat}
    {slot : Fin 3} {i : EvId} (h : X.AsyncArrive i (readyObject l owner slot) true) :
    owner / l.block = i.1 / l.block := by
  obtain ⟨_, he⟩ := h
  obtain ⟨_, _, hLoc, _⟩ := Thread.Loader.readyObservation hp hX he rfl
  exact congrArg Loc.cta hLoc

/-- The actual guard of each later publication observes at least its preceding generation. -/
def EmptyGuardLower (l : Launch) (X : Execution) (owner : Nat) (slot : Fin 3) : Prop :=
  ∀ issue n, X.AsyncArrive issue (readyObject l owner slot) true →
    generation l X issue slot = n + 1 →
    ∃ (guard : OrderedGuardedReuse l X issue slot) (j phase : Nat) (r : Record Ref),
      (X.objects (emptyObject l owner slot))[j]? = some r ∧ r.id = .thread guard.acquire ∧
        r.reply.waited = some true ∧
        observedAt (X.objects (emptyObject l owner slot)) j = some phase ∧ n ≤ phase

/-- A guard's exact earlier-success count and prefix parity establish the observation
bound. Each slot starts with the free wait before its first publication. -/
theorem EmptyGuardLower.ofPrefix (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : Nat} {slot : Fin 3}
    (hCursor : ∀ issue n, X.AsyncArrive issue (readyObject l owner slot) true →
      generation l X issue slot = n + 1 →
      ∃ guard : OrderedGuardedReuse l X issue slot, n + 1 ≤ emptyOrdinal l X guard.acquire slot ∧
        AlternatesEmptyThrough l X issue.1 issue.2 slot 1) :
    EmptyGuardLower l X owner slot := by
  intro issue n hIssue hGen
  obtain ⟨guard, hCount, hAlt⟩ := hCursor issue n hIssue hGen
  obtain ⟨j, phase, r, hj, hId, _, hSuccess, hObserved, hFloor⟩ :=
    guard.observedLowerOfPrefix hp hX hCount hAlt
  have hLoc : Thread.Loader.emptyObject l guard.acquire.1 slot = emptyObject l owner slot := by
    simp only [emptyObject, Thread.Loader.emptyObject, guard.issuer, publicationCta hp hX hIssue]
  rw [hLoc] at hj hObserved
  exact ⟨guard, j, phase, r, hj, hId, hSuccess, hObserved, hFloor⟩

/-- The actual priming and recurring waits supply the count for the guard. Only the
parities through the requested publication are needed. -/
theorem EmptyGuardLower.ofAlternation (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {owner : Nat} {slot : Fin 3}
    (hAlt : ∀ issue, X.AsyncArrive issue (readyObject l owner slot) true →
      0 < generation l X issue slot → AlternatesEmptyThrough l X issue.1 issue.2 slot 1) :
    EmptyGuardLower l X owner slot := by
  apply EmptyGuardLower.ofPrefix hp hX
  intro issue n hPub hGeneration
  have hPos : 0 < generation l X issue slot := by rw [hGeneration]; omega
  obtain ⟨guard⟩ := Thread.Loader.positiveGenerationOrderedGuard hp hX hPub hPos
  have hCount := guard.exactOrdinalLower hp hX hPub
  change generation l X issue slot ≤ emptyOrdinal l X guard.acquire slot at hCount
  exact ⟨guard, hGeneration ▸ hCount, hAlt issue hPub hPos⟩

private theorem readyReleasePath {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {g k wait : Nat}
    (release : EmptyReleaseAt l X loc g k)
    (hWait : Resumes kernel X (g, wait) (g, release.index)) :
    Relation.TransGen (DepStep l kernel X) (.thread (g, wait), true)
      (release.record.id, false) := by
  have hPresent := object_record_present hX.tma (List.mem_of_getElem? release.atIndex)
  rw [release.notification] at hPresent ⊢
  exact (Relation.TransGen.single (DepStep.of_resumes l hWait)).tail
    (DepStep.issue ⟨_, release.issue⟩ hPresent
      (by intro t h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h))

private theorem readyUnitOfObserved {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {j phase : Nat}
    {poll : Record Ref} (hObj : NoIncObject X loc 64)
    (hPoll : (X.objects loc)[j]? = some poll) (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects loc) j = some phase) :
    ∃ (k : Nat) (r : Record Ref), (X.objects loc)[k]? = some r ∧ r.action = .arrive 1 0 ∧
      r.fault = none ∧ phaseAt (X.objects loc) k = some phase := by
  classical
  obtain ⟨st, hState, hPhase⟩ := (X.objects_checked hX loc).observed_phase hPoll hSuccess hObserved
  have hCard := hObj.completed_count hX (List.getElem?_eq_some_iff.mp hPoll).1.le hState
    (q := phase) (by omega)
  have hPos : 0 < 64 := by decide
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < _ from hCard.symm ▸ hPos)
  obtain ⟨_, r, tx, hr, ha, hf, hp⟩ := Finset.mem_filter.mp hk
  obtain ⟨_, rfl, _⟩ := hObj.arrive_source hr ha
  exact ⟨k, r, hr, ha, hf, hp⟩

/-- No delivered publication is ahead of the phase of its ready record. -/
def ReadyPhaseBound (l : Launch) (X : Execution) (owner : Nat) (slot : Fin 3)
    (phase : Nat) : Prop :=
  let loc := readyObject l owner slot
  ∀ k r issue, (X.objects loc)[k]? = some r → r.fault = none →
    r.action = .arrive 1 0 → phaseAt (X.objects loc) k = some phase →
    r.id = .async issue .arriveOn → generation l X issue slot ≤ phase

/-- Each delivered empty release is paired with its phase's ready ordinal. -/
def EmptyPhaseExact (l : Launch) (X : Execution) (owner : Nat) (slot : Fin 3)
    (phase : Nat) : Prop :=
  let loc := emptyObject l owner slot
  ∀ k g (r : EmptyReleaseAt l X loc g k), r.record.fault = none →
    phaseAt (X.objects loc) k = some phase → r.ordinal = phase

private theorem readyPhaseStep (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner phase : Nat} {slot : Fin 3} (hGuard : EmptyGuardLower l X owner slot)
    (hEarlier : ∀ q < phase, EmptyPhaseExact l X owner slot q) :
    ReadyPhaseBound l X owner slot phase := by
  intro k arrival issue hArrival _ hAction hAt hId
  by_contra! hFuture
  let ready := readyObject l owner slot
  let empty := emptyObject l owner slot
  have o := Thread.Loader.readyHistory hp hX (g := owner) (slot := slot) hArrival
  obtain ⟨_, _, i, hActual, hPub, hDone⟩ := o.arrive_source hArrival hAction
  have hEq : i = issue := (Ref.async.inj (hActual.symm.trans hId)).1
  subst i
  let n := generation l X issue slot - 1
  have hGen : generation l X issue slot = n + 1 := by dsimp [n]; omega
  obtain ⟨guard, j, releasePhase, emptyPoll, hPoll, hPollId, hSuccess, hObserved, hFloor⟩ :=
    hGuard issue n hPub hGen
  obtain ⟨r, unit, hUnit, hArrive, hClean, hPhase⟩ :=
    Thread.Mma.emptyUnitThroughObservedPhase hp hX hPoll hSuccess hObserved (Nat.le_refl _)
  obtain ⟨g, ⟨release⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hUnit hArrive
  have hBefore : phase ≤ releasePhase := by dsimp [n] at hFloor; omega
  have hOrdinal := release.ordinalGeOfPriorExact hp hX hPhase hBefore hEarlier
  have hWait := release.matched.ready
  rw [release.matchedSlot] at hWait
  obtain ⟨i, seen, readyPoll, hReadyPoll, hReadyId, hReadySuccess, hSeen, hSeenGe⟩ :=
    readyObservedLower hp hX (release.issue.issuerWarp hp hX) hWait
  have hLoc : readyObject l g slot = ready := by
    simp only [ready, readyObject, release.issuerCta hp hX]
  rw [hLoc] at hReadyPoll hSeen
  unfold EmptyReleaseAt.ordinal at hOrdinal
  rw [release.matchedSlot] at hOrdinal
  have hReadyOrder := recordBeforeObservation hX hArrival hReadyPoll hAt hReadySuccess hSeen
    (hOrdinal.trans hSeenGe)
  rw [hId, hReadyId] at hReadyOrder
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) empty
  have hObs := hX.observed_of_phase hNoInval hUnit hClean
    (by rw [hArrive]; trivial) hPoll hSuccess hPhase hObserved
  have hSame := Option.some.inj (hUnit.symm.trans release.atIndex)
  rw [hSame, hPollId] at hObs
  have hPath := ((readyReleasePath hX release release.matched.resumes).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hObs))).trans
    (Thread.Loader.guardedCopyBeforePublication hX guard.guarded guard.tracked hDone)
  exact Round.Slot.not_before_of_reach hX hPath hReadyOrder

private theorem emptyPhaseStep (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner phase : Nat} {slot : Fin 3} (hGuard : EmptyGuardLower l X owner slot)
    (hEarlier : ∀ q < phase, EmptyPhaseExact l X owner slot q)
    (hReady : ∀ q ≤ phase, ReadyPhaseBound l X owner slot q) :
    EmptyPhaseExact l X owner slot phase := by
  intro k g release _ hPhase
  have hLower := release.ordinalGeOfPriorExact hp hX hPhase (Nat.le_refl _) hEarlier
  refine Nat.le_antisymm ?_ hLower
  by_contra! hFuture
  let ready := readyObject l owner slot
  let empty := emptyObject l owner slot
  have hWait := release.matched.ready
  rw [release.matchedSlot] at hWait
  obtain ⟨j, seen, poll, hPoll, hId, hSuccess, hSeen, hSeenGe⟩ :=
    readyObservedLower hp hX (release.issue.issuerWarp hp hX) hWait
  have hLoc : readyObject l g slot = ready := by
    simp only [ready, readyObject, release.issuerCta hp hX]
  rw [hLoc] at hPoll hSeen
  unfold EmptyReleaseAt.ordinal at hFuture
  rw [release.matchedSlot] at hFuture
  have hSeenLater : phase < seen := hFuture.trans_le hSeenGe
  have o := Thread.Loader.readyHistory hp hX (g := owner) (slot := slot) hPoll
  obtain ⟨i, arrival, hArrival, hAction, hClean, hAt⟩ :=
    readyUnitOfObserved hX o hPoll hSuccess hSeen
  obtain ⟨_, _, issue, hIssued, hPub, hDone⟩ := o.arrive_source hArrival hAction
  have hPrior : ∀ q ≤ phase, ∀ k r issue, (X.objects ready)[k]? = some r → r.fault = none →
      r.action = .arrive 1 0 → phaseAt (X.objects ready) k = some q →
      r.id = .async issue .arriveOn → Loader.readyOrdinal X ready issue ≤ q := by
    intro q hq k r i hr hf ha hPhase hRid
    obtain ⟨_, _, actual, hActual, hPub, _⟩ := o.arrive_source hr ha
    have hEq : actual = i := (Ref.async.inj (hActual.symm.trans hRid)).1
    subst actual
    rw [← Thread.Loader.publicationOrdinalAtObject hp hX hPub]
    exact hReady q hq k r i hr hf ha hPhase hRid
  have hPubLater := Loader.readyOrdinalAfterCoveredPrefix hp hX slot o hPoll hSuccess hSeen
    hArrival hAction hIssued hAt hSeenLater hPrior
  change phase < Loader.readyOrdinal X (readyObject l owner slot) issue at hPubLater
  rw [← Thread.Loader.publicationOrdinalAtObject hp hX hPub] at hPubLater
  change phase < generation l X issue slot at hPubLater
  let n := generation l X issue slot - 1
  have hGen : generation l X issue slot = n + 1 := by dsimp [n]; omega
  obtain ⟨guard, i', observed, emptyPoll, hEmptyPoll, hEmptyId, hEmptySuccess, hObserved, hFloor⟩ :=
    hGuard issue n hPub hGen
  have hEmptyBefore := recordBeforeObservation hX release.atIndex hEmptyPoll hPhase
    hEmptySuccess hObserved (show phase ≤ observed by dsimp [n] at hFloor; omega)
  rw [hEmptyId] at hEmptyBefore
  have hObs := hX.observed_of_phase o.noInval hArrival hClean
    (by rw [hAction]; trivial) hPoll hSuccess hAt hSeen
  rw [hIssued, hId] at hObs
  have hBack := ((Thread.Loader.guardedCopyBeforePublication hX guard.guarded guard.tracked
    hDone).tail (DepStep.of_witness l (Witness.of_mbarObserved hObs))).trans
    (readyReleasePath hX release release.matched.resumes)
  exact Round.Slot.not_before_of_reach hX hBack hEmptyBefore

/-- The two histories advance in lockstep. The induction uses the lower bound supplied by
each loader guard and the ready alternation supplied by the MMA role trace. -/
theorem phaseAlignment (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {owner : Nat}
    {slot : Fin 3} (hGuard : EmptyGuardLower l X owner slot) (phase : Nat) :
    ReadyPhaseBound l X owner slot phase ∧ EmptyPhaseExact l X owner slot phase := by
  induction phase using Nat.strong_induction_on with
  | h phase ih =>
    have hEarlier := fun q hq => (ih q hq).2
    have hReady := readyPhaseStep hp hX hGuard hEarlier
    refine ⟨hReady, emptyPhaseStep hp hX hGuard hEarlier ?_⟩
    intro q hq
    rcases Nat.eq_or_lt_of_le hq with rfl | h
    · exact hReady
    · exact (ih q h).1

/-- Subsequent publications are causally gated by the selected ready acquisition on the
elected issuer's lane. The match is through the checked empty generation. -/
theorem causalReuseForObservedIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait parity : Nat} {slot : Fin 3}
    (hIssuer : ∀ {h index : Nat} {form : Thread.Mma.ReleaseForm} {spec : TcCommit.Spec},
      Thread.Mma.ReleaseIssue X h index form spec → g / l.block = h / l.block → g = h)
    (hReady : ReadyPoll l X g wait slot parity true .cta) (hGuard : EmptyGuardLower l X g slot) :
    CausalReuse l X (g, wait) slot ((Thread.Mma.atPrefix l X g wait).kvAcquires slot) := by
  apply causalReuseOfNextWitness hp hX
  intro issue hPub hGen
  obtain ⟨guard, j, phase, poll, hPoll, hId, hSuccess, hObserved, hFloor⟩ :=
    hGuard issue _ hPub hGen
  obtain ⟨k, r, hAt, hAction, hClean, hPhase⟩ :=
    Thread.Mma.emptyUnitThroughObservedPhase hp hX hPoll hSuccess hObserved (Nat.le_refl _)
  obtain ⟨issuer, ⟨release⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hAt hAction
  have hSameIssuer := hIssuer release.issue (release.issuerCta hp hX)
  subst issuer
  have hSame := Option.some.inj (hAt.symm.trans release.atIndex)
  have hExact := (phaseAlignment hp hX hGuard phase).2 k g release (hSame ▸ hClean) hPhase
  have hw : ReadyPoll l X g wait release.matched.slot parity true .cta := by
    rw [release.matchedSlot]
    exact hReady
  have hOrder : (Thread.Mma.atPrefix l X g wait).kvAcquires release.matched.slot ≤
      release.ordinal := by rw [release.matchedSlot, hExact]; exact hFloor
  have hResumes := release.matched.resumesOfEarlierReady hX hw hOrder
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (emptyObject l g slot)
  have hObs := hX.observed_of_phase hNoInval hAt hClean
    (by rw [hAction]; trivial) hPoll hSuccess hPhase hObserved
  rw [hSame, hId] at hObs
  exact ⟨release.record.id, ⟨⟨guard.acquire, guard.copy, hObs, guard.guarded, guard.tracked⟩⟩,
    readyReleasePath hX release hResumes⟩

/-- For the elected release issuer, the ready poll observes its actual role-machine ordinal. -/
theorem readyGenerationForObservedIssuer (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g wait parity : Nat} {slot : Fin 3}
    (hw : Prologue.warpIndex l g = 12)
    (hIssuer : ∀ {h index : Nat} {form : Thread.Mma.ReleaseForm} {spec : TcCommit.Spec},
      Thread.Mma.ReleaseIssue X h index form spec → g / l.block = h / l.block → g = h)
    (hReady : ReadyPoll l X g wait slot parity true .cta) (hGuard : EmptyGuardLower l X g slot) :
    ∃ (j : Nat) (r : Record Ref), (X.objects (readyObject l g slot))[j]? = some r ∧
      r.id = .thread (g, wait) ∧ r.reply.waited = some true ∧
      observedAt (X.objects (readyObject l g slot)) j =
        some ((Thread.Mma.atPrefix l X g wait).kvAcquires slot) := by
  have hRing := MmaReady.followsRing hp hX hw
  apply hReady.generationOfReuse hp hX (fun _ _ _ _ => hRing.alternates)
  intro issue hPub hDone hBefore
  change (Thread.Mma.atPrefix l X g wait).kvAcquires slot <
    Loader.readyOrdinal X (readyObject l g slot) issue at hBefore
  rw [← Thread.Loader.publicationOrdinalAtObject hp hX hPub] at hBefore
  exact causalReuseForObservedIssuer hp hX hIssuer hReady hGuard issue hPub hDone hBefore

/-- For the elected release issuer, the ready poll observes its actual role-machine ordinal. -/
theorem readyGenerationForIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait index parity : Nat} {slot : Fin 3} {form : Thread.Mma.ReleaseForm}
    {spec : TcCommit.Spec} (anchor : Thread.Mma.ReleaseIssue X g index form spec)
    (hReady : ReadyPoll l X g wait slot parity true .cta) (hGuard : EmptyGuardLower l X g slot) :
    ∃ (j : Nat) (r : Record Ref), (X.objects (readyObject l g slot))[j]? = some r ∧
      r.id = .thread (g, wait) ∧ r.reply.waited = some true ∧
      observedAt (X.objects (readyObject l g slot)) j =
        some ((Thread.Mma.atPrefix l X g wait).kvAcquires slot) :=
  readyGenerationForObservedIssuer hp hX (anchor.issuerWarp hp hX)
    (fun h hc => anchor.sameIssuer hp hX h hc) hReady hGuard

/-- The checked poll on the issuing lane supplies the completed packet generation. -/
theorem completedForObservedIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait parity : Nat} {slot : Fin 3} (hw : Prologue.warpIndex l g = 12)
    (hIssuer : ∀ {h index : Nat} {form : Thread.Mma.ReleaseForm} {spec : TcCommit.Spec},
      Thread.Mma.ReleaseIssue X h index form spec → g / l.block = h / l.block → g = h)
    (hReady : ReadyPoll l X g wait slot parity true .cta) (hGuard : EmptyGuardLower l X g slot) :
    Nonempty (Completed l X (g, wait) slot ((Thread.Mma.atPrefix l X g wait).kvAcquires slot)) := by
  obtain ⟨j, r, hj, hId, hSuccess, hObserved⟩ :=
    readyGenerationForObservedIssuer hp hX hw hIssuer hReady hGuard
  exact ⟨⟨Thread.Loader.acquireOfMmaPoll hReady, j, r, hj, hId, hSuccess, hObserved⟩⟩

/-- The checked poll on the issuing lane supplies the completed packet generation. -/
theorem completedForIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait index parity : Nat} {slot : Fin 3} {form : Thread.Mma.ReleaseForm}
    {spec : TcCommit.Spec} (anchor : Thread.Mma.ReleaseIssue X g index form spec)
    (hReady : ReadyPoll l X g wait slot parity true .cta) (hGuard : EmptyGuardLower l X g slot) :
    Nonempty (Completed l X (g, wait) slot ((Thread.Mma.atPrefix l X g wait).kvAcquires slot)) := by
  obtain ⟨j, r, hj, hId, hSuccess, hObserved⟩ := readyGenerationForIssuer hp hX anchor hReady hGuard
  exact ⟨⟨Thread.Loader.acquireOfMmaPoll hReady, j, r, hj, hId, hSuccess, hObserved⟩⟩

/-- The observed generation gives this loader lane's publication at the exact abstract
ordinal. The acquire observes all copies tracked by that publication. -/
theorem Completed.visiblePublicationOfLane (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {wait : EvId} {slot : Fin 3} {phase : Nat}
    (h : Completed l X wait slot phase) (hGuard : EmptyGuardLower l X wait.1 slot) (lane : Fin 64) :
    ∃ issue, issue.1 = Thread.Loader.producer l (wait.1 / l.block) lane ∧
      X.AsyncArrive issue (readyObject l wait.1 slot) true ∧
      X.async.arrived issue = true ∧ generation l X issue slot = phase ∧
      ∀ copy, TracksCpAsync X copy issue → AsyncFinished l X copy (.write .copy) wait := by
  have o := (h.acquire.record hp hX).1
  obtain ⟨k, r, issue, _, hAt, hClean, hAction, hPhase, hId, hLane, hPub, hGeneration⟩ :=
    Thread.Loader.readyCoverageByOrdinal hp hX o h.record h.success h.observed
      (fun q _ => (phaseAlignment hp hX hGuard q).1) phase (Nat.le_refl _) lane
  obtain ⟨_, _, actual, hActual, _, hArrived⟩ := o.arrive_source hAt hAction
  have hIssueEq := (Ref.async.inj (hActual.symm.trans hId)).1
  subst actual
  exact ⟨issue, hLane, hPub, hArrived, hGeneration,
    h.acquire.seesCopies hp hX h.record h.id h.success
      h.observed hAt hClean hAction hId hPhase hPub⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
