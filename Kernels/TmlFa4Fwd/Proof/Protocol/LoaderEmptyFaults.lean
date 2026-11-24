-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReadyFaults
import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
import Kernels.TmlFa4Fwd.Proof.Thread.EmptyRingObservation
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open Thread.Loader (readyObject)
open Thread.Mma (EmptyReleaseAt)
open Thread.Mma.Observation (emptyObject)

private theorem emptyGuardingPoll {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g k : Nat} {slot : Fin 3} (a : EmptyReleaseAt l X (emptyObject l owner slot) g k)
    (hPositive : 0 < a.ordinal) :
    ∃ j poll st, j < k ∧ (X.objects (emptyObject l owner slot))[j]? = some poll ∧
      poll.reply.waited = some true ∧ stateBefore (X.objects (emptyObject l owner slot)) j =
        some st ∧ a.ordinal = st.phase := by
  have hReady := a.matched.ready
  rw [a.matchedSlot] at hReady
  obtain ⟨completion⟩ := actualCompletedForIssuer hp hX a.issue hReady
  have hOrdinal : (Thread.Mma.atPrefix l X g a.matched.wait).kvAcquires slot = a.ordinal := by
    simp only [EmptyReleaseAt.ordinal, a.matchedSlot]
  rw [hOrdinal] at completion
  let o := (completion.acquire.record hp hX).1
  obtain ⟨i, r, issue, _, hEntry, hClean, hUnit, hAt, hEntryId, _, hPub, hGeneration⟩ :=
    Thread.Loader.readyCoverageByOrdinal hp hX o completion.record completion.success
      completion.observed (fun q _ => (phaseAlignment hp hX (actualEmptyGuardLower hp hX g slot)
        q).1) a.ordinal (Nat.le_refl _) (0 : Fin 64)
  obtain ⟨_, _, actual, hActual, _, hDone⟩ := o.arrive_source hEntry hUnit
  have heq : actual = issue := (Ref.async.inj (hActual.symm.trans hEntryId)).1
  subst actual
  have hMma := hX.observed_of_phase o.noInval hEntry hClean
    (by rw [hUnit]; trivial) completion.record completion.success hAt completion.observed
  rw [hEntryId, completion.id] at hMma
  let n := a.ordinal - 1
  have hGen : generation l X issue slot = n + 1 := by
    change generation l X issue slot = a.ordinal at hGeneration
    rw [hGeneration]
    dsimp [n]
    omega
  obtain ⟨guard, g', k', previous, hPrevious, hObs⟩ :=
    actualReleaseForNextPublicationExact hp hX hPub hGen
  have hOwner : owner / l.block = guard.acquire.1 / l.block := by
    rw [a.issuerCta hp hX, guard.issuer, publicationCta hp hX hPub]
  have hObject : emptyObject l owner slot = emptyObject l guard.acquire.1 slot :=
    congrArg (fun cta => Prologue.initObject l cta (Loader.emptySlot slot)) hOwner
  have hObs := guard.empty.observedInSlot hObs
  obtain ⟨idx, j, old, poll, phase, hOld, hOldId, hOldClean, hPoll, hId, _, hSuccess, _,
    hOldPhase, hSeen, _⟩ := hObs
  have hIndex := ObjectInit.checked_record_index_eq (X.objects_checked hX _) hOld
    previous.atIndex hOldId
  subst idx
  have hRecord := Option.some.inj (hOld.symm.trans previous.atIndex)
  subst old
  have hExact := (phaseAlignment hp hX (actualEmptyGuardLower hp hX guard.acquire.1 slot)
    phase).2 _ _ previous hOldClean hOldPhase
  obtain ⟨st, hState, hPhase⟩ := (X.objects_checked hX _).observed_phase hPoll hSuccess hSeen
  change (X.objects (emptyObject l guard.acquire.1 slot))[j]? = some poll at hPoll
  change stateBefore (X.objects (emptyObject l guard.acquire.1 slot)) j = some st at hState
  rw [← hObject] at hPoll hState
  have hPresent := object_record_present hX.tma (List.mem_of_getElem? a.atIndex)
  rw [a.notification] at hPresent
  have hEnd : Relation.TransGen (DepStep l kernel X) (.thread (g, a.matched.wait), true)
      (a.record.id, false) := by
    rw [a.notification]
    exact (Relation.TransGen.single (DepStep.of_resumes l a.matched.resumes)).tail
      (DepStep.issue ⟨_, a.issue⟩ hPresent
        (by intro t h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h))
  have hPath := ((Thread.Loader.guardedCopyBeforePublication hX guard.guarded guard.tracked
    hDone).tail (DepStep.of_witness l (Witness.of_mbarObserved hMma))).trans hEnd
  have hBefore : j < k := by
    rcases Nat.lt_trichotomy j k with hLt | hEq | hGt
    · exact hLt
    · rw [hEq, a.atIndex] at hPoll
      have hIdent := (congrArg Record.id (Option.some.inj hPoll)).trans hId
      rw [a.notification] at hIdent
      cases hIdent
    · exact (Round.Slot.not_before_of_reach hX hPath
        ⟨k, j, a.record, poll, a.atIndex, rfl, hPoll, hId, hGt⟩).elim
  exact ⟨j, poll, st, hBefore, hPoll, hSuccess, hState, by omega⟩

/-- Every actual KV-empty history record is fault free, including undrained releases. -/
theorem emptyHistoryClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (owner : Nat) (slot : Fin 3) {r : Record Ref}
    (hr : r ∈ X.objects (emptyObject l owner slot)) :
    r.fault = none := by
  classical
  let loc := emptyObject l owner slot
  let log := X.objects loc
  let labels (ref : Ref) := Σ g : Nat, Σ k : Nat,
    {a : EmptyReleaseAt l X loc g k // a.record.id = ref}
  let label (ref : Ref) := ((), if h : Nonempty (labels ref) then
    (Classical.choice h).2.2.1.ordinal else 0)
  have hInit : PairTmaRing.InitFirst X loc 1 := by
    have hCount : ∀ s : Fin 3, (Prologue.initSite (Loader.emptySlot s)).count = 1 := by decide
    rw [← hCount slot]
    exact (activeObjectHistory hp hX (Loader.emptySlot slot) hr).1
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have update {r : Record Ref} (hMem : r ∈ log) (h : CounterUpdate r.action) :=
    Thread.Mma.emptyUpdateArrival hp hX hMem h
  have hUnit {r : Record Ref} (hMem : r ∈ log) {count tx : Nat}
      (ha : r.action = .arrive count tx) : count = 1 ∧ tx = 0 := by
    obtain ⟨_, _, _, _, hAction⟩ := update hMem (by rw [ha]; trivial)
    rw [ha] at hAction
    exact Action.arrive.inj hAction
  have hNoComplete (r : Record Ref) (hMem : r ∈ log) (n : Nat) :
      r.action ≠ .completeTx n := by
    intro h
    obtain ⟨_, _, _, _, ha⟩ := update hMem (by rw [h]; trivial)
    rw [h] at ha
    cases ha
  have hNoIncrement : incrementsBefore log log.length = 0 :=
    incrementsBefore_length_of _ fun r hMem h => by
      obtain ⟨_, _, _, _, ha⟩ := update hMem (by rw [h]; trivial)
      rw [h] at ha
      cases ha
  have hChecked := X.objects_checked hX loc
  have hLabel {k : Nat} {r : Record Ref} {count tx : Nat} (hk : log[k]? = some r)
      (ha : r.action = .arrive count tx) :
      ∃ (g : Nat) (a : EmptyReleaseAt l X loc g k), a.ordinal = (label r.id).2 := by
    obtain ⟨rfl, rfl⟩ := hUnit (List.mem_of_getElem? hk) ha
    obtain ⟨g, ⟨a⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hk ha
    have hId : a.record.id = r.id :=
      congrArg Record.id (Option.some.inj (a.atIndex.symm.trans hk))
    have hExists : Nonempty (labels r.id) := ⟨⟨g, k, a, hId⟩⟩
    let w := Classical.choice hExists
    have hChoice := ObjectInit.checked_record_index_eq hChecked w.2.2.1.atIndex hk w.2.2.2
    have hValue : w.2.2.1.ordinal = (label r.id).2 := by simp only [label, dite_eq_left hExists, w]
    exact ⟨w.1, hChoice ▸ w.2.2.1, by cases hChoice; exact hValue⟩
  have hGated := hChecked.gated_arrive hNoInval ({()} : Finset Unit) label
    (fun i st hLen hState => ⟨by
      rw [Finset.card_singleton]
      exact PairTmaRing.expected_of_init hX hInit hNoInval hState,
      tx_zero_of hX hNoInval (fun r hr _ _ ha => (hUnit hr ha).2) hNoComplete hLen hState⟩)
    (fun k r c tx hk ha => by
      obtain ⟨_, st, hs, _⟩ := PairTmaRing.state_of_init hX hInit hNoInval hk
        (by intro n; rw [ha]; simp)
      exact ⟨st, hs⟩)
    (fun _ r _ _ hk ha => ⟨(hUnit (List.mem_of_getElem? hk) ha).1,
      (hUnit (List.mem_of_getElem? hk) ha).2, by change () ∈ _; simp⟩)
    (fun _ _ _ _ _ _ _ _ hk hk' ha ha' hEq => by
      obtain ⟨_, a, hA⟩ := hLabel hk ha
      obtain ⟨_, b, hB⟩ := hLabel hk' ha'
      exact a.position_eq_of_ordinal_eq hp hX b
        (hA.trans ((congrArg Prod.snd hEq).trans hB.symm)))
    (fun _ _ _ _ hk ha hPositive => by
      obtain ⟨_, a, hA⟩ := hLabel hk ha
      rw [← hA] at hPositive ⊢
      obtain ⟨j, poll, st, hBefore, hPoll, hSuccess, hState, hPhase⟩ :=
        emptyGuardingPoll hp hX a hPositive
      exact ⟨j, poll, st, hBefore, hPoll, hSuccess, hState, hPhase.le⟩)
    hNoIncrement
  cases ha : r.action with
  | init n => exact PairTmaRing.init_clean hInit hr ha
  | pollParity parity acquire =>
    exact PairTmaRing.poll_clean hX hInit hNoInval r hr ⟨parity, acquire, ha⟩
  | inval => exact (hNoInval r hr ha).elim
  | increment | completeTx =>
    obtain ⟨_, _, _, _, hAction⟩ := update hr (by rw [ha]; trivial)
    rw [ha] at hAction
    cases hAction
  | arrive count tx =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    exact (hGated k r count tx hk ha).1

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
