-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyCycle
public import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.MBarrier PTX.MbarRing PTX.AsyncCopy Prologue

noncomputable section

/-- If no ready phase contains a producer ahead of that phase's use, completion of
a ready phase proves that it and all earlier phases each contain one arrival per
loader lane. The finite count reuses the ring's generic content theorem. -/
theorem readyPhaseCoverageThrough {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j phase through : Nat} (stage : Fin 3)
    (hObj : NoIncObject X (initObject l cta (readySlot stage)) 64)
    {poll : Record Ref} (hRecord : (X.objects (initObject l cta (readySlot stage)))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (initObject l cta (readySlot stage))) j = some phase)
    (hThrough : through ≤ phase)
    (hCap : let loc := initObject l cta (readySlot stage)
      ∀ q ≤ through, ∀ k r issue, (X.objects loc)[k]? = some r → r.fault = none →
        r.action = .arrive 1 0 → phaseAt (X.objects loc) k = some q →
        r.id = .async issue .arriveOn → readyOrdinal X loc issue ≤ q) :
    let loc := initObject l cta (readySlot stage)
    ∀ q ≤ through, ∀ lane : Fin 64, ∃ (k : Nat) (r : Record Ref) (pc : Nat), k < j ∧
      (X.objects loc)[k]? = some r ∧ r.fault = none ∧ r.action = .arrive 1 0 ∧
      phaseAt (X.objects loc) k = some q ∧
      r.id = .async (readyIssue X loc (readyProducer l cta lane) q) .arriveOn ∧
      X.get (readyIssue X loc (readyProducer l cta lane) q) =
        some ⟨pc, .asyncArrive loc true⟩ := by
  classical
  dsimp only
  let loc := initObject l cta (readySlot stage)
  let log := X.objects loc
  let support := (Finset.range log.length).filter (fun k =>
    ∃ q ≤ through, UnitArrivalIn log q k)
  have hChecked := X.objects_checked hX loc
  obtain ⟨state, hs, hPhase⟩ := hChecked.observed_phase hRecord hSuccess hObserved
  have hj : j ≤ log.length := ((List.getElem?_eq_some_iff.mp hRecord).1).le
  let Label := fun (k : Nat) (item : Fin 64 × Nat) =>
    ∃ (r : Record Ref) (pc gen : Nat), gen ≤ through ∧
      log[k]? = some r ∧ r.fault = none ∧ r.action = .arrive 1 0 ∧ phaseAt log k = some gen ∧
      r.id = .async (readyIssue X loc (readyProducer l cta item.1) item.2) .arriveOn ∧
      X.get (readyIssue X loc (readyProducer l cta item.1) item.2) =
        some ⟨pc, .asyncArrive loc true⟩ ∧ item.2 ≤ gen
  have hDecode (k : Nat) (hk : k ∈ support) : ∃ item, Label k item := by
    obtain ⟨gen, hg, r, tx, hr, hAct, hCl, hPh⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨_, rfl, issue, hId, ⟨pc, he⟩, _⟩ := hObj.arrive_source hr hAct
    obtain ⟨lane, hLane⟩ := readyArrivalProducer hp hX stage he
    have hLimit := hCap gen hg k r issue hr hCl hAct hPh hId
    have hs : readyIssue X loc issue.1 (readyOrdinal X loc issue) = issue := by
      cases issue
      exact readyIssueOfActual he
    rw [hLane] at hs
    exact ⟨(lane, readyOrdinal X loc issue), r, pc, gen, hg, hr, hCl, hAct, hPh,
      hs.symm ▸ hId, hs.symm ▸ he, hLimit⟩
  let label := fun k : Nat => if hk : k ∈ support then Classical.choose (hDecode k hk) else (0, 0)
  have hLabel (k : Nat) (hk : k ∈ support) : Label k (label k) := by
    simpa only [label, dite_eq_left hk] using Classical.choose_spec (hDecode k hk)
  have hInj : Set.InjOn label ↑support := by
    intro i hi k hk he
    obtain ⟨r, _, _, _, hr, _, _, _, hR, _, _⟩ := hLabel i hi
    obtain ⟨s, _, _, _, hs, _, _, _, hS, _, _⟩ := hLabel k hk
    rw [he] at hR
    exact object_record_index_unique hX.tma.2.2.1 hr hs (hR.trans hS.symm)
  let items := support.image label
  let atPhase := fun item : Fin 64 × Nat =>
    if h : item ∈ items then (phaseAt log (Classical.choose (Finset.mem_image.mp h))).getD 0
    else 0
  have hAt (k : Nat) (hk : k ∈ support) : atPhase (label k) = (phaseAt log k).getD 0 := by
    let hmem : label k ∈ items := Finset.mem_image_of_mem _ hk
    dsimp only [atPhase]
    rw [dite_eq_left hmem]
    have hc := Classical.choose_spec (Finset.mem_image.mp hmem)
    rw [hInj hc.1 hk hc.2]
  have hEach (q : Nat) (hq : q ≤ through) :
      (items.filter (fun item => atPhase item = q)).card = Fintype.card (Fin 64) := by
    let present := (Finset.range log.length).filter (UnitArrivalIn log q)
    have hc : present.card = 64 := hObj.completed_count hX hj hs (by omega)
    have hSub : present ⊆ support := by
      intro k hk
      obtain ⟨hRange, hUnit⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hRange, q, hq, hUnit⟩
    have hImage : present.image label = items.filter (fun item => atPhase item = q) := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨r, tx, _, _, _, hAtQ⟩ := (Finset.mem_filter.mp hk).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem _ (hSub hk), by rw [hAt k (hSub hk), hAtQ]; rfl⟩
      · intro hx
        obtain ⟨hx, hq'⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨r, _, gen, _, hr, hCl, hAct, hPhase, _, _, _⟩ := hLabel k hk
        rw [hAt k hk, hPhase] at hq'
        obtain rfl : gen = q := hq'
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hk).1, r, 0, hr, hAct, hCl, hPhase⟩)
    rw [← hImage, Finset.card_image_of_injOn (hInj.mono hSub), hc]
    simp
  have hBound (q : Nat) (_ : q ≤ through) (item : Fin 64 × Nat)
      (hItem : item ∈ items) (hq : atPhase item = q) : item.2 ≤ q := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hItem
    obtain ⟨_, _, gen, _, _, _, _, hg, _, _, hc⟩ := hLabel k hk
    rw [hAt k hk, hg] at hq
    exact hq ▸ hc
  have hCovered := Round.content items atPhase id through (by intros; assumption) hEach hBound
  intro q hq lane
  obtain ⟨hm, hItem⟩ := (hCovered q hq).2 lane
  obtain ⟨k, hk, hEq⟩ := Finset.mem_image.mp hm
  obtain ⟨r, pc, gen, _, hGet, hCl, hAct, hg, hId, hIss, _⟩ := hLabel k hk
  rw [← hEq, hAt k hk, hg] at hItem
  obtain rfl : gen = q := hItem
  have hJ : k < j := by
    by_contra! hK
    obtain ⟨u, hu, hle⟩ := hChecked.phase_mono hObj.noInval hK
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1).le hs
    change (stateBefore log k).map State.phase = some gen at hg
    rw [hu] at hg
    have hUnit : u.phase = gen := Option.some.inj hg
    omega
  rw [hEq] at hId hIss
  exact ⟨k, r, pc, hJ, hGet, hCl, hAct, hg, hId, hIss⟩

/-- The observed ready phase and its predecessors contain every lane's corresponding arrival
when each lane stays within the phase's ordinal. -/
theorem readyPhaseCoverage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j phase : Nat} (stage : Fin 3)
    (hObj : NoIncObject X (initObject l cta (readySlot stage)) 64)
    {poll : Record Ref} (hRecord : (X.objects (initObject l cta (readySlot stage)))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (initObject l cta (readySlot stage))) j = some phase)
    (hCap : let loc := initObject l cta (readySlot stage)
      ∀ q ≤ phase, ∀ k r issue, (X.objects loc)[k]? = some r → r.fault = none →
        r.action = .arrive 1 0 → phaseAt (X.objects loc) k = some q →
        r.id = .async issue .arriveOn → readyOrdinal X loc issue ≤ q) :
    let loc := initObject l cta (readySlot stage)
    ∀ q ≤ phase, ∀ lane : Fin 64, ∃ (k : Nat) (r : Record Ref) (pc : Nat), k < j ∧
      (X.objects loc)[k]? = some r ∧ r.fault = none ∧ r.action = .arrive 1 0 ∧
      phaseAt (X.objects loc) k = some q ∧
      r.id = .async (readyIssue X loc (readyProducer l cta lane) q) .arriveOn ∧
      X.get (readyIssue X loc (readyProducer l cta lane) q) =
        some ⟨pc, .asyncArrive loc true⟩ :=
  readyPhaseCoverageThrough hp hX stage hObj hRecord hSuccess hObserved (Nat.le_refl _) hCap

/-- Once a completed prefix of ready phases respects its publication bounds, no producer can
contribute one of that prefix's ordinals to a later observed phase. -/
theorem readyOrdinalAfterCoveredPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j k phase through : Nat} (slot : Fin 3)
    (hObj : NoIncObject X (initObject l cta (readySlot slot)) 64)
    {poll arrival : Record Ref} {issue : EvId}
    (hPoll : (X.objects (initObject l cta (readySlot slot)))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hSeen : observedAt (X.objects (initObject l cta (readySlot slot))) j = some phase)
    (hArrival : (X.objects (initObject l cta (readySlot slot)))[k]? = some arrival)
    (hAction : arrival.action = .arrive 1 0) (hId : arrival.id = .async issue .arriveOn)
    (hPhase : phaseAt (X.objects (initObject l cta (readySlot slot))) k = some phase)
    (hThrough : through < phase)
    (hEarlier : let loc := initObject l cta (readySlot slot)
      ∀ q ≤ through, ∀ i r published, (X.objects loc)[i]? = some r → r.fault = none →
        r.action = .arrive 1 0 → phaseAt (X.objects loc) i = some q →
        r.id = .async published .arriveOn → readyOrdinal X loc published ≤ q) :
    through < readyOrdinal X (initObject l cta (readySlot slot)) issue := by
  let loc := initObject l cta (readySlot slot)
  change through < readyOrdinal X loc issue
  by_contra! hLow
  obtain ⟨_, _, actual, hActual, ⟨_, hIssue⟩, _⟩ := hObj.arrive_source hArrival hAction
  have hEq : actual = issue := (Ref.async.inj (hActual.symm.trans hId)).1
  subst actual
  obtain ⟨lane, hLane⟩ := readyArrivalProducer hp hX slot hIssue
  have hIssueByOrdinal : readyIssue X loc (readyProducer l cta lane) (readyOrdinal X loc issue) =
      issue := by
    rw [← hLane]
    cases issue
    exact readyIssueOfActual hIssue
  obtain ⟨i, earlier, _, _, hRecord, _, _, hPrior, hEarlierId, _⟩ :=
    readyPhaseCoverageThrough hp hX slot hObj hPoll hSuccess hSeen hThrough.le hEarlier
      (readyOrdinal X loc issue) hLow lane
  rw [hIssueByOrdinal] at hEarlierId
  have hPosition := object_record_index_unique hX.tma.2.2.1 hRecord hArrival
    (hEarlierId.trans hId.symm)
  rw [hPosition, hPhase] at hPrior
  have hEqual := Option.some.inj hPrior
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
