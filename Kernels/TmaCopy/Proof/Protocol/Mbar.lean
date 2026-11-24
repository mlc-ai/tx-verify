-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Protocol.Events
public import Lemmas.Protocol.MbarOneShot

@[expose] public section

/-! # `tma_copy`: the mbarrier's event table

Every operation on an mbarrier is thread 0's initialization of `mbar`, its expect-tx arrival of
16 bytes, the bulk copy's complete-tx of 16 bytes, or one of its polls of parity 0, all on `mbar`
(`object_action_cases`, from the records' sources). Thread 0's program order puts the
initialization before every other event, so `mbar` is a one-phase mbarrier with that arrival and
that copy (`table`, a `MbarOneShot.Table`). From it: no record faults (`object_fault_free`),
every record follows the published initialization (`object_published`), every successful wait
observes the copy's completion (`wait_observes_copy`), and after the arrival `mbar` is in the
completed phase once the copy has notified (`final_state`). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof AsyncCopy MBarrier
noncomputable section

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}
variable (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include ht hX

/-- Every object operation is the initialization, the one expect-tx arrival, this
copy's actual notification, or a source-level poll. No other producer can be invented. -/
theorem object_action_cases {m : Loc} {id : Ref} {act : Action}
    (ha : objectAction X X.async m id = some act) : m = mbar L.sharedBase ∧
    ((id = .thread (0, 0) ∧ act = .init 1) ∨
      (id = .thread (0, 2) ∧ act = .arrive 1 16) ∨
      (id = .async (0, 3) (.notify .copy) ∧ act = .completeTx 16 ∧
        (X.async.copies (0, 3)).notified = true) ∨
      (∃ j ok, 4 ≤ j ∧ id = .thread (0, j) ∧ act = .pollParity 0 ok ∧
        X.get (0, j) = some (waitE L.sharedBase ok))) := by
  cases id with
  | thread i =>
    unfold objectAction at ha
    cases he : X.get i with
    | none => simp [he] at ha
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp only [he] at ha
      all_goals try contradiction
      case mbInval mb => exact (no_inval ht hX ⟨pc, he⟩).elim
      case asyncArrive mb noinc => exact (no_asyncArrive ht hX ⟨pc, he⟩).elim
      case mbInit mb n =>
        obtain ⟨rfl, rfl, rfl⟩ := mbInit_cases ht hX ⟨pc, he⟩
        split_ifs at ha with hm
        · cases ha; exact ⟨hm.symm, .inl ⟨rfl, rfl⟩⟩
      case arrive mb tx count rel sc =>
        obtain ⟨rfl, rfl, rfl, rfl⟩ := arrive_cases ht hX ⟨pc, he⟩
        split_ifs at ha with hm
        · cases ha; exact ⟨hm.symm, .inr (.inl ⟨rfl, rfl⟩)⟩
      case wait mb parity ok acq sc =>
        obtain ⟨hg, hj, rfl, rfl, rfl, rfl⟩ := wait_cases ht hX he
        split_ifs at ha with hm
        · cases ha
          obtain ⟨g, j⟩ := i
          simp only at hg hj
          subst g
          have hpc : pc = 13 := by
            rcases (event_cases ht hX he).2 with ⟨hn, _⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ |
              ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, ⟨ok', hh⟩ | ⟨_, _, _, _, hh⟩⟩
            · exact (hn rfl).elim
            all_goals try (simp [initE, fenceE, arriveE, bulkE] at hh)
            · exact (Event.mk.inj hh).1
            · rcases hh with ⟨_, hh⟩ | ⟨_, _, _, _, _, hh⟩ | hh | ⟨_, _, hh, _⟩ <;>
                simp [rdE, wrE] at hh
          subst pc
          exact ⟨hm.symm, .inr (.inr (.inr ⟨j, ok, hj, rfl, rfl, he⟩))⟩
  | async i p =>
    cases p <;> simp only [objectAction] at ha
    all_goals try contradiction
    case notifyCopy =>
      cases hs : issuedBy X i with
      | none => simp [hs] at ha
      | some spec =>
        obtain ⟨rfl, rfl⟩ := bulk_cases ht hX (issuedBy_some.mp hs)
        simp only [hs] at ha
        change (if (copySpec A L.sharedBase).completion = .mbarrier m ∧
          (X.async.copies (0, 3)).notified = true then
          some (.completeTx (copySpec A L.sharedBase).dst.size) else none) = some act at ha
        split_ifs at ha with hc
        · cases ha
          have hm : mbar L.sharedBase = m := by simpa [copySpec, bulkSpec] using hc.1
          exact ⟨hm.symm, .inr (.inr (.inl ⟨rfl, rfl, hc.2⟩))⟩
    case tcNotify =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he] at ha
        all_goals try contradiction
        exact ((noTc ht hX) i pc _ he).elim
    case arriveOn =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc, kind⟩ := ev
        cases kind <;> simp only [he] at ha
        all_goals try contradiction
        exact (no_asyncArrive ht hX ⟨pc, he⟩).elim
    case notifyLoad | notifyCta =>
      cases he : X.get i with
      | none => simp [he] at ha
      | some ev =>
        obtain ⟨pc,kind⟩ := ev
        cases kind <;> simp only [he] at ha
        all_goals try contradiction
        all_goals exact False.elim (not_class ht hX he rfl)

/-- The same classification holds for every recorded operation, including records
whose validity still has to be proved by the kernel's protocol invariant. -/
theorem object_record_cases {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) :
    m = mbar L.sharedBase ∧
    ((r.id = .thread (0, 0) ∧ r.action = .init 1) ∨
      (r.id = .thread (0, 2) ∧ r.action = .arrive 1 16) ∨
      (r.id = .async (0, 3) (.notify .copy) ∧ r.action = .completeTx 16 ∧
        (X.async.copies (0, 3)).notified = true) ∨
      (∃ j ok, 4 ≤ j ∧ r.id = .thread (0, j) ∧ r.action = .pollParity 0 ok ∧
        X.get (0, j) = some (waitE L.sharedBase ok))) :=
  object_action_cases ht hX (((hX.tma.2.2.1 m).2.1 r hr).1)

/-- Reaching any source event at or after the arrival includes that arrival. -/
theorem arrive_get {j : Nat} {ev : Event} (he : X.get (0, j) = some ev) (hj : 2 ≤ j) :
    X.get (0, 2) = some (arriveE L.sharedBase) := by
  obtain ⟨ev', h2⟩ := pre_of he hj
  rcases (event_cases ht hX h2).2 with ⟨hne, _⟩ | ⟨_, hi, _⟩ | ⟨_, hi, _⟩ |
    ⟨_, _, hev⟩ | ⟨_, hi, _⟩ | ⟨_, hi, _⟩
  all_goals simp_all

omit ht hX in
/-- A later event of thread 0 is after its event `k` in program order. -/
theorem po_zero {k j : Nat} {ev ev' : Event} (hk : X.get (0, k) = some ev)
    (hacc : ev.acc = none) (hj : k < j) (he : X.get (0, j) = some ev') : baseCausality L X (0, k)
        (0, j) :=
  .single (.inl (po_of_source_not_access rfl hj (len_of_get he) (by rw [hk]; exact hacc)))

/-- **`mbar` is a one-phase mbarrier** of the initialization, the arrival expecting 16 bytes,
the copy of 16 bytes and the polls of thread 0. -/
theorem table : MbarOneShot.Table L X (mbar L.sharedBase) (0, 0) [(.thread (0, 2), 16)]
    [((0, 3), 16)] := by
  refine ⟨by decide, by decide, by simp, by simp, by simp, fun r hr => ?_,
    fun r hr a ha hid => ?_, fun r hr hid => ?_, fun ev he => ?_, fun c hc s hs => ?_,
    fun v hv => no_inval ht hX hv⟩
  · rcases (object_record_cases ht hX hr).2 with h | h | ⟨h1, h2, -⟩ | ⟨j, ok, -, h1, h2, -⟩
    · exact .inl h
    · exact .inr (.inl ⟨_, List.mem_singleton_self _, h⟩)
    · exact .inr (.inr (.inl ⟨_, List.mem_singleton_self _, h1, h2⟩))
    · exact .inr (.inr (.inr ⟨_, ok, h1, h2⟩))
  · obtain rfl := List.mem_singleton.mp ha
    rcases (object_record_cases ht hX hr).2 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨j, ok, hj, h, -⟩
    · rw [h] at hid; cases hid
    · exact h
    · rw [h] at hid; cases hid
    · rw [h] at hid; cases hid; omega
  · -- the issuer of every other record is an event of thread 0 after the initialization
    have hp := object_record_present hX.tma hr
    rcases (object_record_cases ht hX hr).2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, hn⟩ |
      ⟨j, ok, hj, h, -, he⟩
    · exact (hid h).elim
    · rw [h] at hp ⊢
      obtain ⟨ev, he⟩ := hp
      exact po_zero (init_get ht hX he) (by simp [initE, Event.acc]) (by decide) he
    · obtain ⟨ev, he⟩ :=
        asyncPresent_issuer hX.effectValidity (i := (0, 3)) (p := .notify .copy) hn
      rw [h]
      exact po_zero (init_get ht hX he) (by simp [initE, Event.acc]) (by decide) he
    · rw [h]
      exact po_zero (init_get ht hX he) (by simp [initE, Event.acc]) (by omega) he
  · rcases (event_cases ht hX he).2 with ⟨h, -⟩ | ⟨-, -, rfl⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩
    · exact (h rfl).elim
    · rfl
    all_goals simp at h
  · obtain rfl := List.mem_singleton.mp hc
    rw [(bulk_cases ht hX (issuedBy_some.mp hs)).2]
    rfl

/-- **No record faults.** -/
theorem object_fault_free {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) : r.fault = none := by
  obtain ⟨rfl, -⟩ := object_record_cases ht hX hr
  exact ((table ht hX).hist hX).fault_free hX hr

/-- **Every record follows the published initialization.** -/
theorem object_published {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) :
    ObjectPublished L X m r := by
  obtain ⟨rfl, -⟩ := object_record_cases ht hX hr
  exact (table ht hX).published hX hr

/-- **Every successful wait observes the copy's completion.** -/
theorem wait_observes_copy {w : EvId} {m : Loc} (hw : X.AcquireWait w m) :
    ∃ ws, AsyncObserved X (0, 3) (.notify .copy) w true ws := by
  obtain ⟨pc, parity, scope, he⟩ := hw
  obtain ⟨-, -, rfl, rfl, -, rfl⟩ := wait_cases ht hX he
  exact ⟨.cta, ((table ht hX).hist hX).observes_copy hX (c := ((0, 3), 16))
    (List.mem_singleton_self _) he⟩

/-- **After the arrival, `mbar` has a state**, the completed phase once the copy has
notified. -/
theorem final_state {j : Nat} {ev : Event} (he : X.get (0, j) = some ev) (hj : 2 ≤ j) :
    ∃ s, stateBefore (X.objects (mbar L.sharedBase)) (X.objects (mbar L.sharedBase)).length =
      some s ∧ ((X.async.copies (0, 3)).notified = true → s.phase = 1) := by
  have hact :
      objectAction X X.async (mbar L.sharedBase) (.thread (0, 2)) = some (.arrive 1 16) := by
    simp only [objectAction, arrive_get ht hX he hj, arriveE, ↓reduceIte]
  obtain ⟨r, hr, hid, -⟩ :=
    ((table ht hX).hist hX).arrive_recorded hX (List.mem_singleton_self _) hact
  obtain ⟨s, hs, -, hphase⟩ := ((table ht hX).hist hX).final_state hX (List.ne_nil_of_mem hr)
  exact ⟨s, hs, fun hn => hphase.mpr ⟨fun a ha => by
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨r, hr, hid⟩, fun c hc => by
    obtain rfl := List.mem_singleton.mp hc
    exact ((table ht hX).hist hX).copy_recorded hX hc hn⟩⟩

end

end PTX.Kernels.TmaCopy.Proof
