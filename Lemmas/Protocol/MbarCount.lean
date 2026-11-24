-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierTransactions
public import Lemmas.Protocol.MbarInit
public import Lemmas.Protocol.MbarPending

@[expose] public section

/-! # Counting records of one checked mbarrier history

A proof tool. On one checked history: positions whose records carry identities of a finset are at
most that finset (`card_positions_le`), and a finset whose elements name, injectively, records at
positions of a set is at most that set (`card_le_positions`); a history whose arrivals expect no
bytes and that has no complete-tx keeps a zero transaction counter (`tx_zero`); after the
initialization, a poll never faults (`poll_fault_none`), and a unit arrival without bytes faults
only by underflow or an unobserved preceding phase (`arrive_fault_none`). -/

namespace PTX.MBarrier

noncomputable section

/-- Positions of a checked history whose records carry identities `u y` of a finset `T` are at
most `T`. -/
theorem card_positions_le {ι κ : Type} [DecidableEq ι] {log : List (Record ι)}
    (h : CheckedLog log) (T : Finset κ) (u : κ → ι) (P : Finset Nat)
    (hP : ∀ i ∈ P, ∃ r, log[i]? = some r ∧ ∃ y ∈ T, r.id = u y) : P.card ≤ T.card := by
  classical
  let idAt : Nat → Option ι := fun i => (log[i]?).map Record.id
  have hinj : Set.InjOn idAt P := by
    intro i hi i' hi' heq
    obtain ⟨r, hr, -⟩ := hP i hi
    obtain ⟨r', hr', -⟩ := hP i' hi'
    simp only [idAt, hr, hr', Option.map_some, Option.some.injEq] at heq
    exact ObjectInit.checked_record_index_eq h hr hr' heq
  calc P.card = (P.image idAt).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (T.image (fun y => some (u y))).card := Finset.card_le_card (by
        intro o ho
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
        obtain ⟨r, hr, y, hy, hid⟩ := hP i hi
        exact Finset.mem_image.mpr ⟨y, hy, by simp [idAt, hr, hid]⟩)
    _ ≤ T.card := Finset.card_image_le

/-- A finset whose elements name, injectively, records at positions of `P` is at most `P`. -/
theorem card_le_positions {ι κ : Type} [DecidableEq ι] {log : List (Record ι)}
    (T : Finset κ) (u : κ → ι) (hu : Set.InjOn u T) (P : Finset Nat)
    (h : ∀ y ∈ T, ∃ i ∈ P, ∃ r, log[i]? = some r ∧ r.id = u y) : T.card ≤ P.card := by
  classical
  let idAt : Nat → Option ι := fun i => (log[i]?).map Record.id
  have hinj : Set.InjOn (fun y => some (u y)) T := fun y hy y' hy' he =>
    hu hy hy' (Option.some.inj he)
  calc T.card = (T.image (fun y => some (u y))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P.image idAt).card := Finset.card_le_card (by
        intro o ho
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ho
        obtain ⟨i, hi, r, hr, hid⟩ := h y hy
        exact Finset.mem_image.mpr ⟨i, hi, by simp [idAt, hr, hid]⟩)
    _ ≤ P.card := Finset.card_image_le

private theorem expectedTxBytes_zero {ι : Type} {xs : List (Record ι)}
    (h : ∀ r ∈ xs, ∀ n b, r.action = .arrive n b → b = 0) : expectedTxBytes xs = 0 := by
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    simp only [expectedTxBytes, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    unfold Record.expectedTxBytes
    cases ha : r.action with
    | arrive n b => cases r.fault <;> simp [h r List.mem_cons_self n b ha]
    | _ => cases r.fault <;> simp

private theorem completedTxBytes_zero {ι : Type} {xs : List (Record ι)}
    (h : ∀ r ∈ xs, ∀ n, r.action ≠ .completeTx n) : completedTxBytes xs = 0 := by
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    simp only [completedTxBytes, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    unfold Record.completedTxBytes
    cases ha : r.action <;> cases r.fault <;> simp
    exact absurd ha (h r List.mem_cons_self _)

/-- A history whose arrivals expect no bytes and that has no complete-tx keeps a zero
transaction counter. -/
theorem tx_zero {ι : Type} {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    (harr : ∀ r ∈ log, ∀ n b, r.action = .arrive n b → b = 0)
    (hct : ∀ r ∈ log, ∀ n, r.action ≠ .completeTx n) {j : Nat} {s : State}
    (hs : stateBefore log j = some s) : s.tx = 0 := by
  have hj : j ≤ log.length := by
    unfold stateBefore at hs
    split_ifs at hs with h0
    obtain ⟨r, hr, -⟩ := Option.bind_eq_some_iff.mp hs
    have := (List.getElem?_eq_some_iff.mp hr).1
    omega
  rw [h.tx_balance hni hj hs,
    expectedTxBytes_zero (fun r hr => harr r (List.mem_of_mem_take hr)),
    completedTxBytes_zero (fun r hr => hct r (List.mem_of_mem_take hr))]
  rfl

/-- A poll of an initialized object does not fault. -/
theorem poll_fault_none {ι : Type} {log : List (Record ι)} (h : CheckedLog log) {i : Nat}
    {r : Record ι} {s : State} (hi : log[i]? = some r) (hs : stateBefore log i = some s)
    {p : Nat} {ok : Bool} (ha : r.action = .pollParity p ok) : r.fault = none := by
  have hr := h.at hi
  rw [hs] at hr
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, pure, Except.pure] at hr
  exact hr.2

/-- A unit arrival without bytes on an initialized object with a zero transaction counter
faults only by underflow or an unobserved preceding phase. -/
theorem arrive_fault_none {ι : Type} {log : List (Record ι)} (h : CheckedLog log) {i : Nat}
    {r : Record ι} {s : State} (hi : log[i]? = some r) (hs : stateBefore log i = some s)
    (htx : s.tx = 0) (ha : r.action = .arrive 1 0)
    (hu : r.fault ≠ some .arrivalUnderflow) (hp : r.fault ≠ some .precedingPhaseNotObserved) :
    r.fault = none := by
  have hr := h.at hi
  rw [hs] at hr
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, htx] at hr
  split_ifs at hr <;> simp_all [validCount, validTxOperand, validTx, limit]

end

end PTX.MBarrier
