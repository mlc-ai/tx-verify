-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierTransactions
public import Lemmas.Protocol.MbarPending
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! # Phases of a unit-transaction barrier

A proof tool. A barrier is an object of expected count one whose non-faulting arrivals are unit
arrivals expecting `T` bytes and whose non-faulting completions complete `T` bytes (`UnitTx`).
Read from its checked history only: its phase is at most its completions so far
(`phase_le_completed`), since a phase advance leaves a zero transaction counter, so the
completed bytes equal the expected ones; and every completed phase holds a non-faulting
completion (`completion_in_phase`), since the phase's transaction updates cancel and its arrival
expects bytes.

Beside it: records of a kind before a position counted by their identities
(`countP_take_le_card`), when a record that passes every check of its object does not fault
(`RecordOk.arrive_fault_none`, `RecordOk.arrive_fault`, `RecordOk.complete_fault_none`), and the
arrival units of unit arrivals bounded by one thread's arrivals (`arrivalUnits_le_countP`). -/

namespace PTX.MBarrier

section
variable {ι : Type}

/-- A history of expected count one whose non-faulting arrivals are unit arrivals expecting `T`
bytes and whose non-faulting completions complete `T` bytes. -/
structure UnitTx (log : List (Record ι)) (T : Nat) : Prop where
  arrive : ∀ r ∈ log, r.fault = none → ∀ c tx, r.action = .arrive c tx → c = 1 ∧ tx = T
  complete : ∀ r ∈ log, r.fault = none → ∀ n, r.action = .completeTx n → n = T
  expected : ∀ k st, stateBefore log k = some st → st.expected = 1

theorem expectedTxBytes_unit {T : Nat} {xs : List (Record ι)}
    (h : ∀ r ∈ xs, r.fault = none → ∀ c tx, r.action = .arrive c tx → c = 1 ∧ tx = T) :
    expectedTxBytes xs = T * arrivalUnits xs := by
  induction xs with
  | nil => simp [expectedTxBytes, arrivalUnits]
  | cons r xs ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [expectedTxBytes, arrivalUnits, ih, Record.expectedTxBytes]
    cases ha : r.action <;> cases hf : r.fault <;> simp
    case arrive.none c tx =>
      obtain ⟨rfl, rfl⟩ := h r List.mem_cons_self hf c tx ha
      rw [Nat.mul_add, Nat.mul_one]

theorem UnitTx.expected_bytes {log : List (Record ι)} {T : Nat} (hu : UnitTx log T) (j : Nat) :
    expectedTxBytes (log.take j) = T * unitsBefore log j :=
  expectedTxBytes_unit fun r hr => hu.arrive r (List.mem_of_mem_take hr)

theorem UnitTx.completed_bytes {log : List (Record ι)} {T : Nat} (hu : UnitTx log T) (j : Nat) :
    completedTxBytes (log.take j) = T * completedTxCount (log.take j) :=
  completedTxBytes_eq_unit_mul_count fun r hr hf n ha =>
    hu.complete r (List.mem_of_mem_take hr) hf n ha

/-- The units before a position: the completed phases, plus the current phase's arrival when it
is in. -/
theorem UnitTx.units {log : List (Record ι)} {T : Nat} (hu : UnitTx log T) (h : CheckedLog log)
    (hni : NoInval log)
    {j : Nat} (hj : j ≤ log.length) {st : State} (hs : stateBefore log j = some st) :
    st.pending ≤ 1 + incrementsBefore log j ∧
      unitsBefore log j + st.pending = st.phase + 1 + incrementsBefore log j := by
  obtain ⟨hp, hu'⟩ := (h.accounted hni hj).2 st hs
  rw [hu.expected j st hs] at hp hu'
  rw [Nat.one_mul] at hu'
  omega

/-- The transaction counter is the expected bytes of the units less the completed bytes. -/
theorem UnitTx.tx {log : List (Record ι)} {T : Nat} (hu : UnitTx log T) (h : CheckedLog log)
    (hni : NoInval log)
    {j : Nat} (hj : j ≤ log.length) {st : State} (hs : stateBefore log j = some st) :
    st.tx = (T * unitsBefore log j : Nat) - (T * completedTxCount (log.take j) : Nat) := by
  rw [h.tx_balance hni hj hs, hu.expected_bytes, hu.completed_bytes]

/-- **The phase is at most the completions so far.** The latest phase advance left a zero
transaction counter, so its completed bytes are its expected bytes, of at least one unit per
completed phase. -/
theorem UnitTx.phase_le_completed {log : List (Record ι)} {T : Nat} (hu : UnitTx log T)
    (hT : 0 < T) (h : CheckedLog log) (hni : NoInval log) {j : Nat}
        (hj : j ≤ log.length) {st : State}
    (hs : stateBefore log j = some st) : st.phase ≤ completedTxCount (log.take j) := by
  rcases Nat.eq_zero_or_pos st.phase with h0 | hpos
  · omega
  obtain ⟨q, hq, s, s', hsq, hsc, hs', hsc'⟩ := h.crossing hni hj hs (c := st.phase - 1) (by omega)
  have hql : q < log.length := by omega
  obtain ⟨r, hr⟩ : ∃ r, log[q]? = some r := ⟨_, List.getElem?_eq_getElem hql⟩
  have hb := h.phase_advance_transaction_bytes hni hr hsq hs' (by omega)
  rw [hu.expected_bytes, hu.completed_bytes] at hb
  have hcu := Nat.eq_of_mul_eq_mul_left hT hb
  obtain ⟨hpen, hun⟩ := hu.units h hni (show q + 1 ≤ log.length by omega) hs'
  have hmono : completedTxCount (log.take (q + 1)) ≤ completedTxCount (log.take j) := by
    unfold completedTxCount
    exact (List.take_sublist_take_left (by omega)).countP_le
  omega

/-- **A completed phase holds a non-faulting completion.** The phase's transaction updates cancel
at its completion, and it has an arrival unit, which expects bytes; only a completion takes
them back. -/
theorem UnitTx.completion_in_phase {log : List (Record ι)} {T : Nat} (hu : UnitTx log T)
    (hT : 0 < T) (h : CheckedLog log) (hni : NoInval log) {j : Nat}
        (hj : j ≤ log.length) {st : State}
    (hs : stateBefore log j = some st) {q : Nat} (hq : q < st.phase) :
    ∃ k r n, k < j ∧ log[k]? = some r ∧ r.fault = none ∧ r.action = .completeTx n ∧
      phaseAt log k = some q := by
  classical
  obtain ⟨b, hbj, hc⟩ := h.crossing hni hj hs hq
  have hbl : b < log.length := by omega
  obtain ⟨hz, hpos⟩ := h.completion_sums hni hbl hc
  by_contra hno
  push Not at hno
  have hterm : ∀ k ∈ Finset.range (b + 1),
      ((T : Int) * (if phaseAt log k = some q then unitsAt log k else 0 : Nat)) ≤
        (if phaseAt log k = some q then txDeltaAt log k else 0) := by
    intro k hk
    have hkb := Finset.mem_range.mp hk
    split_ifs with hp
    · unfold unitsAt txDeltaAt
      cases hr : log[k]? with
      | none => simp
      | some r =>
        simp only
        by_cases hf : r.fault = none
        · simp only [hf, ↓reduceIte, Record.txDelta]
          cases ha : r.action with
          | arrive c tx =>
            obtain ⟨rfl, rfl⟩ := hu.arrive r (List.mem_of_getElem? hr) hf c tx ha
            simp [Action.units, Action.txDelta]
          | completeTx n => exact absurd hp (hno k r n (by omega) hr hf ha)
          | init n => simp [Action.units, Action.txDelta]
          | pollParity p ok => simp [Action.units, Action.txDelta]
          | increment => simp [Action.units, Action.txDelta]
          | inval => simp [Action.units, Action.txDelta]
        · simp [hf, Record.txDelta]
    · simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hu' : ((phaseUnits log (b + 1) q : Nat) : Int) =
      ∑ k ∈ Finset.range (b + 1),
        ((if phaseAt log k = some q then unitsAt log k else 0 : Nat) : Int) := by
    simp only [phaseUnits, Nat.cast_sum]
  have htx : phaseTx log (b + 1) q =
      ∑ k ∈ Finset.range (b + 1), (if phaseAt log k = some q then txDeltaAt log k else 0) := rfl
  rw [← htx, hz] at hsum
  have : (0 : Int) < (T : Int) * (phaseUnits log (b + 1) q : Nat) := by
    have : 0 < T * phaseUnits log (b + 1) q := Nat.mul_pos hT hpos
    exact_mod_cast this
  rw [hu'] at this
  exact absurd hsum (not_le.mpr this)

/-- Counting the records of a kind before a position by their identities. -/
theorem countP_take_le_card [DecidableEq ι] {log : List (Record ι)}
    (hnd : (log.map Record.id).Nodup) (p : Record ι → Bool) {i : Nat} (I : Finset ι)
    (hids : ∀ k < i, ∀ r, log[k]? = some r → p r = true → r.id ∈ I) :
    (log.take i).countP p ≤ I.card := by
  have hnd' : (((log.take i).filter p).map Record.id).Nodup :=
    (hnd.sublist ((List.take_sublist i log).map Record.id)).sublist
      ((List.filter_sublist (p := p) (l := log.take i)).map Record.id)
  rw [List.countP_eq_length_filter, ← List.length_map Record.id, ← List.toFinset_card_of_nodup hnd']
  refine Finset.card_le_card (fun x hx => ?_)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨hrt, hpr⟩ := List.mem_filter.mp hr
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrt
  have hki : k < (log.take i).length := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.getElem?_take_of_lt (by simp at hki; omega)] at hk
  exact hids k (by simp at hki; omega) r hk hpr

/-- An arrival that passes every check of its object does not fault. -/
theorem RecordOk.arrive_fault_none {st : State} {r : Record ι} (hr : RecordOk (some st) r)
    {n tx : Nat} (ha : r.action = .arrive n tx) (hn : validCount n) (htx : validTxOperand tx)
    (hobs : st.observed = true) (hp : n ≤ st.pending) (hv : validTx (st.tx + tx)) :
    r.fault = none := by
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, hobs] at hr
  split_ifs at hr <;> first | exact hr.2 | (exfalso; omega)

/-- An arrival in range that neither underflows nor arrives in an unobserved phase does not
fault. -/
theorem RecordOk.arrive_fault {st : State} {r : Record ι} (hr : RecordOk (some st) r)
    {n tx : Nat} (ha : r.action = .arrive n tx) (hn : validCount n) (htx : validTxOperand tx)
    (hv : validTx (st.tx + tx)) (h1 : r.fault ≠ some .arrivalUnderflow)
    (h2 : r.fault ≠ some .precedingPhaseNotObserved) : r.fault = none := by
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hr
  split_ifs at hr <;> simp_all

/-- A completion that passes every check of its object does not fault. -/
theorem RecordOk.complete_fault_none {st : State} {r : Record ι} (hr : RecordOk (some st) r)
    {n : Nat} (ha : r.action = .completeTx n) (hn : validTxOperand n)
    (hv : validTx (st.tx - n)) : r.fault = none := by
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hr
  split_ifs at hr
  exact hr.2

/-- With unit arrivals, the arrival units of a history are at most its arrivals of one thread,
when every non-faulting arrival is that thread's. -/
theorem arrivalUnits_le_countP {xs : List (Record ι)} (p : Record ι → Bool)
    (h : ∀ r ∈ xs, r.fault = none → ∀ c tx, r.action = .arrive c tx → c = 1 ∧ p r = true) :
    arrivalUnits xs ≤ xs.countP p := by
  induction xs with
  | nil => simp [arrivalUnits]
  | cons r xs ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [arrivalUnits, List.countP_cons]
    cases ha : r.action <;> cases hf : r.fault <;> simp only <;> try omega
    case arrive.none c tx =>
      obtain ⟨rfl, hp⟩ := h r List.mem_cons_self hf c tx ha
      simp [hp]
      omega

end

end PTX.MBarrier
