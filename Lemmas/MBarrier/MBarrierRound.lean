-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierPhase
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-! Transaction accounting per phase, and the round identity of transaction updates.
An object's transaction counter is the signed sum of the current phase's updates. Hence,
when every update carries a round label and each round's notifications total at most its
expected bytes, each `complete_tx` belongs to its own round's phase. No kernel shape is
assumed: rounds, sizes and the order premises are explicit. -/

namespace PTX.MBarrier
open Finset

/-- Signed transaction effect of an action: expected bytes add, completions subtract. -/
def Action.txDelta : Action → Int
  | .arrive _ tx => tx
  | .completeTx n => -(n : Int)
  | _ => 0

/-- A faulting record has no effect. -/
def Record.txDelta (r : Record ι) : Int := if r.fault = none then r.action.txDelta else 0

def txDeltaAt (log : List (Record ι)) (k : Nat) : Int :=
  match log[k]? with
  | some r => r.txDelta
  | none => 0

/-- Signed transaction updates of phase `p` before position `j`. -/
def phaseTx (log : List (Record ι)) (j p : Nat) : Int :=
  ∑ k ∈ range j, if phaseAt log k = some p then txDeltaAt log k else 0

/-- A successful object step either stays in its phase, adding its transaction effect,
or completes the phase with a zero counter. -/
theorem perform_some_tx {s : State} {a : Action} {rep : Reply}
    (hp : perform (some s) a = .ok rep) (hni : a ≠ .inval) :
    ∃ st, rep.state = some st ∧
      ((st.phase = s.phase ∧ st.tx = s.tx + a.txDelta) ∨
       (st.phase = s.phase + 1 ∧ st.tx = 0 ∧ s.tx + a.txDelta = 0)) := by
  have adv : ∀ t : State, t.phase = s.phase →
      ((advance t).phase = s.phase ∧ (advance t).tx = t.tx) ∨
      ((advance t).phase = s.phase + 1 ∧ (advance t).tx = 0 ∧ t.tx = 0) := by
    intro t ht
    unfold advance
    split_ifs with hc
    · exact .inr ⟨by simp [ht], by simp [hc.2], hc.2⟩
    · exact .inl ⟨ht, rfl⟩
  cases a <;> simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hp
  · split_ifs at hp
    simp at hp; subst hp
    refine ⟨_, rfl, ?_⟩
    rcases adv { s with tx := s.tx - _ } rfl with h | h
    · exact .inl ⟨h.1, by rw [h.2]; simp [Action.txDelta]; omega⟩
    · exact .inr ⟨h.1, h.2.1, by have := h.2.2; simp [Action.txDelta] at this ⊢; omega⟩
  · split_ifs at hp
    simp at hp; subst hp
    refine ⟨_, rfl, ?_⟩
    rcases adv { s with pending := s.pending - _, tx := s.tx + _ } rfl with h | h
    · exact .inl ⟨h.1, by rw [h.2]; simp [Action.txDelta]⟩
    · exact .inr ⟨h.1, h.2.1, by have := h.2.2; simpa [Action.txDelta] using this⟩
  · split_ifs at hp
    simp at hp; subst hp
    exact ⟨_, rfl, .inl ⟨rfl, by simp [Action.txDelta]⟩⟩
  · subst hp
    exact ⟨_, rfl, .inl ⟨rfl, by simp [Action.txDelta]⟩⟩
  · exact absurd rfl hni

theorem CheckedLog.none_before {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {j k : Nat}
    (hj : j ≤ log.length) (hkj : k ≤ j) (hn : stateBefore log j = none) :
    stateBefore log k = none := by
  cases hs : stateBefore log k with
  | none => rfl
  | some s =>
    obtain ⟨t, ht, -⟩ := h.phase_mono hni hkj hj hs
    rw [hn] at ht; cases ht

theorem CheckedLog.phaseAt_le {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {j k p : Nat}
    {s : State} (hj : j ≤ log.length) (hkj : k ≤ j) (hs : stateBefore log j = some s)
    (hk : phaseAt log k = some p) : p ≤ s.phase := by
  cases hsk : stateBefore log k with
  | none => simp [phaseAt, hsk] at hk
  | some sk =>
    simp only [phaseAt, hsk, Option.map_some, Option.some.injEq] at hk
    obtain ⟨t, ht, hle⟩ := h.phase_mono hni hkj hj hsk
    rw [hs] at ht; cases ht; omega

theorem stateBefore_succ {log : List (Record ι)} {j : Nat} {r : Record ι}
    (hj : log[j]? = some r) : stateBefore log (j + 1) = r.reply.state := by
  simp [stateBefore, hj]

/-- The transaction counter is the signed sum of the current phase's updates. -/
theorem CheckedLog.tx_eq {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log) :
    ∀ {j : Nat} {s : State}, j ≤ log.length → stateBefore log j = some s →
      s.tx = phaseTx log j s.phase := by
  intro j
  induction j with
  | zero => intro s _ hs; simp [stateBefore] at hs
  | succ j ih =>
    intro st hj hst
    have hlt : j < log.length := by omega
    obtain ⟨r, hr⟩ : ∃ r, log[j]? = some r := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [stateBefore_succ hr] at hst
    have hsum : ∀ p, phaseTx log (j + 1) p = phaseTx log j p +
        (if phaseAt log j = some p then r.txDelta else 0) := by
      intro p; simp [phaseTx, sum_range_succ, txDeltaAt, hr]
    have hok := h.at hr
    unfold RecordOk at hok
    cases hb : stateBefore log j with
    | none =>
      have hnone : ∀ k < j, phaseAt log k = none := fun k hk => by
        simp [phaseAt, h.none_before hni hlt.le hk.le hb]
      have h0 : ∀ p, phaseTx log j p = 0 := fun p =>
        sum_eq_zero fun k hk => by simp [hnone k (mem_range.mp hk)]
      have hpj : phaseAt log j = none := by simp [phaseAt, hb]
      rw [hb] at hok
      split at hok
      · rename_i rep hp
        rw [hok.1] at hst
        cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
          Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
        split_ifs at hp
        simp at hp; subst hp
        simp only [Option.some.injEq] at hst; subst hst
        simp [hsum, h0, hpj]
      · rw [hok.1] at hst; cases hst
    | some s =>
      have hs := ih hlt.le hb
      have hpj : phaseAt log j = some s.phase := by simp [phaseAt, hb]
      rw [hb] at hok
      split at hok
      · rename_i rep hp
        rw [hok.1] at hst
        have hd : r.txDelta = r.action.txDelta := by simp [Record.txDelta, hok.2]
        obtain ⟨t, ht, hcase⟩ := perform_some_tx hp (hni r (List.mem_of_getElem? hr))
        rw [ht] at hst; cases hst
        rcases hcase with ⟨hph, htx⟩ | ⟨hph, htx, hz⟩
        · rw [hsum, hph, ite_eq_left hpj, htx, hs, hd]
        · rw [hsum, hph, htx, ite_eq_right (by rw [hpj]; simp)]
          symm
          rw [add_zero]
          apply sum_eq_zero
          intro k hk
          rw [ite_eq_right]
          intro hpk
          have := h.phaseAt_le hni hlt.le (mem_range.mp hk).le hb hpk
          omega
      · rw [hok.1] at hst; cases hst
        have hd : r.txDelta = 0 := by simp [Record.txDelta, hok.2]
        rw [hsum, ite_eq_left hpj, hd, hs]; simp

/-- Arrival units of an action. -/
def Action.units : Action → Nat
  | .arrive n _ => n
  | _ => 0

/-- Pending-count increments of an action: `cp.async.mbarrier.arrive` without `.noinc` raises the
pending count by one before its arrive-on lowers it again. -/
def Action.increments : Action → Nat
  | .increment => 1
  | _ => 0

def unitsAt (log : List (Record ι)) (k : Nat) : Nat :=
  match log[k]? with
  | some r => if r.fault = none then r.action.units else 0
  | none => 0

def incrementsAt (log : List (Record ι)) (k : Nat) : Nat :=
  match log[k]? with
  | some r => if r.fault = none then r.action.increments else 0
  | none => 0

/-- Arrival units of phase `p` before position `j`. -/
def phaseUnits (log : List (Record ι)) (j p : Nat) : Nat :=
  ∑ k ∈ range j, if phaseAt log k = some p then unitsAt log k else 0

/-- Pending-count increments of phase `p` before position `j`. -/
def phaseIncrements (log : List (Record ι)) (j p : Nat) : Nat :=
  ∑ k ∈ range j, if phaseAt log k = some p then incrementsAt log k else 0

/-- A history with no increment record has no pending-count increment in any phase. -/
theorem phaseIncrements_eq_zero {log : List (Record ι)} (h : ∀ r ∈ log, r.action ≠ .increment)
    (j p : Nat) : phaseIncrements log j p = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs
  · unfold incrementsAt
    cases hk : log[k]? with
    | none => rfl
    | some r =>
      have hr := h r (List.mem_of_getElem? hk)
      simp only
      split_ifs
      · cases ha : r.action <;> simp_all [Action.increments]
      · rfl
  · rfl

/-- Pending arrivals, the phase's arrival units and its pending-count increments are
complementary: an increment raises the count the phase must reach. -/
theorem perform_some_pending {s : State} {a : Action} {rep : Reply}
    (hp : perform (some s) a = .ok rep) (hni : a ≠ .inval) :
    ∃ st, rep.state = some st ∧ st.expected = s.expected ∧
      ((st.phase = s.phase ∧ st.pending + a.units = s.pending + a.increments) ∨
       (st.phase = s.phase + 1 ∧ st.pending = s.expected ∧
         a.units = s.pending + a.increments ∧ s.tx + a.txDelta = 0)) := by
  cases a <;> simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hp
  · split_ifs at hp
    simp at hp; subst hp
    refine ⟨_, rfl, ?_⟩
    unfold advance
    split_ifs with hc
    · simp only at hc
      exact ⟨rfl, .inr ⟨rfl, rfl, by simp [Action.units, Action.increments, hc.1], by
        simp [Action.txDelta]; omega⟩⟩
    · exact ⟨rfl, .inl ⟨rfl, by simp [Action.units, Action.increments]⟩⟩
  · rename_i n tx
    split_ifs at hp with h1 h2 h3
    simp at hp; subst hp
    refine ⟨_, rfl, ?_⟩
    unfold advance
    split_ifs with hc
    · simp only at hc
      exact ⟨rfl, .inr ⟨rfl, rfl, by simp [Action.units, Action.increments]; omega, by
        simpa [Action.txDelta] using hc.2⟩⟩
    · exact ⟨rfl, .inl ⟨rfl, by simp [Action.units, Action.increments]; omega⟩⟩
  · split_ifs at hp
    simp at hp; subst hp
    exact ⟨_, rfl, rfl, .inl ⟨rfl, by simp [Action.units, Action.increments]⟩⟩
  · subst hp
    exact ⟨_, rfl, rfl, .inl ⟨rfl, by simp [Action.units, Action.increments]⟩⟩
  · exact absurd rfl hni

/-- The pending count plus the phase's arrival units is its expected count plus the
pending-count increments of the phase: a phase consumes one arrival unit per pending arrival, and
each increment of `cp.async.mbarrier.arrive` raises the count the phase must reach. -/
theorem CheckedLog.pending_eq {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log) :
    ∀ {j : Nat} {s : State}, j ≤ log.length → stateBefore log j = some s →
      s.pending + phaseUnits log j s.phase = s.expected + phaseIncrements log j s.phase := by
  intro j
  induction j with
  | zero => intro s _ hs; simp [stateBefore] at hs
  | succ j ih =>
    intro st hj hst
    have hlt : j < log.length := by omega
    obtain ⟨r, hr⟩ : ∃ r, log[j]? = some r := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [stateBefore_succ hr] at hst
    have hsum : ∀ p, phaseUnits log (j + 1) p = phaseUnits log j p +
        (if phaseAt log j = some p then unitsAt log j else 0) := by
      intro p; simp [phaseUnits, sum_range_succ, unitsAt, hr]
    have hsumI : ∀ p, phaseIncrements log (j + 1) p = phaseIncrements log j p +
        (if phaseAt log j = some p then incrementsAt log j else 0) := by
      intro p; simp [phaseIncrements, sum_range_succ, incrementsAt, hr]
    have hok := h.at hr
    unfold RecordOk at hok
    cases hb : stateBefore log j with
    | none =>
      have hnone : ∀ k < j, phaseAt log k = none := fun k hk => by
        simp [phaseAt, h.none_before hni hlt.le hk.le hb]
      have h0 : ∀ p, phaseUnits log j p = 0 := fun p =>
        sum_eq_zero fun k hk => by simp [hnone k (mem_range.mp hk)]
      have h0I : ∀ p, phaseIncrements log j p = 0 := fun p =>
        sum_eq_zero fun k hk => by simp [hnone k (mem_range.mp hk)]
      have hpj : phaseAt log j = none := by simp [phaseAt, hb]
      rw [hb] at hok
      split at hok
      · rename_i rep hp
        rw [hok.1] at hst
        cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
          Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
        split_ifs at hp
        simp at hp; subst hp
        simp only [Option.some.injEq] at hst; subst hst
        simp [hsum, hsumI, h0, h0I, hpj]
      · rw [hok.1] at hst; cases hst
    | some s =>
      have hs := ih hlt.le hb
      have hpj : phaseAt log j = some s.phase := by simp [phaseAt, hb]
      rw [hb] at hok
      split at hok
      · rename_i rep hp
        rw [hok.1] at hst
        obtain ⟨t, ht, hexp, hcase⟩ := perform_some_pending hp (hni r (List.mem_of_getElem? hr))
        rw [ht] at hst; cases hst
        have hua : unitsAt log j = r.action.units := by simp [unitsAt, hr, hok.2]
        have hia : incrementsAt log j = r.action.increments := by
          simp [incrementsAt, hr, hok.2]
        rcases hcase with ⟨hph, hpe⟩ | ⟨hph, hpe, hu, -⟩
        · have hsp : phaseUnits log (j + 1) st.phase =
              phaseUnits log j s.phase + r.action.units := by
            rw [hsum, hph, hua]
            simp [hpj]
          have hsi : phaseIncrements log (j + 1) st.phase =
              phaseIncrements log j s.phase + r.action.increments := by
            rw [hsumI, hph, hia]
            simp [hpj]
          rw [hsp, hsi, hexp]
          omega
        · have h1 : phaseUnits log j (s.phase + 1) = 0 := by
            apply sum_eq_zero
            intro k hk
            rw [ite_eq_right]
            intro hpk
            have := h.phaseAt_le hni hlt.le (mem_range.mp hk).le hb hpk
            omega
          have h2 : phaseIncrements log j (s.phase + 1) = 0 := by
            apply sum_eq_zero
            intro k hk
            rw [ite_eq_right]
            intro hpk
            have := h.phaseAt_le hni hlt.le (mem_range.mp hk).le hb hpk
            omega
          have hsp : phaseUnits log (j + 1) (s.phase + 1) = 0 := by
            rw [hsum, h1]
            simp [hpj]
          have hsi : phaseIncrements log (j + 1) (s.phase + 1) = 0 := by
            rw [hsumI, h2]
            simp [hpj]
          rw [hph, hsp, hsi, hpe, hexp]
      · rw [hok.1] at hst; cases hst
        have hz : unitsAt log j = 0 := by simp [unitsAt, hr, hok.2]
        have hzI : incrementsAt log j = 0 := by simp [incrementsAt, hr, hok.2]
        rw [hsum, hsumI, hz, hzI]
        simpa [hpj] using hs

/-- Position `q` completes phase `c`. -/
def Completes (log : List (Record ι)) (q c : Nat) : Prop :=
  ∃ s s', stateBefore log q = some s ∧ s.phase = c ∧
    stateBefore log (q + 1) = some s' ∧ s'.phase = c + 1

/-- Phases increase one at a time: reaching beyond `c` passes a completion of `c`. -/
theorem CheckedLog.crossing {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {c : Nat} :
    ∀ {b : Nat} {t : State}, b ≤ log.length → stateBefore log b = some t → c < t.phase →
      ∃ q < b, Completes log q c := by
  intro b
  induction b with
  | zero => intro t _ ht; simp [stateBefore] at ht
  | succ b ih =>
    intro t hb ht hc
    have hlt : b < log.length := by omega
    obtain ⟨r, hr⟩ : ∃ r, log[b]? = some r := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hok := h.at hr
    have ht' := ht
    rw [stateBefore_succ hr] at ht'
    unfold RecordOk at hok
    cases hsb : stateBefore log b with
    | none =>
      rw [hsb] at hok
      split at hok
      · rename_i rep hp
        rw [hok.1] at ht'
        cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
          Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
        split_ifs at hp
        simp at hp; subst hp
        simp only [Option.some.injEq] at ht'; subst ht'
        simp at hc
      · rw [hok.1] at ht'; cases ht'
    | some s =>
      by_cases hs : c < s.phase
      · obtain ⟨q, hq, hcq⟩ := ih hlt.le hsb hs
        exact ⟨q, by omega, hcq⟩
      · rw [hsb] at hok
        split at hok
        · rename_i rep hp
          rw [hok.1] at ht'
          obtain ⟨st, hst, -, hcase⟩ := perform_some_pending hp (hni r (List.mem_of_getElem? hr))
          rw [hst] at ht'; cases ht'
          rcases hcase with ⟨hph, -⟩ | ⟨hph, -⟩
          · omega
          · exact ⟨b, by omega, s, t, hsb, by omega, ht, by omega⟩
        · rw [hok.1] at ht'; cases ht'; omega

/-- At a completion the phase's transaction updates cancel and its arrivals are complete. -/
theorem CheckedLog.completion_sums {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {q c : Nat}
    (hq : q < log.length) (hc : Completes log q c) :
    phaseTx log (q + 1) c = 0 ∧ 0 < phaseUnits log (q + 1) c := by
  obtain ⟨s, s', hs, hsc, hs', hsc'⟩ := hc
  obtain ⟨r, hr⟩ : ∃ r, log[q]? = some r := ⟨_, List.getElem?_eq_getElem hq⟩
  have hpq : phaseAt log q = some c := by simp [phaseAt, hs, hsc]
  have htx := h.tx_eq hni hq.le hs
  have hpe := h.pending_eq hni hq.le hs
  obtain ⟨he, -, -⟩ := h.bounded hq.le s hs
  have hok := h.at hr
  rw [hs] at hok
  rw [stateBefore_succ hr] at hs'
  unfold RecordOk at hok
  split at hok
  · rename_i rep hp
    rw [hok.1] at hs'
    obtain ⟨t, ht, -, hcase⟩ := perform_some_pending hp (hni r (List.mem_of_getElem? hr))
    rw [ht] at hs'; cases hs'
    rcases hcase with ⟨hph, -⟩ | ⟨-, -, hu, hz⟩
    · omega
    · have hd : r.txDelta = r.action.txDelta := by simp [Record.txDelta, hok.2]
      have h1 : phaseTx log (q + 1) c = phaseTx log q c + r.txDelta := by
        simp [phaseTx, sum_range_succ, txDeltaAt, hr, hpq]
      have h2 : phaseUnits log (q + 1) c = phaseUnits log q c + r.action.units := by
        simp [phaseUnits, sum_range_succ, unitsAt, hr, hpq, hok.2]
      subst hsc
      refine ⟨by rw [h1, ← htx, hd, hz], by rw [h2]; omega⟩
  · rw [hok.1] at hs'; cases hs'; omega

/-- A non-faulting operation other than `init` acts on an initialized object. -/
theorem CheckedLog.initialized {log : List (Record ι)} (h : CheckedLog log) {k : Nat}
    {r : Record ι} (hk : log[k]? = some r) (hf : r.fault = none)
    (hi : ∀ n, r.action ≠ .init n) : ∃ s, stateBefore log k = some s := by
  have hok := h.at hk
  cases hs : stateBefore log k with
  | some s => exact ⟨s, rfl⟩
  | none =>
    rw [hs] at hok
    unfold RecordOk at hok
    split at hok
    · rename_i rep hp
      cases a : r.action with
      | init n => exact (hi n a).elim
      | _ => rw [a] at hp; simp [perform, throw, throwThe, MonadExceptOf.throw] at hp
    · rw [hok.2] at hf; cases hf

/-- Bytes notified by non-faulting `complete_tx` operations of round `c` at position `k`. -/
def completeBytesAt (log : List (Record ι)) (round : ι → Nat) (c k : Nat) : Int :=
  match log[k]? with
  | some r =>
    if r.fault = none ∧ round r.id = c then
      match r.action with
      | .completeTx n => n
      | _ => 0
    else 0
  | none => 0

/-- All bytes notified for round `c` in the history. -/
def roundBytes (log : List (Record ι)) (round : ι → Nat) (c : Nat) : Int :=
  ∑ k ∈ range log.length, completeBytesAt log round c k

theorem completeBytesAt_nonneg (log : List (Record ι)) (round : ι → Nat) (c k : Nat) :
    0 ≤ completeBytesAt log round c k := by
  unfold completeBytesAt
  split
  · split
    · split <;> omega
    · exact le_refl _
  · exact le_refl _

section
variable {log : List (Record ι)} (round : ι → Nat)

/-- Round labels of the updates. Round `c ≥ 1` notifications follow the `(c-1)`-th
successful poll: the consumer has released the slot of the previous round. -/
def NotifiesAfterRelease (log : List (Record ι)) : Prop :=
  ∀ k r n, log[k]? = some r → r.action = .completeTx n → r.fault = none → 0 < round r.id →
    ∃ j q, j < k ∧ log[j]? = some q ∧ q.reply.waited = some true ∧
      okBefore log j + 1 = round r.id

/-- Each arrival is in its round's phase and expects that round's bytes. -/
def ArrivalsInRound (log : List (Record ι)) (T : Nat → Nat) : Prop :=
  ∀ k r n tx, log[k]? = some r → r.action = .arrive n tx → r.fault = none →
    phaseAt log k = some (round r.id) ∧ tx = T (round r.id)

/-- A notification cannot precede the phase of its round. -/
theorem CheckedLog.round_lower (h : CheckedLog log) (hni : NoInval log) (hpar : Alternates log 0)
    (hafter : NotifiesAfterRelease round log) {k : Nat} {r : Record ι} {n : Nat}
    (hk : log[k]? = some r) (ha : r.action = .completeTx n) (hf : r.fault = none) :
    ∃ s, stateBefore log k = some s ∧ round r.id ≤ s.phase := by
  obtain ⟨s, hs⟩ := h.initialized hk hf (by intro m; rw [ha]; simp)
  refine ⟨s, hs, ?_⟩
  rcases Nat.eq_zero_or_pos (round r.id) with h0 | hpos
  · omega
  obtain ⟨j, q, hjk, hq, hw, hcnt⟩ := hafter k r n hk ha hf hpos
  have hklt : k < log.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨sj, hsj, hph⟩ := h.poll_phase hni (Nat.zero_le 1) hpar hq hw
  obtain ⟨t, ht, hle⟩ := h.phase_mono hni hjk.le hklt.le hsj
  rw [hs] at ht; cases ht
  omega

/-- Round identity of transaction notifications. If each round's arrival expects that
round's bytes, its notifications total at most those bytes, and notifications follow
the release of the previous round, then every `complete_tx` lands in its round's phase:
it can neither complete an earlier phase nor be left for a later one. -/
theorem CheckedLog.complete_round (h : CheckedLog log) (hni : NoInval log) (T : Nat → Nat)
    (hpar : Alternates log 0) (harr : ArrivalsInRound round log T)
    (hafter : NotifiesAfterRelease round log)
    (hpos : ∀ (k : Nat) (r : Record ι) (n : Nat), log[k]? = some r → r.action = .completeTx n →
      r.fault = none → 0 < n)
    (hbytes : ∀ c, roundBytes log round c ≤ T c) :
    ∀ c k r n, log[k]? = some r → r.action = .completeTx n → r.fault = none →
      round r.id = c → phaseAt log k = some c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro k r n hk ha hf hc
  obtain ⟨s, hs, hlow⟩ := h.round_lower round hni hpar hafter hk ha hf
  rw [hc] at hlow
  suffices hsc : s.phase = c by simp [phaseAt, hs, hsc]
  refine Classical.byContradiction fun hne => ?_
  have hgt : c < s.phase := by omega
  have hklt : k < log.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨q, hqk, hcomp⟩ := h.crossing hni hklt.le hs hgt
  have hqlt : q < log.length := by omega
  obtain ⟨htx0, hunits⟩ := h.completion_sums hni hqlt hcomp
  -- An arrival of this phase exists before the completion.
  obtain ⟨a, haq, hane⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show phaseUnits log (q + 1) c ≠ 0
    by omega)
  have hpa : phaseAt log a = some c := by by_contra hp; simp [hp] at hane
  obtain ⟨ra, hra⟩ : ∃ ra, log[a]? = some ra := by
    cases hl : log[a]? with
    | none => simp [hpa, unitsAt, hl] at hane
    | some ra => exact ⟨ra, rfl⟩
  have hfa : ra.fault = none := by
    by_contra hfa; simp [hpa, unitsAt, hra, hfa] at hane
  obtain ⟨na, txa, haa⟩ : ∃ na txa, ra.action = .arrive na txa := by
    cases hact : ra.action with
    | arrive na txa => exact ⟨na, txa, rfl⟩
    | _ => simp [hpa, unitsAt, hra, hfa, hact, Action.units] at hane
  obtain ⟨hpra, htxa⟩ := harr a ra na txa hra haa hfa
  have hrc : round ra.id = c := by rw [hpa] at hpra; exact (Option.some.inj hpra).symm
  -- Termwise: the phase's net updates plus the round's notifications cover its arrival.
  have term : ∀ k' ∈ range (q + 1),
      (if k' = a then (T c : Int) else 0) ≤
        (if phaseAt log k' = some c then txDeltaAt log k' else 0) +
          completeBytesAt log round c k' := by
    intro k' _
    have hcb := completeBytesAt_nonneg log round c k'
    by_cases hka : k' = a
    · subst hka
      simp only [ite_true, hpa, txDeltaAt, hra, Record.txDelta, hfa, haa, Action.txDelta,
        completeBytesAt, hrc, and_self, ite_true]
      rw [htxa, hrc]; simp
    rw [ite_eq_right hka]
    by_cases hp : phaseAt log k' = some c
    · rw [ite_eq_left hp]
      cases hl : log[k']? with
      | none => simpa [txDeltaAt, hl] using hcb
      | some r' =>
        by_cases hf' : r'.fault = none
        · cases hact : r'.action with
          | arrive n' tx' =>
            obtain ⟨hp', htx'⟩ := harr k' r' n' tx' hl hact hf'
            have : txDeltaAt log k' = tx' := by simp [txDeltaAt, hl, Record.txDelta, hf', hact,
              Action.txDelta]
            omega
          | completeTx n' =>
            have hr' : round r'.id = c := by
              rcases lt_trichotomy (round r'.id) c with hlt | heq | hgt'
              · have := ih _ hlt k' r' n' hl hact hf' rfl
                rw [hp] at this; cases this; omega
              · exact heq
              · obtain ⟨s', hs', hle'⟩ := h.round_lower round hni hpar hafter hl hact hf'
                simp [phaseAt, hs'] at hp; omega
            simp [txDeltaAt, completeBytesAt, hl, Record.txDelta, hf', hact, Action.txDelta, hr']
          | init n' => simp [txDeltaAt, hl, Record.txDelta, hf', hact, Action.txDelta]; omega
          | increment =>
            simp [txDeltaAt, hl, Record.txDelta, hf', hact, Action.txDelta]; omega
          | pollParity p' ok' =>
            simp [txDeltaAt, hl, Record.txDelta, hf', hact, Action.txDelta]; omega
          | inval => simp [txDeltaAt, hl, Record.txDelta, hf', hact, Action.txDelta]; omega
        · simp [txDeltaAt, hl, Record.txDelta, hf']; omega
    · rw [ite_eq_right hp]; omega
  have hsum := Finset.sum_le_sum term
  rw [Finset.sum_ite_eq' (range (q + 1)) a, ite_eq_left haq, Finset.sum_add_distrib] at hsum
  change (T c : Int) ≤ phaseTx log (q + 1) c + _ at hsum
  rw [htx0, zero_add] at hsum
  -- The notification at `k` comes after the completion, so the round over-notifies.
  have hkn : completeBytesAt log round c k = n := by
    simp [completeBytesAt, hk, hf, hc, ha]
  have hsub : insert k (range (q + 1)) ⊆ range log.length := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact mem_range.mpr hklt
    · exact mem_range.mpr (by have := mem_range.mp hx; omega)
  have hnot : k ∉ range (q + 1) := by simp; omega
  have htot := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => completeBytesAt_nonneg log round c x)
  rw [Finset.sum_insert hnot, hkn] at htot
  have hb := hbytes c
  have hn := hpos k r n hk ha hf
  unfold roundBytes at hb
  omega

end

end PTX.MBarrier
