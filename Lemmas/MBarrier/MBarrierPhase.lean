-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierHistory
public import Mathlib.Data.Nat.Init

@[expose] public section

/-! Phase identity of parity waits. The ISA forbids an arrival in a phase whose
predecessor has not been observed (§9.7.15.16.5.1), so an object cannot run more than
one phase ahead of its successful polls. When successful polls use alternating parity,
parity therefore identifies the actual phase: no kernel shape is assumed. -/

namespace PTX.MBarrier

/-- Number of successful parity polls in a history. -/
def okPolls (log : List (Record ι)) : Nat :=
  (log.filter fun r => r.reply.waited = some true).length

/-- Successful polls strictly before position `j`. -/
def okBefore (log : List (Record ι)) (j : Nat) : Nat := okPolls (log.take j)

/-- The `c`-th successful poll of the object uses parity `c + δ`. -/
def Alternates (log : List (Record ι)) (δ : Nat) : Prop :=
  ∀ j r p ok, log[j]? = some r → r.action = .pollParity p ok →
    r.reply.waited = some true → p % 2 = (okBefore log j + δ) % 2

/-- Executable check of `Alternates` for concrete histories. -/
def alternates (log : List (Record ι)) (δ : Nat) : Bool :=
  (List.range log.length).all fun j =>
    match log[j]? with
    | some r =>
      match r.action, r.reply.waited with
      | .pollParity p _, some true => p % 2 == (okBefore log j + δ) % 2
      | _, _ => true
    | none => true

theorem alternates_sound {log : List (Record ι)} {δ : Nat} (h : alternates log δ = true) :
    Alternates log δ := by
  intro j r p ok hj ha hw
  have hlt : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
  have := List.all_eq_true.mp h j (List.mem_range.mpr hlt)
  simp only [hj, ha, hw, beq_iff_eq] at this
  exact this

/-- Object state bounded by `c` successful polls. -/
def Bounded (s : Option State) (c : Nat) : Prop :=
  ∀ st, s = some st → 0 < st.expected ∧ (st.observed = false → 0 < st.pending) ∧
    st.phase ≤ c + (if st.observed then 0 else 1)

theorem okPolls_append (xs ys : List (Record ι)) :
    okPolls (xs ++ ys) = okPolls xs + okPolls ys := by
  simp [okPolls, List.filter_append]

theorem okPolls_single (r : Record ι) :
    okPolls [r] = if r.reply.waited = some true then 1 else 0 := by
  by_cases h : r.reply.waited = some true <;> simp [okPolls, List.filter, h]

theorem okBefore_succ {log : List (Record ι)} {j : Nat} {r : Record ι}
    (hj : log[j]? = some r) :
    okBefore log (j + 1) = okBefore log j + if r.reply.waited = some true then 1 else 0 := by
  have hlt : j < log.length := by
    by_contra h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hj
  have ht : log.take (j + 1) = log.take j ++ [r] := by
    rw [List.take_add_one, hj]; rfl
  simp only [okBefore, ht, okPolls_append, okPolls_single]

/-- Completion moves into an unobserved phase only from an observed one. -/
private theorem bounded_advance {t : State} {c : Nat} (hb : Bounded (some t) c) :
    Bounded (some (advance t)) c := by
  obtain ⟨he, hpe, hph⟩ := hb t rfl
  intro st hst
  simp only [Option.some.injEq] at hst; subst hst
  unfold advance
  by_cases hc : t.pending = 0 ∧ t.tx = 0
  · rw [ite_eq_left hc]
    have ho : t.observed = true := by
      cases ho : t.observed
      · have := hpe ho; omega
      · rfl
    rw [ho, ite_eq_left rfl] at hph
    exact ⟨he, fun _ => he, by simp; omega⟩
  · rw [ite_eq_right hc]; exact ⟨he, hpe, hph⟩

/-- `perform` with its `Except` steps reduced to nested conditionals. -/
private theorem bounded_perform {s : Option State} {c : Nat} {a : Action} {rep : Reply}
    (hb : Bounded s c) (hp : perform s a = .ok rep) :
    Bounded rep.state (c + if rep.waited = some true then 1 else 0) := by
  intro st hst
  cases s with
  | none =>
    cases a <;> simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hp
    rename_i n
    split_ifs at hp with hv
    simp at hp
    subst hp
    simp only [Option.some.injEq] at hst; subst hst
    exact ⟨hv.1, by simp, by simp⟩
  | some s0 =>
    obtain ⟨he, hpe, hph⟩ := hb s0 rfl
    cases a <;> simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hp
    · -- completeTx
      split_ifs at hp
      simp at hp
      subst hp
      simpa using bounded_advance (t := { s0 with tx := s0.tx - _ }) (c := c)
        (fun _ h => by cases h; exact ⟨he, hpe, hph⟩) st hst
    · -- arrive
      split_ifs at hp with h1 hobs h3 h4
      simp at hp
      subst hp
      simpa using bounded_advance (t := { s0 with pending := s0.pending - _, tx := s0.tx + _ })
        (c := c) (fun _ h => by
          cases h; refine ⟨he, fun h' => by simp_all, ?_⟩; simpa [hobs] using hph) st hst
    · -- increment
      split_ifs at hp with h1
      simp at hp
      subst hp
      simp only [Option.some.injEq] at hst; subst hst
      refine ⟨he, fun _ => Nat.succ_pos _, ?_⟩
      simpa using hph
    · -- pollParity
      subst hp
      simp only [Option.some.injEq] at hst; subst hst
      refine ⟨he, ?_, ?_⟩
      · intro h; simp only [Bool.or_eq_false_iff] at h; exact hpe h.1
      · rename_i p ok
        cases hok : (ok && s0.phase % 2 != p % 2) <;> cases ho : s0.observed <;>
          simp_all
        omega
    · -- inval
      subst hp
      cases hst

/-- A step never invalidates the run-ahead bound. -/
theorem bounded_step {s : Option State} {c : Nat} {r : Record ι} (hb : Bounded s c)
    (hr : RecordOk s r) :
    Bounded r.reply.state (c + if r.reply.waited = some true then 1 else 0) := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [hr.1]; exact bounded_perform hb hp
  · rw [hr.1]; simpa using hb

theorem bounded_history {s t : Option State} {xs : List (Record ι)} {c : Nat}
    (h : RecordedHistory s xs t) (hb : Bounded s c) : Bounded t (c + okPolls xs) := by
  induction h generalizing c with
  | nil => simpa [okPolls] using hb
  | @cons s r rest t hr _ ih =>
    have := ih (bounded_step hb hr)
    have hc : okPolls (r :: rest) = okPolls [r] + okPolls rest := okPolls_append [r] rest
    rw [hc, okPolls_single]
    simpa [Nat.add_assoc] using this

theorem RecordedHistory.split {s t : Option State} {xs ys : List (Record ι)}
    (h : RecordedHistory s (xs ++ ys) t) :
    ∃ m, RecordedHistory s xs m ∧ RecordedHistory m ys t := by
  induction xs generalizing s with
  | nil => exact ⟨s, .nil _, h⟩
  | cons r xs ih =>
    cases h with
    | cons hr hrest =>
      obtain ⟨m, h1, h2⟩ := ih hrest
      exact ⟨m, .cons hr h1, h2⟩

/-- Checked transitions determine the final object state. -/
theorem RecordedHistory.unique {s t t' : Option State} {xs : List (Record ι)}
    (h : RecordedHistory s xs t) (h' : RecordedHistory s xs t') : t = t' := by
  induction h with
  | nil => cases h'; rfl
  | cons _ _ ih => cases h' with | cons _ hrest => exact ih hrest

/-- The prefix before position `j` is a checked history ending in `stateBefore`. -/
theorem CheckedLog.prefix {log : List (Record ι)} (h : CheckedLog log) {j : Nat}
    (hj : j ≤ log.length) : RecordedHistory none (log.take j) (stateBefore log j) := by
  obtain ⟨last, hh⟩ := h.2
  rw [← List.take_append_drop j log] at hh
  obtain ⟨m, hm, -⟩ := hh.split
  cases j with
  | zero => simp at hm ⊢; cases hm; exact .nil _
  | succ j =>
    have hlt : j < log.length := by omega
    have hl : (log.take (j + 1)).getLast? = some log[j] := by
      rw [List.getLast?_eq_getElem?]; simp [Nat.min_eq_left hj]
    rw [hm.last hl] at hm
    simpa [stateBefore, List.getElem?_eq_getElem hlt] using hm

/-- Every reachable object state is within one phase of its successful polls. -/
theorem CheckedLog.bounded {log : List (Record ι)} (h : CheckedLog log) {j : Nat}
    (hj : j ≤ log.length) : Bounded (stateBefore log j) (okBefore log j) := by
  have := bounded_history (h.prefix hj) (c := 0) (fun _ h => by cases h)
  simpa [okBefore] using this

private theorem mono_step {st : State} {r : Record ι} (hr : RecordOk (some st) r)
    (hni : r.action ≠ .inval) :
    ∃ t, r.reply.state = some t ∧ st.phase ≤ t.phase := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [hr.1]
    cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hp
    · split_ifs at hp
      simp at hp; subst hp
      refine ⟨_, rfl, ?_⟩; unfold advance; split_ifs <;> simp
    · split_ifs at hp
      simp at hp; subst hp
      refine ⟨_, rfl, ?_⟩; unfold advance; split_ifs <;> simp
    · split_ifs at hp
      simp at hp; subst hp
      exact ⟨_, rfl, Nat.le_refl _⟩
    · subst hp; exact ⟨_, rfl, Nat.le_refl _⟩
    · exact absurd a hni
  · exact ⟨st, hr.1 ▸ rfl, Nat.le_refl _⟩

theorem RecordedHistory.phase_mono {s t : Option State} {xs : List (Record ι)}
    (h : RecordedHistory s xs t) (hni : NoInval xs) {st : State} (hs : s = some st) :
    ∃ tt, t = some tt ∧ st.phase ≤ tt.phase := by
  induction h generalizing st with
  | nil => exact ⟨st, hs, Nat.le_refl _⟩
  | @cons s0 r rest t0 hr _ ih =>
    subst hs
    obtain ⟨m, hm, hle⟩ := mono_step hr (hni r List.mem_cons_self)
    obtain ⟨tt, ht, hle'⟩ := ih (fun q hq => hni q (List.mem_cons_of_mem _ hq)) hm
    exact ⟨tt, ht, Nat.le_trans hle hle'⟩

/-- Object phases never decrease along a checked history. -/
theorem CheckedLog.phase_mono {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ log.length) {s : State} (hs : stateBefore log i = some s) :
    ∃ t, stateBefore log j = some t ∧ s.phase ≤ t.phase := by
  have hp := h.prefix hj
  rw [← List.take_append_drop i (log.take j)] at hp
  obtain ⟨m, hm, hrest⟩ := hp.split
  rw [List.take_take, Nat.min_eq_left hij] at hm
  rw [hm.unique (h.prefix (Nat.le_trans hij hj)), hs] at hrest
  exact hrest.phase_mono (fun q hq => hni q (List.mem_of_mem_take (List.mem_of_mem_drop hq))) rfl

/-- What a successful poll is: a parity poll that saw the opposite phase parity. -/
theorem CheckedLog.okPoll {log : List (Record ι)} (h : CheckedLog log) {j : Nat}
    {r : Record ι} (hj : log[j]? = some r) (hw : r.reply.waited = some true) :
    ∃ s p, stateBefore log j = some s ∧ r.action = .pollParity p true ∧
      s.phase % 2 ≠ p % 2 ∧
      r.reply.completed = if 0 < s.phase then some (s.phase - 1) else none := by
  have hr := h.at hj
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [hr.1] at hw ⊢
    cases hb : stateBefore log j with
    | none =>
      rw [hb] at hp
      cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      split_ifs at hp
      simp at hp; subst hp; simp at hw
    | some s =>
      rw [hb] at hp
      cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      · split_ifs at hp
        simp at hp; subst hp; simp at hw
      · split_ifs at hp
        simp at hp; subst hp; simp at hw
      · split_ifs at hp
        simp at hp; subst hp; simp at hw
      · rename_i p ok
        subst hp
        simp only [Option.some.injEq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
        obtain ⟨rfl, hne⟩ := hw
        refine ⟨s, p, rfl, rfl, hne, ?_⟩
        simp [hne]
      · subst hp; simp at hw
  · rw [hr.1] at hw; simp at hw

theorem okBefore_zero (log : List (Record ι)) : okBefore log 0 = 0 := by
  simp [okBefore, okPolls]

/-- Locate the successful poll that made the count `c + 1`. -/
theorem previous_okPoll {log : List (Record ι)} {j c : Nat}
    (hc : okBefore log j = c + 1) :
    ∃ i r, i < j ∧ log[i]? = some r ∧ r.reply.waited = some true ∧ okBefore log i = c := by
  induction j with
  | zero => rw [okBefore_zero] at hc; cases hc
  | succ j ih =>
    cases hr : log[j]? with
    | none =>
      have hlen : log.length ≤ j := List.getElem?_eq_none_iff.mp hr
      have : okBefore log (j + 1) = okBefore log j := by
        simp [okBefore, List.take_of_length_le hlen,
          List.take_of_length_le (by omega : log.length ≤ j + 1)]
      obtain ⟨i, q, hi, hq, hw, hb⟩ := ih (this ▸ hc)
      exact ⟨i, q, by omega, hq, hw, hb⟩
    | some r =>
      rw [okBefore_succ hr] at hc
      by_cases hw : r.reply.waited = some true
      · rw [ite_eq_left hw] at hc
        exact ⟨j, r, by omega, hr, hw, by omega⟩
      · rw [ite_eq_right hw] at hc
        obtain ⟨i, q, hi, hq, hw', hb⟩ := ih (by simpa using hc)
        exact ⟨i, q, by omega, hq, hw', hb⟩

/-- Alternating parity identifies phases. If the `c`-th successful poll of an object
uses parity `c + δ`, it runs in phase `c + 1 - δ`: δ = 0 for a wait on a phase to be
completed, δ = 1 for a wait whose first poll passes on the initial phase. -/
theorem CheckedLog.poll_phase {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {δ : Nat}
    (hδ : δ ≤ 1)
    (hpar : Alternates log δ)
    {j : Nat} {r : Record ι} (hj : log[j]? = some r) (hw : r.reply.waited = some true) :
    ∃ s, stateBefore log j = some s ∧ s.phase + δ = okBefore log j + 1 := by
  induction j using Nat.strong_induction_on generalizing r with
  | _ j ih =>
    have hlt : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨s, p, hs, ha, hne, -⟩ := h.okPoll hj hw
    have hp := hpar j r p true hj ha hw
    obtain ⟨-, -, hbound⟩ := h.bounded (Nat.le_of_lt hlt) s hs
    have hb' : s.phase ≤ okBefore log j + 1 := by split_ifs at hbound <;> omega
    refine ⟨s, hs, ?_⟩
    cases hc : okBefore log j with
    | zero => rw [hc] at hp hb'; omega
    | succ c =>
      rw [hc] at hp hb'
      obtain ⟨i, q, hi, hq, hwq, hci⟩ := previous_okPoll hc
      obtain ⟨si, hsi, hpi⟩ := ih i hi hq hwq
      obtain ⟨t, ht, hle⟩ := h.phase_mono hni (Nat.le_of_lt hi) (Nat.le_of_lt hlt) hsi
      rw [hs] at ht; cases ht
      rw [hci] at hpi
      omega

/-- A wait on the `c`-th completion with parity `c` observes exactly completed phase `c`. -/
theorem CheckedLog.poll_observes {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    (hpar : Alternates log 0)
    {j : Nat} {r : Record ι} (hj : log[j]? = some r) (hw : r.reply.waited = some true) :
    observedAt log j = some (okBefore log j) := by
  obtain ⟨s, hs, hph⟩ := h.poll_phase hni (δ := 0) (Nat.zero_le 1) hpar hj hw
  obtain ⟨s', p, hs', -, -, hc⟩ := h.okPoll hj hw
  rw [hs] at hs'; cases hs'
  have hpos : 0 < s.phase := by omega
  simp only [observedAt, hj, Option.bind_some, hc, ite_eq_left hpos]
  congr 1; omega

/-- A non-faulting arrival needs an initialized object whose previous phase was observed. -/
theorem arrive_observed {before : Option State} {r : Record ι} {n tx : Nat}
    (hr : RecordOk before r) (ha : r.action = .arrive n tx) (hf : r.fault = none) :
    ∃ s, before = some s ∧ s.observed = true := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [ha] at hp
    cases before with
    | none => simp [perform, throw, throwThe, MonadExceptOf.throw] at hp
    | some s =>
      simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hp
      split_ifs at hp with h1 h2
      exact ⟨s, rfl, h2⟩
  · rw [hr.2] at hf; cases hf

/-- With alternating parity, an arrival belongs to the phase counted by the successful
polls before it: it can neither precede the observed phase nor run ahead of it. -/
theorem CheckedLog.arrive_phase {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    (hpar : Alternates log 0)
    {i : Nat} {r : Record ι} {n tx : Nat} (hi : log[i]? = some r)
    (ha : r.action = .arrive n tx) (hf : r.fault = none) :
    phaseAt log i = some (okBefore log i) := by
  have hlt : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨s, hs, hobs⟩ := arrive_observed (h.at hi) ha hf
  obtain ⟨-, -, hbound⟩ := h.bounded (Nat.le_of_lt hlt) s hs
  rw [hobs, ite_eq_left rfl] at hbound
  simp only [phaseAt, hs, Option.map_some, Option.some.injEq]
  cases hc : okBefore log i with
  | zero => rw [hc] at hbound; omega
  | succ c =>
    rw [hc] at hbound
    obtain ⟨j, q, hj, hq, hwq, hcj⟩ := previous_okPoll hc
    obtain ⟨sj, hsj, hpj⟩ := h.poll_phase hni (δ := 0) (Nat.zero_le 1) hpar hq hwq
    obtain ⟨t, ht, hle⟩ := h.phase_mono hni (Nat.le_of_lt hj) (Nat.le_of_lt hlt) hsj
    rw [hs] at ht; cases ht
    rw [hcj] at hpj
    omega

/-! Arrival accounting: a phase consumes exactly `expected` arrival units, so the units before
an operation determine its phase. A `cp.async.mbarrier.arrive` without `.noinc` raises the count
its phase must reach by one before its arrive-on lowers it again, so the increments of a history
are counted separately. -/

/-- Arrival units of the non-faulting arrivals in a history. -/
def arrivalUnits : List (Record ι) → Nat
  | [] => 0
  | r :: rest => (match r.action, r.fault with
      | .arrive n _, none => n
      | _, _ => 0) + arrivalUnits rest

def unitsBefore (log : List (Record ι)) (j : Nat) : Nat := arrivalUnits (log.take j)

/-- Pending-count increments of the non-faulting `cp.async.mbarrier.arrive` operations in a
history: each one raises the count its phase must reach by one. -/
def incrementUnits : List (Record ι) → Nat
  | [] => 0
  | r :: rest => (match r.action, r.fault with
      | .increment, none => 1
      | _, _ => 0) + incrementUnits rest

def incrementsBefore (log : List (Record ι)) (j : Nat) : Nat := incrementUnits (log.take j)

/-- Units so far are the completed phases plus the arrivals of the current phase. `incrs` counts
the pending-count increments so far, which raise the pending count a phase must reach. -/
def Accounted (s : Option State) (units incrs : Nat) : Prop :=
  (s = none → units = 0 ∧ incrs = 0) ∧ ∀ st, s = some st →
    st.pending ≤ st.expected + incrs ∧
      units + st.pending = st.expected * (st.phase + 1) + incrs

theorem arrivalUnits_append (xs ys : List (Record ι)) :
    arrivalUnits (xs ++ ys) = arrivalUnits xs + arrivalUnits ys := by
  induction xs with
  | nil => simp [arrivalUnits]
  | cons r xs ih => simp only [List.cons_append, arrivalUnits, ih]; omega

theorem incrementUnits_append (xs ys : List (Record ι)) :
    incrementUnits (xs ++ ys) = incrementUnits xs + incrementUnits ys := by
  induction xs with
  | nil => simp [incrementUnits]
  | cons r xs ih => simp only [List.cons_append, incrementUnits, ih]; omega

private theorem accounted_advance {t : State} {u c : Nat} (hp : t.pending ≤ t.expected + c)
    (hu : u + t.pending = t.expected * (t.phase + 1) + c) :
    (advance t).pending ≤ (advance t).expected + c ∧
      u + (advance t).pending = (advance t).expected * ((advance t).phase + 1) + c := by
  unfold advance
  split_ifs with hc
  · simp only
    rw [hc.1] at hu
    have hm : t.expected * (t.phase + 1 + 1) = t.expected * (t.phase + 1) + t.expected :=
      Nat.mul_succ _ _
    constructor <;> omega
  · exact ⟨hp, hu⟩

theorem accounted_step {s : Option State} {u c : Nat} {r : Record ι} (ha : Accounted s u c)
    (hr : RecordOk s r) (hni : r.action ≠ .inval) :
    Accounted r.reply.state (u + arrivalUnits [r]) (c + incrementUnits [r]) := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    obtain ⟨hrep, hf⟩ := hr
    rw [hrep]
    cases s with
    | none =>
      cases hact : r.action <;> rw [hact] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      split_ifs at hp
      simp at hp; subst hp
      obtain ⟨h0, hc0⟩ := ha.1 rfl
      refine ⟨by simp, fun st hst => ?_⟩
      simp only [Option.some.injEq] at hst; subst hst
      simp [arrivalUnits, incrementUnits, hact, h0, hc0]
    | some s0 =>
      obtain ⟨hp0, hu0⟩ := ha.2 s0 rfl
      cases hact : r.action <;> rw [hact] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      · split_ifs at hp
        simp at hp; subst hp
        refine ⟨by simp, fun st hst => ?_⟩
        simp only [Option.some.injEq] at hst; subst hst
        simpa [arrivalUnits, incrementUnits, hact] using
          accounted_advance (t := { s0 with tx := s0.tx - _ }) hp0 hu0
      · rename_i n tx
        split_ifs at hp with h1 h2 h3
        simp at hp; subst hp
        refine ⟨by simp, fun st hst => ?_⟩
        simp only [Option.some.injEq] at hst; subst hst
        have := accounted_advance (u := u + n) (c := c)
          (t := { s0 with pending := s0.pending - n, tx := s0.tx + tx })
          (by simp only; omega) (by simp only; omega)
        simpa [arrivalUnits, incrementUnits, hact, hf] using this
      · split_ifs at hp
        simp at hp; subst hp
        refine ⟨by simp, fun st hst => ?_⟩
        simp only [Option.some.injEq] at hst; subst hst
        simp only [arrivalUnits, incrementUnits, hact, hf]
        refine ⟨?_, ?_⟩
        · show s0.pending + 1 ≤ s0.expected + (c + 1)
          omega
        · show u + 0 + (s0.pending + 1) = s0.expected * (s0.phase + 1) + (c + 1)
          omega
      · subst hp
        refine ⟨by simp, fun st hst => ?_⟩
        simp only [Option.some.injEq] at hst; subst hst
        simpa [arrivalUnits, incrementUnits, hact] using ⟨hp0, hu0⟩
      · exact absurd hact hni
  · obtain ⟨hrep, hf⟩ := hr
    rw [hrep]
    have h0 : arrivalUnits [r] = 0 := by
      simp only [arrivalUnits, hf]; split <;> simp_all
    have hc0 : incrementUnits [r] = 0 := by
      simp only [incrementUnits, hf]; split <;> simp_all
    simpa [h0, hc0] using ha

theorem accounted_history {s t : Option State} {xs : List (Record ι)} {u c : Nat}
    (h : RecordedHistory s xs t) (hni : NoInval xs) (ha : Accounted s u c) :
    Accounted t (u + arrivalUnits xs) (c + incrementUnits xs) := by
  induction h generalizing u c with
  | nil => simpa [arrivalUnits, incrementUnits] using ha
  | @cons s r rest t hr _ ih =>
    have huc := ih (fun q hq => hni q (List.mem_cons_of_mem _ hq))
      (accounted_step ha hr (hni r List.mem_cons_self))
    have hua : arrivalUnits (r :: rest) = arrivalUnits [r] + arrivalUnits rest :=
      arrivalUnits_append [r] rest
    have hic : incrementUnits (r :: rest) = incrementUnits [r] + incrementUnits rest :=
      incrementUnits_append [r] rest
    rw [hua, hic, ← Nat.add_assoc, ← Nat.add_assoc]
    exact huc

theorem CheckedLog.accounted {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    {j : Nat} (hj : j ≤ log.length) :
    Accounted (stateBefore log j) (unitsBefore log j) (incrementsBefore log j) := by
  have := accounted_history (h.prefix hj) (fun q hq => hni q (List.mem_of_mem_take hq)) (u := 0)
    (c := 0) ⟨fun _ => ⟨rfl, rfl⟩, fun _ h => by cases h⟩
  simpa [unitsBefore, incrementsBefore] using this

/-- A non-faulting full-count arrival starts a phase: the arrival units before it, together with
the pending arrivals above the expected count (`pending - expected`, which a pending-count
increment can create), are the completed phases plus the increments. In a history without
increments the two extra terms are zero, so the `c`-th arrival is in phase `c`. -/
theorem CheckedLog.full_arrival_phase {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {i : Nat} {r : Record ι} {tx : Nat} {s : State} (hi : log[i]? = some r)
    (hs : stateBefore log i = some s) (ha : r.action = .arrive s.expected tx)
    (hf : r.fault = none) :
    unitsBefore log i + (s.pending - s.expected) =
      s.expected * s.phase + incrementsBefore log i := by
  have hlt : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hp, hu⟩ := (h.accounted hni (Nat.le_of_lt hlt)).2 s hs
  have hr := h.at hi
  rw [hs] at hr
  unfold RecordOk at hr
  split at hr
  · rename_i rep hper
    rw [ha] at hper
    simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hper
    split_ifs at hper with h1 h2 h3
    rw [Nat.mul_succ] at hu
    omega
  · rw [hr.2] at hf; cases hf

end PTX.MBarrier
