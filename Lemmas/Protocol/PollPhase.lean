-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierAddress
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! # Phases of one mbarrier object from its own history

A proof tool. Every statement reads one object's checked history only.

Polls. A selected poller (one thread, say) whose successful polls alternate parity
(`SelectedAlternates … δ`) sees strictly increasing phases (`selected_phase_lt`) and observes
strictly increasing completed phases (`selected_observed_lt`); its successful poll with `c`
earlier selected successes finds a state of phase at least `c + 1 - δ`, of the parity of
`c + 1 + δ` (`selected_poll_phase_ge`). No gate is assumed: in particular not that a phase is
observed before the next phase's arrivals (OBJ-MBAR-STATE reports that as a fault, so it
cannot be assumed while fault freedom is being proved). With a budget excluding two
unobserved phases, `phase + δ ≤ c + 2`, the phase is exactly `c + 1 - δ`
(`selected_poll_phase_eq`), and the poll observes the completed phase `c - δ`; the budget holds when
the arrival units before the poll are fewer than `expected · (c + 2 - δ)`
(`selected_poll_phase_of_units`).

Unit arrivals. When every non-faulting arrival has count one and the object's expected count
is `n`, a non-faulting arrival lies in the phase numbered by the arrivals before it divided by
`n`, up to the pending-count increments before it (`unit_arrival_phase`: the phase's upper bound
is `expected · (phase + 1)` plus those increments, since an increment raises the pending count
with no arrival); in a history where no increment widens that bound, every completed phase holds
exactly `n` of them (`card_unit_arrivals_phase`), and the units before a position are at most the
number of identities their records can have (`unitsBefore_le_card`).

Faults. Only a phase completion clears the observed flag (`RecordOk.observed_step`), so a
state is observed when a successful poll found its phase earlier (`observed_of_poll`). A unit
arrival with fewer than `expected · (s + 1)` units before it, and a successful poll finding
each phase `1, …, s` before it, neither underflows nor arrives in an unobserved phase
(`arrive_fault_free`). -/

namespace PTX.MBarrier

variable {ι : Type}

/-- Gate-free lower bound: a selected poller with alternating parity sees, at its successful
poll with `c` earlier selected successes, a phase of at least `c + 1 - δ`, of the parity of
`c + 1 + δ`. -/
theorem CheckedLog.selected_poll_phase_ge {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    (selected : ι → Bool) {δ : Nat} (hδ : δ ≤ 1) (hpar : SelectedAlternates selected log δ)
    {j : Nat} {r : Record ι} (hj : log[j]? = some r) (hselected : selected r.id = true)
    (hw : r.reply.waited = some true) :
    ∃ st, stateBefore log j = some st ∧ selectedBefore selected log j + 1 ≤ st.phase + δ ∧
      st.phase % 2 = (selectedBefore selected log j + 1 + δ) % 2 := by
  induction j using Nat.strong_induction_on generalizing r with
  | _ j ih =>
    have hlt : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨st, p, hs, ha, hne, -⟩ := h.okPoll hj hw
    have hp := hpar j r p true hj ha hselected hw
    have hparity : st.phase % 2 = (selectedBefore selected log j + 1 + δ) % 2 := by omega
    refine ⟨st, hs, ?_, hparity⟩
    cases hc : selectedBefore selected log j with
    | zero => rw [hc] at hparity; omega
    | succ c =>
      rw [hc] at hparity
      obtain ⟨i, q, hi, hq, hsq, hwq, hci⟩ := previous_selected_success selected hc
      obtain ⟨sti, hsi, hge, hpi⟩ := ih i hi hq hsq hwq
      obtain ⟨stj, hstj, hle⟩ := h.phase_mono hni (Nat.le_of_lt hi) (Nat.le_of_lt hlt) hsi
      rw [hs] at hstj
      cases hstj
      rw [hci] at hge hpi
      omega

/-- With a budget excluding two unobserved phases, the selected poll's phase is exact. -/
theorem CheckedLog.selected_poll_phase_eq {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    (selected : ι → Bool) {δ : Nat} (hδ : δ ≤ 1) (hpar : SelectedAlternates selected log δ)
    {j : Nat} {r : Record ι} (hj : log[j]? = some r) (hselected : selected r.id = true)
    (hw : r.reply.waited = some true)
    (hbudget :
      ∀ st, stateBefore log j = some st → st.phase + δ ≤ selectedBefore selected log j + 2) :
    ∃ st, stateBefore log j = some st ∧ st.phase + δ = selectedBefore selected log j + 1 := by
  obtain ⟨st, hs, hge, hpar'⟩ := h.selected_poll_phase_ge hni selected hδ hpar hj hselected hw
  have hb := hbudget st hs
  exact ⟨st, hs, by omega⟩

theorem selectedBefore_mono (selected : ι → Bool) (log : List (Record ι)) {i j : Nat}
    (hij : i ≤ j) : selectedBefore selected log i ≤ selectedBefore selected log j := by
  induction j with
  | zero => simp at hij; subst hij; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · cases hk : log[j]? with
      | none =>
        have hlen : log.length ≤ j := List.getElem?_eq_none_iff.mp hk
        have : selectedBefore selected log (j + 1) = selectedBefore selected log j := by
          simp [selectedBefore, List.take_of_length_le hlen,
            List.take_of_length_le (by omega : log.length ≤ j + 1)]
        rw [this]; exact ih (by omega)
      | some r => rw [selectedBefore_succ selected hk]; have := ih (by omega); omega
    · rw [heq]

/-- A selected success counts for every later position. -/
theorem selectedBefore_lt_of_success (selected : ι → Bool) {log : List (Record ι)} {i j : Nat}
    {r : Record ι} (hij : i < j) (hi : log[i]? = some r) (hs : selected r.id = true)
    (hw : r.reply.waited = some true) :
    selectedBefore selected log i + 1 ≤ selectedBefore selected log j := by
  have h := selectedBefore_succ selected hi
  rw [observerIncrement_success selected r hs hw] at h
  have := selectedBefore_mono selected log (by omega : i + 1 ≤ j)
  omega

/-- The phase found by a selected successful poll has the parity of its selected count. -/
theorem CheckedLog.selected_parity {log : List (Record ι)} (h : CheckedLog log)
    (selected : ι → Bool) {δ : Nat} (hpar : SelectedAlternates selected log δ)
    {j : Nat} {r : Record ι} (hj : log[j]? = some r) (hselected : selected r.id = true)
    (hw : r.reply.waited = some true) :
    ∃ st, stateBefore log j = some st ∧
      st.phase % 2 = (selectedBefore selected log j + 1 + δ) % 2 := by
  obtain ⟨st, p, hs, ha, hne, -⟩ := h.okPoll hj hw
  have hp := hpar j r p true hj ha hselected hw
  exact ⟨st, hs, by omega⟩

/-- Gate-free: the selected successful polls of an alternating poller find strictly increasing
phases. -/
theorem CheckedLog.selected_phase_lt {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    (selected : ι → Bool) {δ : Nat} (hpar : SelectedAlternates selected log δ)
    {i j : Nat} {ri rj : Record ι} (hij : i < j) (hi : log[i]? = some ri)
    (hsi : selected ri.id = true) (hwi : ri.reply.waited = some true)
    (hj : log[j]? = some rj) (hsj : selected rj.id = true) (hwj : rj.reply.waited = some true) :
    ∃ si sj, stateBefore log i = some si ∧ stateBefore log j = some sj ∧ si.phase < sj.phase := by
  induction j using Nat.strong_induction_on generalizing i ri rj with
  | _ j ih =>
    have hjlt : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
    have hcij := selectedBefore_lt_of_success selected hij hi hsi hwi
    obtain ⟨c, hc⟩ : ∃ c, selectedBefore selected log j = c + 1 :=
      ⟨selectedBefore selected log j - 1, by omega⟩
    obtain ⟨k, rk, hk, hkr, hsk, hwk, hck⟩ := previous_selected_success selected hc
    obtain ⟨sj, hsj', hpj⟩ := h.selected_parity selected hpar hj hsj hwj
    obtain ⟨sk, hsk', hpk⟩ := h.selected_parity selected hpar hkr hsk hwk
    obtain ⟨sj2, hsj2, hle⟩ := h.phase_mono hni (Nat.le_of_lt hk) (Nat.le_of_lt hjlt) hsk'
    rw [hsj'] at hsj2
    cases hsj2
    have hkj : sk.phase < sj.phase := by
      rcases Nat.lt_or_eq_of_le hle with h' | h'
      · exact h'
      · rw [hck] at hpk; omega
    rcases Nat.lt_trichotomy i k with hik | rfl | hki
    · obtain ⟨si, sk', hsi', hsk2, hlt⟩ := ih k hk hik hi hsi hwi hkr hsk hwk
      rw [hsk'] at hsk2
      cases hsk2
      exact ⟨si, sj, hsi', hsj', Nat.lt_trans hlt hkj⟩
    · rw [hi] at hkr
      cases hkr
      exact ⟨sk, sj, hsk', hsj', hkj⟩
    · have := selectedBefore_lt_of_success selected hki hkr hsk hwk
      have := selectedBefore_mono selected log (Nat.le_of_lt hij)
      have := selectedBefore_lt_of_success selected hij hi hsi hwi
      omega

/-- Gate-free: the selected successful polls of an alternating poller observe strictly
increasing completed phases. -/
theorem CheckedLog.selected_observed_lt {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    (selected : ι → Bool) {δ : Nat} (hpar : SelectedAlternates selected log δ)
    {i j qi qj : Nat} {ri rj : Record ι} (hij : i < j) (hi : log[i]? = some ri)
    (hsi : selected ri.id = true) (hwi : ri.reply.waited = some true)
    (hj : log[j]? = some rj) (hsj : selected rj.id = true) (hwj : rj.reply.waited = some true)
    (hoi : observedAt log i = some qi) (hoj : observedAt log j = some qj) : qi < qj := by
  obtain ⟨si, sj, hsi', hsj', hlt⟩ := h.selected_phase_lt
      hni selected hpar hij hi hsi hwi hj hsj hwj
  obtain ⟨si2, -, hsi2, -, -, hci⟩ := h.okPoll hi hwi
  obtain ⟨sj2, -, hsj2, -, -, hcj⟩ := h.okPoll hj hwj
  rw [hsi'] at hsi2; cases hsi2
  rw [hsj'] at hsj2; cases hsj2
  simp only [observedAt, hi, hj, Option.bind_some] at hoi hoj
  rw [hci] at hoi
  rw [hcj] at hoj
  split_ifs at hoi hoj
  simp_all
  omega

/-- The phase at a selected poll is exact when the arrival units before it leave no room for
two completed phases beyond the selected count: `units < expected · (c + 2 - δ)`. -/
theorem CheckedLog.selected_poll_phase_of_units {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    (selected : ι → Bool) {δ : Nat} (hδ : δ ≤ 1) (hpar : SelectedAlternates selected log δ)
    {j : Nat} {r : Record ι} (hj : log[j]? = some r) (hselected : selected r.id = true)
    (hw : r.reply.waited = some true)
    (hunits : ∀ st, stateBefore log j = some st →
      unitsBefore log j < st.expected * (selectedBefore selected log j + 2 - δ)) :
    ∃ st, stateBefore log j = some st ∧ st.phase + δ = selectedBefore selected log j + 1 := by
  have hlt : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
  refine h.selected_poll_phase_eq hni selected hδ hpar hj hselected hw (fun st hs => ?_)
  obtain ⟨hp, hu⟩ := (h.accounted hni (Nat.le_of_lt hlt)).2 st hs
  have hb := hunits st hs
  have hle : st.expected * st.phase < st.expected * (selectedBefore selected log j + 2 - δ) := by
    rw [Nat.mul_succ] at hu; omega
  have := Nat.lt_of_mul_lt_mul_left hle
  omega

/-- Whether a record is a non-faulting arrival. -/
def countedArrive (r : Record ι) : Bool :=
  match r.action, r.fault with
  | .arrive _ _, none => true
  | _, _ => false

theorem countedArrive_iff {r : Record ι} :
    countedArrive r = true ↔ r.fault = none ∧ ∃ c tx, r.action = .arrive c tx := by
  unfold countedArrive
  cases ha : r.action <;> cases hf : r.fault <;> simp

/-- With unit arrivals, the arrival units of a history are its non-faulting arrivals. -/
theorem arrivalUnits_eq_length {xs : List (Record ι)}
    (hunit : ∀ r ∈ xs, ∀ c tx, r.fault = none → r.action = .arrive c tx → c = 1) :
    arrivalUnits xs = (xs.filter countedArrive).length := by
  induction xs with
  | nil => simp [arrivalUnits]
  | cons r xs ih =>
    rw [arrivalUnits, ih (fun r' hr' => hunit r' (List.mem_cons_of_mem _ hr')), List.filter_cons]
    cases ha : r.action with
    | arrive c tx =>
      cases hf : r.fault with
      | none =>
        have := hunit r List.mem_cons_self c tx hf ha
        subst this
        simp [countedArrive, ha, hf]; omega
      | some e => simp [countedArrive, ha, hf]
    | _ => simp [countedArrive, ha]

/-- Counting the arrival units before a position by the identities of their records. -/
theorem CheckedLog.unitsBefore_le_card [DecidableEq ι] {log : List (Record ι)}
    (h : CheckedLog log) {i : Nat} (I : Finset ι)
    (hunit : ∀ (k : Nat) (r : Record ι) (c tx : Nat), log[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1)
    (hids : ∀ k < i, ∀ (r : Record ι) (c tx : Nat), log[k]? = some r → r.fault = none →
      r.action = .arrive c tx → r.id ∈ I) :
    unitsBefore log i ≤ I.card := by
  have hmem : ∀ r ∈ log.take i, ∃ k < i, log[k]? = some r := by
    intro r hr
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hki : k < (log.take i).length := (List.getElem?_eq_some_iff.mp hk).1
    refine ⟨k, by simp at hki; omega, ?_⟩
    rw [List.getElem?_take_of_lt (by simp at hki; omega)] at hk
    exact hk
  rw [unitsBefore, arrivalUnits_eq_length (fun r hr c tx hf ha => by
    obtain ⟨k, -, hk⟩ := hmem r hr; exact hunit k r c tx hk hf ha)]
  have hnd : (((log.take i).filter countedArrive).map Record.id).Nodup :=
    (h.1.sublist ((List.take_sublist i log).map Record.id)).sublist
      ((List.filter_sublist (p := countedArrive) (l := log.take i)).map Record.id)
  rw [← List.length_map Record.id, ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card (fun x hx => ?_)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨hrt, hpr⟩ := List.mem_filter.mp hr
  obtain ⟨k, hk, hkr⟩ := hmem r hrt
  obtain ⟨hf, c, tx, ha⟩ := countedArrive_iff.mp hpr
  exact hids k hk r c tx hkr hf ha

/-- A successful poll leaves its phase observed. -/
theorem RecordOk.poll_observed {before : Option State} {r : Record ι} (hr : RecordOk before r)
    (hw : r.reply.waited = some true) :
    ∃ s t, before = some s ∧ r.reply.state = some t ∧ t.phase = s.phase ∧ t.observed = true := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [hr.1] at hw ⊢
    cases before with
    | none =>
      cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      split_ifs at hp
      simp at hp; subst hp; simp at hw
    | some s =>
      cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      · split_ifs at hp
        simp at hp; subst hp; simp at hw
      · split_ifs at hp
        simp at hp; subst hp; simp at hw
      · split_ifs at hp
        simp at hp; subst hp; simp at hw
      · subst hp
        simp only [Option.some.injEq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
        exact ⟨s, _, rfl, rfl, rfl, by simp [hw.1, hw.2]⟩
      · subst hp; simp at hw
  · rw [hr.1] at hw; simp at hw

/-- Only a phase completion clears the observed flag: a step that leaves the phase unchanged
keeps an observed phase observed, and the initial state is observed. -/
theorem RecordOk.observed_step {before : Option State} {r : Record ι} {t : State}
    (hr : RecordOk before r) (ht : r.reply.state = some t) (hto : t.observed = false) :
    ∃ s, before = some s ∧ (s.phase < t.phase ∨ (s.phase = t.phase ∧ s.observed = false)) := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [hr.1] at ht
    cases before with
    | none =>
      cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      split_ifs at hp
      simp at hp; subst hp
      simp at ht; subst ht; simp at hto
    | some s =>
      refine ⟨s, rfl, ?_⟩
      cases a : r.action <;> rw [a] at hp <;> simp [perform, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at hp
      · split_ifs at hp
        simp at hp; subst hp
        simp only [Option.some.injEq] at ht; subst ht
        unfold advance at hto ⊢
        split_ifs at hto ⊢ <;> simp_all
      · split_ifs at hp
        simp at hp; subst hp
        simp only [Option.some.injEq] at ht; subst ht
        unfold advance at hto ⊢
        split_ifs at hto ⊢ <;> simp_all
      · split_ifs at hp
        simp at hp; subst hp
        simp only [Option.some.injEq] at ht; subst ht
        exact Or.inr ⟨by simp, by simpa using hto⟩
      · subst hp
        simp only [Option.some.injEq] at ht; subst ht
        simp only [Bool.or_eq_false_iff] at hto
        exact .inr ⟨rfl, hto.1⟩
      · subst hp; cases ht
  · rw [hr.1] at ht
    cases before with
    | none => cases ht
    | some s =>
      cases ht
      exact ⟨t, rfl, .inr ⟨rfl, hto⟩⟩

/-- A state is observed when a successful poll found the same phase earlier, or when its phase
is the initial one. -/
theorem CheckedLog.observed_of_poll {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    {m : Nat} {sm : State} (hm : stateBefore log m = some sm)
    (hpoll : sm.phase = 0 ∨ ∃ k w sk, k < m ∧ log[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore log k = some sk ∧ sk.phase = sm.phase) :
    sm.observed = true := by
  induction m generalizing sm with
  | zero => simp [stateBefore] at hm
  | succ m ih =>
    by_contra hno
    have hno' : sm.observed = false := by simpa using hno
    obtain ⟨r, hr⟩ : ∃ r, log[m]? = some r := by
      cases hr : log[m]? with
      | none => simp [stateBefore, hr] at hm
      | some r => exact ⟨r, rfl⟩
    have hrs : r.reply.state = some sm := by simpa [stateBefore, hr] using hm
    have hok := h.at hr
    obtain ⟨s, hs, hcase⟩ := hok.observed_step hrs hno'
    have hmlen : m < log.length := (List.getElem?_eq_some_iff.mp hr).1
    rcases hpoll with h0 | ⟨k, w, sk, hk, hw, hww, hsk, hph⟩
    · rcases hcase with hlt | ⟨heq, hso⟩
      · omega
      · exact absurd (ih hs (.inl (heq.trans h0))) (by simp [hso])
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkm | rfl
      · obtain ⟨s2, hs2, hle⟩ := h.phase_mono hni (Nat.le_of_lt hkm) (Nat.le_of_lt hmlen) hsk
        rw [hs] at hs2; cases hs2
        rcases hcase with hlt | ⟨heq, hso⟩
        · omega
        · exact absurd (ih hs (.inr ⟨k, w, sk, hkm, hw, hww, hsk, hph.trans heq.symm⟩))
            (by simp [hso])
      · rw [hr] at hw; cases hw
        obtain ⟨s', t, hs', ht, -, hto⟩ := hok.poll_observed hww
        rw [hrs] at ht; cases ht
        simp [hto] at hno'

/-- Fault freedom of one unit arrival. Its record at position `i` belongs, by its use `s`, to
phase `s` at most: the arrival units before it are fewer than `expected · (s + 1)`, and for
every `1 ≤ q ≤ s` a successful poll before it found phase `q`. Then the arrival neither
underflows the pending count nor arrives in a phase whose predecessor was not observed. -/
theorem CheckedLog.arrive_fault_free {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {i : Nat}
    {r : Record ι} {tx s : Nat} (hi : log[i]? = some r) (ha : r.action = .arrive 1 tx)
    (hunits : ∀ st, stateBefore log i = some st → unitsBefore log i < st.expected * (s + 1))
    (hpolls : ∀ q, 1 ≤ q → q ≤ s → ∃ k w sk, k < i ∧ log[k]? = some w ∧
      w.reply.waited = some true ∧ stateBefore log k = some sk ∧ sk.phase = q) :
    r.fault ≠ some .arrivalUnderflow ∧ r.fault ≠ some .precedingPhaseNotObserved := by
  have hlt : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  have hr := h.at hi
  cases hst : stateBefore log i with
  | none =>
    rw [hst] at hr
    unfold RecordOk at hr
    rw [ha] at hr
    simp [perform, throw, throwThe, MonadExceptOf.throw] at hr
    rw [hr.2]
    simp
  | some st =>
    rw [hst] at hr
    obtain ⟨hp, hu⟩ := (h.accounted hni (Nat.le_of_lt hlt)).2 st hst
    have hb := hunits st hst
    have hph : st.phase < s + 1 := by
      have : st.expected * st.phase < st.expected * (s + 1) := by
        rw [Nat.mul_succ] at hu; omega
      exact Nat.lt_of_mul_lt_mul_left this
    have hobs : st.observed = true := by
      refine h.observed_of_poll hni hst ?_
      rcases Nat.eq_zero_or_pos st.phase with h0 | hpos
      · exact .inl h0
      · obtain ⟨k, w, sk, hk, hw, hww, hsk, hq⟩ := hpolls st.phase hpos (by omega)
        exact .inr ⟨k, w, sk, hk, hw, hww, hsk, hq⟩
    unfold RecordOk at hr
    rw [ha] at hr
    simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, hobs] at hr
    split_ifs at hr with h1 h2 h3
    · simp at hr
      rw [hr.2]
      simp
    · simp at hr
      rw [hr.2]
      simp
    · -- the pending count is exhausted: the phase is complete in arrivals
      have hp0 : st.pending = 0 := by omega
      rw [hp0, Nat.add_zero] at hu
      have : st.expected * (st.phase + 1) < st.expected * (s + 1) := by omega
      have hq := Nat.lt_of_mul_lt_mul_left this
      obtain ⟨k, w, sk, hk, hw, hww, hsk, hq'⟩ := hpolls (st.phase + 1) (by omega) (by omega)
      obtain ⟨s2, hs2, hle⟩ := h.phase_mono hni (Nat.le_of_lt hk) (Nat.le_of_lt hlt) hsk
      rw [hst] at hs2; cases hs2
      omega
    · simp at hr
      rw [hr.2]
      simp

/-- A non-faulting arrival of count `c` finds at least `c` pending arrivals. -/
theorem RecordOk.arrive_pending {s : State} {r : Record ι} {c tx : Nat}
    (hr : RecordOk (some s) r) (ha : r.action = .arrive c tx) (hf : r.fault = none) :
    c ≤ s.pending := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hper
    rw [ha] at hper
    simp [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hper
    split_ifs at hper with h1 h2 h3
    exact h3
  · rw [hr.2] at hf; cases hf

theorem unitsBefore_succ (log : List (Record ι)) {k : Nat} {r : Record ι} (hk : log[k]? = some r) :
    unitsBefore log (k + 1) = unitsBefore log k + arrivalUnits [r] := by
  simp only [unitsBefore, List.take_add_one, hk, Option.toList_some, arrivalUnits_append]

theorem unitsBefore_mono (log : List (Record ι)) {i j : Nat} (hij : i ≤ j) :
    unitsBefore log i ≤ unitsBefore log j := by
  induction j with
  | zero => simp at hij; subst hij; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · cases hk : log[j]? with
      | none =>
        have hlen : log.length ≤ j := List.getElem?_eq_none_iff.mp hk
        have : unitsBefore log (j + 1) = unitsBefore log j := by
          simp [unitsBefore, List.take_of_length_le hlen,
            List.take_of_length_le (by omega : log.length ≤ j + 1)]
        rw [this]; exact ih (by omega)
      | some r => rw [unitsBefore_succ log hk]; have := ih (by omega); omega
    · rw [heq]

/-- A history with no increment record counts no pending-count increment. -/
theorem incrementsBefore_length_of (log : List (Record ι))
    (h : ∀ r ∈ log, r.action ≠ .increment) : incrementsBefore log log.length = 0 := by
  simp only [incrementsBefore, List.take_length]
  induction log with
  | nil => rfl
  | cons r rest ih =>
    have hr := h r List.mem_cons_self
    simp only [incrementUnits, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    split <;> simp_all

/-- A history without pending-count increments has none before any position. -/
theorem incrementsBefore_eq_zero (log : List (Record ι))
    (hinc : incrementsBefore log log.length = 0) (k : Nat) : incrementsBefore log k = 0 := by
  have h := incrementUnits_append (log.take k) (log.drop k)
  rw [List.take_append_drop] at h
  simp only [incrementsBefore, List.take_length] at hinc ⊢
  omega

/-- A non-faulting unit arrival lies in the phase numbered by the arrival units before it
divided by the expected count, up to the pending-count increments before it: an increment raises
the count its phase must reach by one without an arrival, so the phase's upper bound is the
expected count plus those increments. -/
theorem CheckedLog.unit_arrival_phase {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {i : Nat}
    {r : Record ι} {tx : Nat} {s : State} (hi : log[i]? = some r)
    (hs : stateBefore log i = some s) (ha : r.action = .arrive 1 tx) (hf : r.fault = none) :
    s.expected * s.phase ≤ unitsBefore log i ∧
      unitsBefore log i + 1 ≤ s.expected * (s.phase + 1) + incrementsBefore log i := by
  have hlt : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hp, hu⟩ := (h.accounted hni (Nat.le_of_lt hlt)).2 s hs
  have hr := h.at hi
  rw [hs] at hr
  have := hr.arrive_pending ha hf
  rw [Nat.mul_succ] at hu ⊢
  omega

/-- Whether position `i` of the log is a non-faulting unit arrival in phase `q`. -/
def UnitArrivalIn (log : List (Record ι)) (q i : Nat) : Prop :=
  ∃ r tx, log[i]? = some r ∧ r.action = .arrive 1 tx ∧ r.fault = none ∧ phaseAt log i = some q

open Classical in
/-- Every completed phase holds exactly `n` non-faulting unit arrivals, when every
non-faulting arrival has count one, the expected count is `n`, and no pending-count increment
raises the count a phase must reach (`unit_arrival_phase`'s upper bound is `incrementsBefore`
wider in general). -/
theorem CheckedLog.card_unit_arrivals_phase {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    {n q : Nat}
    (hunit : ∀ (i : Nat) (r : Record ι) (c tx : Nat),
      log[i]? = some r → r.fault = none → r.action = .arrive c tx → c = 1)
    (hexp : ∀ i s, i ≤ log.length → stateBefore log i = some s → s.expected = n)
    (hinc : incrementsBefore log log.length = 0)
    {j : Nat} (hj : j ≤ log.length) {s : State} (hs : stateBefore log j = some s)
    (hq : q < s.phase) :
    ((Finset.range log.length).filter (fun i => UnitArrivalIn log q i)).card = n := by
  classical
  -- the count below `k` is the units of phase `q` reached by position `k`
  have key : ∀ k ≤ log.length, ((Finset.range k).filter (fun i => UnitArrivalIn log q i)).card =
      min n (unitsBefore log k - n * q) := by
    intro k hk
    induction k with
    | zero => simp [unitsBefore, arrivalUnits]
    | succ k ih =>
      have hkl : k < log.length := by omega
      obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := ⟨_, List.getElem?_eq_getElem hkl⟩
      rw [Finset.range_add_one, Finset.filter_insert, unitsBefore_succ log hr]
      have ih := ih (by omega)
      by_cases hua : ∃ tx, r.action = .arrive 1 tx ∧ r.fault = none
      · obtain ⟨tx, ha, hf⟩ := hua
        have hunits : arrivalUnits [r] = 1 := by simp [arrivalUnits, ha, hf]
        rw [hunits]
        obtain ⟨st, hst⟩ : ∃ st, stateBefore log k = some st := by
          cases hsk : stateBefore log k with
          | some st => exact ⟨st, rfl⟩
          | none =>
            have hrk := h.at hr
            rw [hsk] at hrk
            unfold RecordOk at hrk
            simp only [perform, ha] at hrk
            split at hrk <;> simp_all
        have hexpk := hexp k st (by omega) hst
        obtain ⟨hlo, hhi⟩ := h.unit_arrival_phase hni hr hst ha hf
        rw [incrementsBefore_eq_zero log hinc k] at hhi
        replace hhi : unitsBefore log k < st.expected * (st.phase + 1) := by omega
        rw [hexpk] at hlo hhi
        by_cases hph : st.phase = q
        · have hin : UnitArrivalIn log q k := ⟨r, tx, hr, ha, hf, by simp [phaseAt, hst, hph]⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true hin), Finset.card_insert_of_notMem (by simp), ih]
          subst hph
          rw [Nat.mul_succ] at hhi
          omega
        · have hnin : ¬ UnitArrivalIn log q k := by
            rintro ⟨r', tx', hr', -, -, hp⟩
            simp [phaseAt, hst] at hp
            exact hph hp
          rw [ite_eq_right_of_eq_false _ _ (eq_false hnin), ih]
          rcases Nat.lt_or_gt_of_ne hph with hlt | hgt
          · have : n * (st.phase + 1) ≤ n * q := Nat.mul_le_mul_left n hlt
            rw [Nat.mul_succ] at hhi this
            omega
          · have : n * (q + 1) ≤ n * st.phase := Nat.mul_le_mul_left n hgt
            rw [Nat.mul_succ] at this
            omega
      · have hunits : arrivalUnits [r] = 0 := by
          cases ha : r.action with
          | arrive c tx =>
            cases hf : r.fault with
            | none =>
              have := hunit k r c tx hr hf ha
              subst this
              exact absurd ⟨tx, ha, hf⟩ hua
            | some e => simp [arrivalUnits, ha, hf]
          | _ => simp [arrivalUnits, ha]
        have hnin : ¬ UnitArrivalIn log q k := by
          rintro ⟨r', tx', hr', ha', hf', -⟩
          rw [hr] at hr'
          cases hr'
          exact hua ⟨tx', ha', hf'⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnin), ih, hunits, Nat.add_zero]
  rw [key log.length (Nat.le_refl _)]
  obtain ⟨-, hu⟩ := (h.accounted hni hj).2 s hs
  have hpend := ((h.accounted hni hj).2 s hs).1
  have hexpj := hexp j s hj hs
  have hmono := unitsBefore_mono log hj
  rw [hexpj] at hu hpend
  have : n * (q + 1) ≤ n * s.phase := Nat.mul_le_mul_left n hq
  rw [Nat.mul_succ] at hu this
  omega

end PTX.MBarrier

namespace PTX.MbarRing.Slot
open MBarrier

/-- A record of the phase a successful poll observes precedes the poll. -/
theorem updateBeforeWait_of_phase {ι : Type} {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    {i j phase : Nat} {d w : Record ι} (hi : log[i]? = some d) (hdf : d.fault = none)
    (hj : log[j]? = some w) (hwf : w.fault = none) (hw : w.reply.waited = some true)
    (hp : phaseAt log i = some phase) (ho : observedAt log j = some phase) :
    UpdateBeforeWait log d.id w.id := by
  have hilt : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  exact ⟨i, j, d, w, phase, hi, rfl, hdf, hj, rfl, hwf, hw,
    h.phase_before_observation hni (Nat.le_of_lt hilt) hp hj hw ho, hp, ho, hni.sameLifetime i j⟩

end PTX.MbarRing.Slot
