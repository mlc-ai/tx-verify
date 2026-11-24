-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Polls
public import Lemmas.Flow.EndSite
public import Lemmas.Flow.Final
public import Lemmas.Execution.EventFrameSource
public import Core.Assembly.Correctness

@[expose] public section

/-! # The thread frame of a kernel proof

A kernel proof follows each thread `g` by a site machine `C g : Flow.Code K A L g`. The layers
above the thread layer speak about a thread's events through the abstract state its machine is
in before each of them:

* `stateAt C X g k`: the state before thread `g`'s `k`-th event; `some none` when the machine no
  longer follows the thread, `none` after an event into a dead state. `stateAt_zero`,
  `stateAt_succ`, `stateAt_end` compute it.
* `Tracked C X`: no thread reaches `some none`; `tracked_of` proves it from the machine's
  successors along the threads' events, `tracked_of_next` for machines that never give up. A
  stopped machine stays stopped (`stateAt_none_mono`), so before a state of a tracked thread its
  machine is at a state (`stateAt_live`).
* `lt_of_get`: an event belongs to a launched thread.
* For sound machines (`∀ g < L.threads, (C g).Sound`) and a consistent execution: every event
  fired from the state before it, or is undefined behaviour after the machine stopped (`fired`);
  an event that is not undefined behaviour fires from a followed state (`event_state`, and every
  event does in an execution without undefined behaviour: `state_of_noUb`), at that
  state's site instruction (`fired_site`) and program counter (`event_pc`); a thread whose machine
  stopped stopped at one event (`first_stop`).
* `Pending L X g`: a launched thread that has neither exited nor been canceled. A pending thread
  of an execution without undefined behaviour has a run that ends in a state (`run_some`), which
  after local steps is a concrete state of the machine's last state (`end_at`), or a dead state
  if the machine stopped (`end_dead`). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} (C : (g : Nat) → Flow.Code K A L g)

/-- The abstract state of thread `g` before its `k`-th event: `some none` when the machine no
longer follows the thread, `none` after an event into a dead state. -/
def stateAt (X : Execution) (g k : Nat) : Option (Option (C g).D) :=
  (C g).toMachine.after (some (C g).init) ((X.tr g).take k)

/-- Every launched thread is followed by its machine at each of its events: it never reaches
`some none`. -/
def Tracked (X : Execution) : Prop :=
  ∀ g k, g < L.threads → stateAt C X g k ≠ some none

/-- A launched thread that has neither exited nor been canceled. -/
def Pending (L : Launch) (X : Execution) (g : Nat) : Prop :=
  g < L.threads ∧ ¬ ClcCanceled L X g ∧ ∀ pc, (X.tr g).getLast? ≠ some ⟨pc, .exit⟩

variable {C} {X : Execution} {g k : Nat}

theorem stateAt_zero : stateAt C X g 0 = some (some (C g).init) := by
  unfold stateAt
  rw [List.take_zero]
  rfl

theorem stateAt_succ {e : Event} (he : (X.tr g)[k]? = some e) :
    stateAt C X g (k + 1) = (stateAt C X g k).bind fun σ => (C g).toMachine.next σ e := by
  unfold stateAt
  rw [List.take_add_one, he, Option.toList_some]
  exact Machine.after_snoc _ _ _ _

theorem stateAt_end : stateAt C X g (X.tr g).length =
    (C g).toMachine.after (some (C g).init) (X.tr g) := by
  unfold stateAt
  rw [List.take_length]

theorem stateAt_of_le (hk : (X.tr g).length ≤ k) :
    stateAt C X g k = stateAt C X g (X.tr g).length := by
  unfold stateAt
  rw [List.take_of_length_le hk, List.take_length]

/-- A stopped machine stays stopped. -/
theorem stateAt_none_mono (h : stateAt C X g k = none) {n : Nat} (hkn : k ≤ n) :
    stateAt C X g n = none := by
  induction n with
  | zero => rwa [show k = 0 by omega] at h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hkn with heq | hlt
    · rwa [← heq]
    have ih' := ih (by omega)
    by_cases hn : n < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[n]? = some e := ⟨_, List.getElem?_eq_getElem hn⟩
      rw [stateAt_succ he, ih']
      rfl
    · rw [stateAt_of_le (by omega)]
      rwa [stateAt_of_le (by omega)] at ih'

/-- **Tracking from the successors**: a machine whose successor along each event of a launched
thread, from a followed state, is never `some none` follows every thread. -/
theorem tracked_of
    (h : ∀ g k d e, g < L.threads → (X.tr g)[k]? = some e → stateAt C X g k = some (some d) →
      (C g).next d e ≠ some none) : Tracked C X := by
  intro g k hg
  have hall : ∀ k, k ≤ (X.tr g).length → stateAt C X g k ≠ some none := by
    intro k
    induction k with
    | zero => intro _; rw [stateAt_zero]; simp
    | succ k ih =>
      intro hk
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [stateAt_succ he]
      cases hs : stateAt C X g k with
      | none => intro h; cases h
      | some σ =>
        cases σ with
        | none => exact absurd hs (ih (by omega))
        | some d =>
          simp only [Option.bind_some]
          exact h g k d e hg he hs
  by_cases hk : k ≤ (X.tr g).length
  · exact hall k hk
  · rw [stateAt_of_le (by omega)]
    exact hall _ le_rfl

/-- A machine that never gives up follows every thread. -/
theorem tracked_of_next (h : ∀ g d e, (C g).next d e ≠ some none) : Tracked C X :=
  tracked_of fun g _ d e _ _ _ => h g d e

/-- Before a state of a machine that follows its thread, the machine is at a state. -/
theorem stateAt_live (ht : Tracked C X) (hg : g < L.threads) {n : Nat} {d : (C g).D}
    (hσ : stateAt C X g n = some (some d)) (hk : k ≤ n) :
    ∃ d', stateAt C X g k = some (some d') := by
  cases h : stateAt C X g k with
  | none => rw [stateAt_none_mono h hk] at hσ; cases hσ
  | some σ =>
    cases σ with
    | none => exact absurd h (ht g k hg)
    | some d' => exact ⟨d', rfl⟩

variable {mem0 : Mem0}

/-- An event belongs to a launched thread. -/
theorem lt_of_get (hX : Consistent L K A mem0 X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) : g < L.threads := by
  have hk := (List.getElem?_eq_some_iff.mp he).1
  by_contra hn
  rw [hX.outside g (by omega)] at hk
  simp at hk

variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
include hC hX

/-- The run of a launched thread is a run of its machine. -/
theorem trace (hg : g < L.threads) : (C g).toMachine.Trace (some (C g).init) (X.tr g) :=
  (hC g hg).machine.produces (hX.thr g hg)

/-- **Each event fired from the state before it**, or is undefined behaviour after the machine
stopped. -/
theorem fired {e : Event} (he : X.get (g, k) = some e) :
    (∃ σ o, stateAt C X g k = some σ ∧ (C g).toMachine.Fired σ e o) ∨
      (stateAt C X g k = none ∧ ∃ pc f, e = ⟨pc, .ub f⟩) :=
  (trace hC hX (lt_of_get hX he)).fired he

omit hX in
/-- An event fired from a followed state is the event of the instruction at the state's site. -/
theorem fired_site_of {d : (C g).D} {e : Event} {o : Option TState} (hg : g < L.threads)
    (hf : (C g).toMachine.Fired (some d) e o) :
    ∃ t ins, (C g).AtD d t ∧ (C g).inv d ∧ K.code[(C g).pc d]? = some ins ∧
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o :=
  Code.fired_site (hC g hg) hf

/-- **An event at a followed state is its site instruction's event.** -/
theorem fired_site {d : (C g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : stateAt C X g k = some (some d)) :
    ∃ t ins o, (C g).AtD d t ∧ (C g).inv d ∧ K.code[(C g).pc d]? = some ins ∧
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o := by
  have hg := lt_of_get hX he
  obtain ⟨o, hf⟩ := (trace hC hX hg).fired_at he hσ
  obtain ⟨t, ins, h1, h2, h3, h4⟩ := fired_site_of hC hg hf
  exact ⟨t, ins, o, h1, h2, h3, h4⟩

/-- **An event is at its state's program counter.** -/
theorem event_pc {d : (C g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : stateAt C X g k = some (some d)) : e.pc = (C g).pc d := by
  obtain ⟨t, ins, o, -, -, -, hf⟩ := fired_site hC hX he hσ
  exact EventFrame.fires_source_pc hf

/-- **An event that is not undefined behaviour fires from a followed state.** -/
theorem event_state (ht : Tracked C X) {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) : ∃ d, stateAt C X g k = some (some d) := by
  rcases fired hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hσ (ht g k (lt_of_get hX he))
    | some d => exact ⟨d, hσ⟩
  · exact absurd rfl (hub pc f)

/-- In an execution without undefined behaviour, every event fires from a followed state. -/
theorem state_of_noUb (ht : Tracked C X) (hub : ¬ HasUb X) {e : Event}
    (he : X.get (g, k) = some e) : ∃ d, stateAt C X g k = some (some d) :=
  event_state hC hX ht he fun pc f h => hub ⟨(g, k), pc, f, h ▸ he⟩

omit hC hX in
/-- **A thread whose machine has stopped by event `k` stopped at an event**: the state before it
is followed and the one after it is not. -/
theorem first_stop (ht : Tracked C X) (hg : g < L.threads) (hk : stateAt C X g k = none) :
    ∃ i d, i < k ∧ stateAt C X g i = some (some d) ∧ stateAt C X g (i + 1) = none := by
  induction k with
  | zero => rw [stateAt_zero] at hk; cases hk
  | succ k ih =>
    cases hs : stateAt C X g k with
    | none =>
      obtain ⟨i, d, hi, h1, h2⟩ := ih hs
      exact ⟨i, d, by omega, h1, h2⟩
    | some σ =>
      cases σ with
      | none => exact absurd hs (ht g k hg)
      | some d => exact ⟨k, d, by omega, hs, hk⟩

omit hC in
/-- **A pending thread of an execution without undefined behaviour has a run that ends in a
state**: its trace ends neither with an exit nor with undefined behaviour. -/
theorem run_some (hub : ¬ HasUb X) (hp : Pending L X g) :
    ∃ t, Run K A L g {} (X.tr g) (some t) := by
  obtain ⟨o, hr⟩ := hX.thr g hp.1
  cases o with
  | some t => exact ⟨t, hr⟩
  | none =>
    obtain ⟨e, he, hk⟩ := Flow.Run.ended_last hr
    exfalso
    rcases hk with ⟨f, hf⟩ | hx
    · apply hub
      refine ⟨(g, (X.tr g).length - 1), e.pc, f, ?_⟩
      change (X.tr g)[(X.tr g).length - 1]? = _
      rw [← List.getLast?_eq_getElem?, he]
      cases e
      simp only at hf
      rw [hf]
    · apply hp.2.2 e.pc
      rw [he]
      cases e
      simp only at hx
      rw [hx]

omit hX in
/-- **Where a run that has not ended stops**: after local steps, at a concrete state of the
machine's last state, whose template is its site instruction's event. -/
theorem end_at (hg : g < L.threads) {t : TState} (hr : Run K A L g {} (X.tr g) (some t))
    {d : (C g).D} (hσ : stateAt C X g (X.tr g).length = some (some d)) :
    ∃ t1 ins, Relation.ReflTransGen (Tau K A L g) t t1 ∧ (C g).AtD d t1 ∧ (C g).inv d ∧
      K.code[(C g).pc d]? = some ins ∧ out K A L g t1 = .ev (eventTmpl A L g t1 ins.op) := by
  rw [stateAt_end] at hσ
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (hC g hg) hr hσ
  have hout := Code.site_out (hC g hg) hgood
  obtain ⟨ins, hc, -, -⟩ := ((hC g hg).steps d).site hgood.2
  simp only [Code.tmpl, hc] at hout
  exact ⟨t1, ins, hl, hgood.1, hgood.2, hc, hout⟩

omit hX in
/-- A run that has not ended, along which the machine stopped, ends in a dead state. -/
theorem end_dead (hg : g < L.threads) {t : TState} (hr : Run K A L g {} (X.tr g) (some t))
    (hσ : stateAt C X g (X.tr g).length = none) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  rw [stateAt_end] at hσ
  exact (hC g hg).machine.final_dead hr hσ

end

end PTX.Frame
