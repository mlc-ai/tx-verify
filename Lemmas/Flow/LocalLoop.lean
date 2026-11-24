-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegChain

@[expose] public section

/-! # Local loops

A proof tool. A loop whose body performs no event is, for a site machine, part of one local
segment: the thread passes through all its iterations between two events. A segment proof
cannot evaluate it by `run n` with a fixed `n` unless the iteration count is known, so the loop
is taken by induction:

* `run_loop_wf`: a measure on the loop-head states decreases with every iteration, until an
  iteration leaves the loop. The number of steps is not tracked.
* `run_iter`, `run_loop`: the iterations are counted by `k` (typically a counter register whose
  value the head facts give as a function of `k`); iterations `k < N` return to the head, the
  `N`-th leaves it. The number of steps is `N * m + e`.
* `Seg.loop`: the counted loop with register facts at the head, as one `Seg` piece, so a site
  machine's step passes through the loop like through any other piece of its segment.

Each body or exit piece is an ordinary segment (`seg_fp`, `Seg.bra` for the loop's branches). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A loop with a decreasing measure.** From a head state (`P`) an iteration either leaves
the loop (reaching `Q`) or returns to a head state of smaller measure; then every head state
reaches `Q`. -/
theorem run_loop_wf (P Q : TState → Prop) (μ : TState → Nat)
    (hstep : ∀ t, P t → (∃ n t', run K A L g n t = some t' ∧ Q t') ∨
      (∃ n t', run K A L g n t = some t' ∧ P t' ∧ μ t' < μ t)) :
    ∀ t, P t → ∃ n t', run K A L g n t = some t' ∧ Q t' := by
  suffices h : ∀ k t, μ t = k → P t → ∃ n t', run K A L g n t = some t' ∧ Q t' from
    fun t => h _ t rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t hk hP
    rcases hstep t hP with h | ⟨n, t', hr, hP', hlt⟩
    · exact h
    · obtain ⟨n', t'', hr', hQ⟩ := ih (μ t') (hk ▸ hlt) t' rfl hP'
      exact ⟨n + n', t'', run_comp hr hr', hQ⟩

/-- **Counted iterations.** If iteration `k < N` takes `m` local steps from a state of `I k` to
one of `I (k + 1)`, then `N * m` local steps take a state of `I 0` to one of `I N`. -/
theorem run_iter (I : Nat → TState → Prop) (m N : Nat)
    (hbody : ∀ k < N, ∀ t, I k t → ∃ t', run K A L g m t = some t' ∧ I (k + 1) t') :
    ∀ t, I 0 t → ∃ t', run K A L g (N * m) t = some t' ∧ I N t' := by
  intro t h0
  suffices h : ∀ k ≤ N, ∃ t', run K A L g (k * m) t = some t' ∧ I k t' from h N le_rfl
  intro k
  induction k with
  | zero => exact fun _ => ⟨t, by simp [run], h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t1, hr1, h1⟩ := ih (by omega)
    obtain ⟨t2, hr2, h2⟩ := hbody k (by omega) t1 h1
    exact ⟨t2, by rw [Nat.succ_mul]; exact run_comp hr1 hr2, h2⟩

/-- **A counted loop and its exit.** `N` iterations of `m` steps, then `e` steps from `I N` to
`Q`. -/
theorem run_loop (I : Nat → TState → Prop) (Q : TState → Prop) (m e N : Nat)
    (hbody : ∀ k < N, ∀ t, I k t → ∃ t', run K A L g m t = some t' ∧ I (k + 1) t')
    (hexit : ∀ t, I N t → ∃ t', run K A L g e t = some t' ∧ Q t') :
    ∀ t, I 0 t → ∃ t', run K A L g (N * m + e) t = some t' ∧ Q t' := by
  intro t h0
  obtain ⟨t1, hr1, h1⟩ := run_iter I m N hbody t h0
  obtain ⟨t2, hr2, h2⟩ := hexit t1 h1
  exact ⟨t2, run_comp hr1 hr2, h2⟩

/-- **A counted loop as one segment piece.** The head is at `head` with facts `F k` before
iteration `k`; iterations `k < N` return to the head, and from `F N` the exit piece reaches
`b`. -/
theorem Seg.loop {head b m e N : Nat} {F : Nat → List (Nat × Value)} {G : List (Nat × Value)}
    (hbody : ∀ k < N, Seg K A L g m head (F k) head (F (k + 1)))
    (hexit : Seg K A L g e head (F N) b G) : Seg K A L g (N * m + e) head (F 0) b G :=
  run_loop (fun k t => At t head (F k)) (fun t => At t b G) m e N hbody hexit

/-- A loop with a decreasing measure as reachability: every head state reaches `Q` by local
steps. -/
theorem rtg_of_loop_wf (P Q : TState → Prop) (μ : TState → Nat)
    (hstep : ∀ t, P t → (∃ n t', run K A L g n t = some t' ∧ Q t') ∨
      (∃ n t', run K A L g n t = some t' ∧ P t' ∧ μ t' < μ t)) {t : TState} (h : P t) :
    ∃ t', Relation.ReflTransGen (Tau K A L g) t t' ∧ Q t' := by
  obtain ⟨n, t', hr, hQ⟩ := run_loop_wf P Q μ hstep t h
  exact ⟨t', run_rtg hr, hQ⟩

end

end PTX.Flow
