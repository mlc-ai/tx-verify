-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # A thread that reached a region of positions never leaves it

A proof tool, generic over the kernel. `LoClosed K A L lo` says that no local step and no
continuation of an event leads from a position at or above `lo` to one below it, and an event
just below `lo` continues at or above it. Then in a run of
a thread, every event after an event at or above `lo - 1` is at or above `lo`
(`Run.pc_ge_later`), undefined behaviour included. -/

namespace PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {lo : Nat}

/-- No local step and no event continuation goes from `lo` or above to below `lo`. -/
structure LoClosed (K : Kernel) (A : List Assumption) (L : Launch) (lo : Nat) : Prop where
  tau : ∀ g (t t' : TState), lo ≤ t.pc → Tau K A L g t t' → lo ≤ t'.pc
  ret : ∀ g (t : TState) e u, lo ≤ t.pc → EStep K A L g t e (some u) → lo ≤ u.pc
  /-- An event at the position just below `lo` continues at or above `lo`. -/
  enter : ∀ g (t : TState) e u, t.pc + 1 = lo → EStep K A L g t e (some u) → lo ≤ u.pc

theorem LoClosed.rtg (h : LoClosed K A L lo) {g : Nat} {t t1 : TState} (hl : lo ≤ t.pc)
    (hr : Relation.ReflTransGen (Tau K A L g) t t1) : lo ≤ t1.pc := by
  induction hr with
  | refl => exact hl
  | tail _ ht ih => exact h.tau g _ _ ih ht

/-- A run from a state at or above `lo` has all its events at or above `lo`. -/
theorem Run.pc_ge_all (h : LoClosed K A L lo) {g : Nat} {t : TState} {es : List Event}
    {o : Option TState} (hr : Run K A L g t es o) (ht : lo ≤ t.pc) {i : Nat} {e' : Event}
    (hi : es[i]? = some e') : lo ≤ e'.pc := by
  induction hr generalizing i with
  | nil => simp at hi
  | @step t t1 t2 e0 rest o hr1 hs hrest ih =>
    have h1 : lo ≤ t1.pc := h.rtg ht hr1
    have h2 := h.ret g t1 _ _ h1 hs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [EventFrame.estep_source_pc hs]; exact h1
    | succ i => exact ih h2 hi
  | @last t t1 e0 hr1 hs =>
    have h1 : lo ≤ t1.pc := h.rtg ht hr1
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [EventFrame.estep_source_pc hs]; exact h1
    | succ i => simp at hi

/-- **Every event after an event at `lo - 1` or above is at or above `lo`.** -/
theorem Run.pc_ge_later (h : LoClosed K A L lo) {g : Nat} {t : TState} {es : List Event}
    {o : Option TState} (hr : Run K A L g t es o) {j i : Nat} (hji : j < i) {e e' : Event}
    (hj : es[j]? = some e) (hlo : lo ≤ e.pc + 1) (hi : es[i]? = some e') : lo ≤ e'.pc := by
  induction hr generalizing j i with
  | nil => simp at hj
  | @step t t1 t2 e0 rest o hr1 hs hrest ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have h0 : e0.pc = t1.pc := EventFrame.estep_source_pc hs
      have h2 : lo ≤ t2.pc := by
        by_cases h1 : lo ≤ t1.pc
        · exact h.ret g t1 _ _ h1 hs
        · exact h.enter g t1 _ _ (by omega) hs
      cases i with
      | zero => omega
      | succ i => exact Run.pc_ge_all h hrest h2 (by simpa using hi)
    | succ j =>
      cases i with
      | zero => omega
      | succ i => exact ih (by omega) hj hi
  | last hr1 hs =>
    cases j with
    | zero =>
      cases i with
      | zero => omega
      | succ i => simp at hi
    | succ j => simp at hj

end PTX
