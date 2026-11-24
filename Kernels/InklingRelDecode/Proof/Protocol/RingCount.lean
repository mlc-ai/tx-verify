-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine
public import Lemmas.Flow.Final
public import Lemmas.Flow.Polls

@[expose] public section

/-!
# Counting events along a run of a site machine

Generic facts about `Flow.Machine.Trace`, which the ring accounting of the loader and of the
MMA warp is built on (candidates for `Lemmas/Flow/`):

* `trace_drop`, `trace_take`: after the first `k` events of a run, the rest is a run from the
  state reached, and a prefix of a run is a run;
* `count_trace`: if the abstract state carries a measure `μ` that each step of the machine
  changes exactly by the event's contribution to a count (`p e = true` for a counted event), then
  the count of a run is the change of the measure along it, as long as the run stays in a set of
  states where this holds. A step is checked once, for an event
  that fires from the state (`Fired`) or an event that ends the thread (`Ends`), the two kinds of
  event of a `Trace`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {M : Machine K A L g}

/-- **The rest of a run is a run.** After the first `k` events of a run from `σ`, which reach the
state `σ'`, the remaining events are a run from `σ'`. -/
theorem trace_drop {σ σ' : M.St} {es : List Event} (h : M.Trace σ es) {k : Nat}
    (ha : M.after σ (es.take k) = some σ') : M.Trace σ' (es.drop k) := by
  induction h generalizing k with
  | nil σ =>
    simp only [List.take_nil, Machine.after_nil, Option.some.injEq] at ha
    subst ha
    rw [List.drop_nil]
    exact .nil _
  | step hf hn rest ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at ha
      subst ha
      exact .step hf hn rest
    | succ k =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some,
        List.drop_succ_cons] at ha ⊢
      exact ih ha
  | last hf =>
    cases k with
    | zero =>
      simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at ha
      subst ha
      exact .last hf
    | succ k =>
      simp only [List.drop_succ_cons, List.drop_nil]
      exact .nil _
  | dead hf hn hlen hub =>
    cases k with
    | zero =>
      simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at ha
      subst ha
      exact .dead hf hn hlen hub
    | succ k =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_none] at ha
      cases ha

/-- **A prefix of a run is a run.** -/
theorem trace_take {σ : M.St} {es : List Event} (h : M.Trace σ es) (n : Nat) :
    M.Trace σ (es.take n) := by
  induction h generalizing n with
  | nil σ => simpa using Machine.Trace.nil σ
  | step hf hn rest ih =>
    cases n with
    | zero => exact .nil _
    | succ n =>
      rw [List.take_succ_cons]
      exact .step hf hn (ih n)
  | last hf =>
    cases n with
    | zero => exact .nil _
    | succ n =>
      cases n
      · simpa using Machine.Trace.last hf
      · simpa using Machine.Trace.last hf
  | dead hf hn hlen hub =>
    cases n with
    | zero => exact .nil _
    | succ n =>
      rw [List.take_succ_cons]
      exact .dead hf hn (le_trans (List.length_take_le' _ _) hlen)
        (fun e' he' => hub e' (List.mem_of_mem_take he'))

/-- **The count of a run is the change of the measure.** `dom` is a set of abstract states, `μ` a
measure, `p` a count of events and `E` a property of the events of the run (every event of `es`
has it; for instance, that each election returned the thread's lane). If every step from a state
of `dom` (by an event that fires there, or by an event that ends the thread) to a state of `dom`
or to the run's last state `τ` changes `μ` by one exactly when `p` counts the event, then along a
run from `σ` to `τ` whose states before each event are in `dom` (`hall`),
`es.countP p + μ σ = μ τ`. -/
theorem count_trace (p : Event → Bool) (μ : M.St → Nat) (dom : M.St → Prop)
    (E : Event → Prop)
    (τ : M.St)
    (hstep : ∀ σ e σ', dom σ → E e → ((∃ u, M.Fired σ e (some u)) ∨ Ends e) →
      M.next σ e = some σ' → (dom σ' ∨ σ' = τ) → μ σ' = μ σ + if p e then 1 else 0) :
    ∀ {σ : M.St} {es : List Event}, M.Trace σ es → (∀ e ∈ es, E e) →
      (∀ j < es.length, ∃ τ, M.after σ (es.take j) = some τ ∧ dom τ) →
      M.after σ es = some τ → es.countP p + μ σ = μ τ := by
  intro σ es h
  induction h with
  | nil σ =>
    intro _ _ ha
    simp only [Machine.after_nil, Option.some.injEq] at ha
    subst ha
    simp
  | @step σ σ1 e es u hf hn rest ih =>
    intro hE hall ha
    simp only [Machine.after_cons, hn, Option.bind_some] at ha
    obtain ⟨σ0, h0, hd0⟩ := hall 0 (by simp)
    simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at h0
    subst h0
    have hd1 : dom σ1 ∨ σ1 = τ := by
      cases es with
      | nil =>
        simp only [Machine.after_nil, Option.some.injEq] at ha
        exact .inr ha
      | cons e' es' =>
        obtain ⟨τ', h', hd'⟩ := hall 1 (by simp)
        simp only [List.take_succ_cons, List.take_zero, Machine.after_cons, hn, Option.bind_some,
          Machine.after_nil] at h'
        simp only [Option.some.injEq] at h'
        subst h'
        exact .inl hd'
    have hm1 := hstep σ e σ1 hd0 (hE e (by simp)) (.inl ⟨u, hf⟩) hn hd1
    have hall' : ∀ j < es.length, ∃ τ, M.after σ1 (es.take j) = some τ ∧ dom τ := by
      intro j hj
      obtain ⟨τ', h', hd'⟩ := hall (j + 1) (by simp; omega)
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some] at h'
      exact ⟨τ', h', hd'⟩
    have hmτ := ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) hall' ha
    rw [List.countP_cons]
    omega
  | @last σ e hf =>
    intro hE hall ha
    simp only [Machine.after_cons, Machine.after_nil] at ha
    obtain ⟨σ0, h0, hd0⟩ := hall 0 (by simp)
    simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at h0
    subst h0
    obtain ⟨u, hu⟩ : ∃ u, M.next σ e = some u := by
      cases hn : M.next σ e with
      | none => simp [hn] at ha
      | some u => exact ⟨u, rfl⟩
    obtain ⟨t, -, hfire⟩ := hf
    have hend := fires_none_ends hfire
    simp only [hu, Option.bind_some, Option.some.injEq] at ha
    have hm1 := hstep σ e _ hd0 (hE e (by simp)) (.inr hend) hu (.inr ha)
    subst ha
    simp only [List.countP_cons, List.countP_nil]
    omega
  | @dead σ e es u hf hn hlen hub =>
    intro _ _ ha
    simp only [Machine.after_cons, hn, Option.bind_none] at ha
    cases ha

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
