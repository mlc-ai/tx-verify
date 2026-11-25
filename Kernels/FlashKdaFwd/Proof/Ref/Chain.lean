-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame

/-!
# Chaining the phases of a thread's run

The reference layer describes a thread's run phase by phase (startup, conversion, carry loads,
one of the three tile loops, epilogue). Each phase proves one theorem of the same shape: from
its entry condition at some trace position, at every later followed state the phase's
invariant holds, or the phase's exit condition held at an earlier position. This file states
that shape once (`Phase`, `Phase.Traces`) and proves that two phases can be joined when the exit
condition of the first gives the entry condition of the second (`Phase.Traces.seq`), so the
whole run of a thread is one chain. It names no kernel.

Words: a *followed state* at position `k` is the state of the thread's machine before the
thread's `k`-th event, when the machine still follows the thread (`Frame.stateAt … = some (some
s)`). The *entry index* of a phase is the position at which its entry condition held; the
invariant and the exit condition may refer to it (counts "since the entry").
-/

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g : Nat}

/-- The machine of thread `g` follows the thread and is at state `s` before event `k`. -/
abbrev At (C : (g : Nat) → Flow.Code K A L g) (X : Execution) (g k : Nat) (s : (C g).D) : Prop :=
  Frame.stateAt C X g k = some (some s)

/-- **A phase of the run of thread `g`**: the entry condition at a position, the invariant at a
position given the entry index, and the exit condition at a position given the entry index. -/
structure Phase (C : (g : Nat) → Flow.Code K A L g) (g : Nat) where
  /-- The entry condition: position, state. -/
  In : Nat → (C g).D → Prop
  /-- The invariant: entry index, position, state. -/
  Inv : Nat → Nat → (C g).D → Prop
  /-- The exit condition: entry index, position, state. -/
  Out : Nat → Nat → (C g).D → Prop

/-- **The theorem of a phase**: from the entry condition at a followed state at `k0`, every
later followed state before an event satisfies the invariant, or the exit condition held at a
followed state between the entry and it. -/
def Phase.Traces (Φ : Phase C g) (X : Execution) : Prop :=
  ∀ k0 s0 k s, At C X g k0 s0 → Φ.In k0 s0 → k0 ≤ k → k < (X.tr g).length → At C X g k s →
    Φ.Inv k0 k s ∨ ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ At C X g j s1 ∧ Φ.Out k0 j s1

/-- The same phase with the exit taken at its FIRST position: the invariant holds at every
followed state from the entry up to it. (Counts of events the phase does not make are only
known at the first exit.) -/
def Phase.first (Φ : Phase C g) (X : Execution) : Phase C g where
  In := Φ.In
  Inv := Φ.Inv
  Out k0 j s1 := Φ.Out k0 j s1 ∧ ∀ i si, k0 ≤ i → i < j → At C X g i si → Φ.Inv k0 i si

open Classical in
/-- A phase leaves through a first exit. -/
theorem Phase.Traces.first {Φ : Phase C g} (h : Φ.Traces X) : (Φ.first X).Traces X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases h k0 s0 k s h0 hin hk0 hk hs with hi | hex
  · exact .inl hi
  · have hex' : ∃ j, k0 ≤ j ∧ j ≤ k ∧ ∃ s1, At C X g j s1 ∧ Φ.Out k0 j s1 := by
      obtain ⟨j, s1, h1, h2, h3, h4⟩ := hex
      exact ⟨j, h1, h2, s1, h3, h4⟩
    obtain ⟨h1, h2, s1, h3, h4⟩ := Nat.find_spec hex'
    refine .inr ⟨Nat.find hex', s1, h1, h2, h3, h4, fun i si hi1 hi2 hsi => ?_⟩
    rcases h k0 s0 i si h0 hin hi1 (by omega) hsi with hi | ⟨j', s', h1', h2', h3', h4'⟩
    · exact hi
    · exact absurd (Nat.find_min' hex' ⟨h1', by omega, s', h3', h4'⟩) (by omega)

/-- **Two phases in a row**: the entry of the first; the invariant of the first, or the first
has left at some position and the invariant of the second holds with that position as its entry
index; the exit of the second after the exit of the first. -/
def Phase.seq (Φ Ψ : Phase C g) (X : Execution) : Phase C g where
  In := Φ.In
  Inv k0 k s := Φ.Inv k0 k s ∨
    ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ At C X g j s1 ∧ Φ.Out k0 j s1 ∧ Ψ.In j s1 ∧ Ψ.Inv j k s
  Out k0 k s := ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ At C X g j s1 ∧ Φ.Out k0 j s1 ∧ Ψ.In j s1 ∧ Ψ.Out j k s

/-- **Joining two phases**: when the exit condition of the first gives the entry condition of
the second at the same followed state, the two theorems give the theorem of the pair. -/
theorem Phase.Traces.seq {Φ Ψ : Phase C g} (hΦ : Φ.Traces X) (hΨ : Ψ.Traces X)
    (hlink : ∀ k0 j s1, At C X g j s1 → Φ.Out k0 j s1 → Ψ.In j s1) : (Φ.seq Ψ X).Traces X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases hΦ k0 s0 k s h0 hin hk0 hk hs with hi | ⟨j, s1, h1, h2, h3, h4⟩
  · exact .inl (.inl hi)
  · have hin2 := hlink k0 j s1 h3 h4
    rcases hΨ j s1 k s h3 hin2 h2 hk hs with hi | ⟨j2, s2, h5, h6, h7, h8⟩
    · exact .inl (.inr ⟨j, s1, h1, h2, h3, h4, hin2, hi⟩)
    · exact .inr ⟨j2, s2, by omega, h6, h7, j, s1, h1, h5, h3, h4, hin2, h8⟩

/-- A phase whose invariant is weakened and whose exit condition is strengthened in the
hypothesis: the theorem transfers along implications. -/
theorem Phase.Traces.mono {Φ Ψ : Phase C g} (h : Φ.Traces X)
    (hin : ∀ k s, At C X g k s → Ψ.In k s → Φ.In k s)
    (hinv : ∀ k0 k s, Φ.Inv k0 k s → Ψ.Inv k0 k s)
    (hout : ∀ k0 j s, At C X g j s → Φ.Out k0 j s → Ψ.Out k0 j s) : Ψ.Traces X := by
  intro k0 s0 k s h0 hi hk0 hk hs
  rcases h k0 s0 k s h0 (hin k0 s0 h0 hi) hk0 hk hs with h1 | ⟨j, s1, h1, h2, h3, h4⟩
  · exact .inl (hinv _ _ _ h1)
  · exact .inr ⟨j, s1, h1, h2, h3, hout _ _ _ h3 h4⟩

/-- Before its first event the machine is at its initial state. -/
theorem at_zero : At C X g 0 (C g).init := by
  simp only [At, Frame.stateAt, List.take_zero]
  rfl

/-- **The whole run**: a chain whose entry condition holds of the initial state gives, at every
followed state before an event, the invariant of the chain (with entry index 0) or an exit of
the chain at an earlier position. -/
theorem Phase.Traces.run {Φ : Phase C g} (h : Φ.Traces X) (hin : Φ.In 0 (C g).init) {k : Nat}
    {s : (C g).D} (hk : k < (X.tr g).length) (hs : At C X g k s) :
    Φ.Inv 0 k s ∨ ∃ j s1, j ≤ k ∧ At C X g j s1 ∧ Φ.Out 0 j s1 := by
  rcases h 0 _ k s at_zero hin (Nat.zero_le _) hk hs with hi | ⟨j, s1, -, h2, h3, h4⟩
  · exact .inl hi
  · exact .inr ⟨j, s1, h2, h3, h4⟩

end PTX.Kernels.FlashKdaFwd.Proof.Ref
