-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Kda
public import Lemmas.Kernel.Bound

@[expose] public section

/-!
# The termination skeleton: bounded executions, from a rank on the machines' states

`Correct.terminates` says that one number bounds the counted size of every consistent
execution (`BoundGoal`: `∃ N, ∀ X, Consistent L K A mem0 X → X.size L ≤ N`). The size counts
the threads' events except failed `mbarrier.try_wait` polls, plus the stages of the
asynchronous operations those events issue. The statement asks only for the existence of the
bound, so no closed formula appears in the theorem; the proof supplies a bound `n` on the
counted events of one thread, and the library turns it into a bound on the size
(`terminates_of_count`: it multiplies by the number of threads and by a grid-dependent bound on
the asynchronous stages of one event).

The bound on one thread is a rank argument (`Frame.count_le`): a natural number `rank g d` for
every state `d` of thread `g`'s site machine such that no step of the machine raises it and
every counted event lowers it by at least one. Then the thread's counted events are at most the
rank of its first state plus two (an event into a dead state, and its undefined behaviour). The
step condition is asked only along consistent executions and from states that satisfy the
machine's invariant, so the rank may use what the invariant knows (for instance that the tile
counter of a loop state is at most the tile count of the thread's sequence).

Failed polls need no bound: they are not counted, and the rank is not asked to fall at them.

`BoundPremises` are the premises (the machines, the rank, its step condition, the bound on the
first states). `bound_of` is the generic theorem; `terminates` is its instance for the FlashKDA
kernel, which needs no further hypothesis: the kernel issues no linear bulk copy (`codeOk`), so
the library's condition on copy sizes is vacuous. Unlike the progress skeleton, nothing here
depends on the assumptions' execution constraints.

The rank for this kernel (`Proof/Ref/Assembly/ProgressNums.lean` defines it): per role, the
events left before the tile loop, plus `(T - t) * W` for the tiles not yet started (`T` the tile
count of the CTA's sequence, `t` the loop counter, `W` the counted events of one tile: 268 for
a compute thread, 72 for the load leader, at most 2,163 for the store leader), plus the events
left in the current tile and after the loop.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Flow PTX.Kernels.FlashKdaFwd

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **The premises of the termination skeleton**: sound machines that follow every consistent
execution, and a rank on their states, at most `n` at the first state, that every step along a
consistent execution lowers by the event's count. -/
structure BoundPremises (C : (g : Nat) → Flow.Code K A L g) (mem0 : Mem0)
    (rank : (g : Nat) → (C g).D → Nat) (n : Nat) : Prop where
  /-- Every thread's site machine is sound. -/
  sound : ∀ g < L.threads, (C g).Sound
  /-- Every consistent execution is followed by the machines. -/
  tracked : ∀ X, Consistent L K A mem0 X → Frame.Tracked C X
  /-- A step from the state before the thread's `k`-th event, which satisfies the machine's
  invariant, does not raise the rank, and lowers it when the event is counted (every event but
  a failed poll). -/
  dec : ∀ X, Consistent L K A mem0 X → ∀ g < L.threads, ∀ k d d' e,
    (X.tr g)[k]? = some e → Frame.stateAt C X g k = some (some d) → (C g).inv d →
    (C g).next d e = some (some d') → rank g d' + (if e.counts then 1 else 0) ≤ rank g d
  /-- The rank of a thread's first state is at most `n`. -/
  init : ∀ g < L.threads, rank g (C g).init ≤ n

/-- **A thread's counted events are at most `n + 2`.** -/
theorem BoundPremises.counts_le {C : (g : Nat) → Flow.Code K A L g} {mem0 : Mem0}
    {rank : (g : Nat) → (C g).D → Nat} {n : Nat} (B : BoundPremises C mem0 rank n)
    {X : Execution} (hX : Consistent L K A mem0 X) {g : Nat} (hg : g < L.threads) :
    (X.tr g).countP Event.counts ≤ n + 2 := by
  have h := Frame.count_le B.sound hX hg (B.tracked X hX) (rank g) (fun _ => false) 0
    fun k d d' e he hσ hinv hn => by simpa using B.dec X hX g hg k d d' e he hσ hinv hn
  have h0 := B.init g hg
  simp only [Nat.zero_mul, Nat.add_zero] at h
  omega

/-- **Bounded executions**, for a kernel that issues no linear bulk copy. -/
theorem bound_of {C : (g : Nat) → Flow.Code K A L g} {mem0 : Mem0}
    {rank : (g : Nat) → (C g).D → Nat} {n : Nat} (hc : CodeOk L K mem0 A)
    (B : BoundPremises C mem0 rank n) : BoundGoal K A L mem0 :=
  terminates_of_count (n + 2) (fun _ hX _ hg => B.counts_le hX hg)
    fun _ hX i _ ⟨_, hi⟩ => (hc.no_kind hX (i := i) rfl hi).elim

/-- **Termination of the FlashKDA kernel**, from the rank premises. -/
theorem terminates {C : (g : Nat) → Flow.Code Decoded.kernel Assumptions.all L g} {mem0 : Mem0}
    {rank : (g : Nat) → (C g).D → Nat} {n : Nat} (B : BoundPremises C mem0 rank n) :
    BoundGoal Decoded.kernel Assumptions.all L mem0 :=
  bound_of codeOk B

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
