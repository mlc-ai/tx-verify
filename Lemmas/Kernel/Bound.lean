-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Goals
public import Lemmas.Flow.Bound
public import Lemmas.Kernel.Correct

@[expose] public section

/-! # `BoundGoal` from a rank on the machines' states

A rank on each thread's abstract states that no machine step increases and every counted event
decreases bounds the thread's counted events by its initial rank plus two (an event into a dead
state and its undefined behaviour), along every execution its machine follows
(`Frame.count_le`); events that reset the thread's work (a successful poll for a new task) may
raise the rank by a budget each. A uniform bound on the initial ranks bounds every consistent
execution's size
(`bound_of_rank`, through `terminates_of_count`). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Flow.Code K A L g}

/-- **A thread's counted events are bounded by its initial rank and its resets.** A rank on the
thread's abstract states that each step, from a state with its invariant before the thread's
`k`-th event, lowers by the event's count, except that a reset event may raise it by `budget`,
bounds the thread's counted events by its initial rank plus two (an event into a dead state and its
undefined behaviour) plus `budget` per reset event. -/
theorem count_le {X : Execution} {g : Nat} (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) (ht : Tracked C X)
    (rank : (C g).D → Nat) (reset : Event → Bool) (budget : Nat)
    (hdec : ∀ k d d' e, (X.tr g)[k]? = some e → stateAt C X g k = some (some d) → (C g).inv d →
      (C g).next d e = some (some d') →
      rank d' + (if e.counts then 1 else 0) ≤ rank d + (if reset e then budget else 0)) :
    (X.tr g).countP Event.counts ≤ rank (C g).init + 2 + budget * (X.tr g).countP reset := by
  let r : (C g).toMachine.St → Nat := fun σ => match σ with
    | some d => rank d
    | none => 0
  exact Machine.Trace.count_le_resets_at r reset budget (trace hC hX hg)
    fun k e σ1 σ2 u he h1 h2 hf => by
      have h1' : stateAt C X g k = some σ1 := h1
      have h2' : stateAt C X g (k + 1) = some σ2 := h2
      rw [stateAt_succ he, h1'] at h2'
      cases σ1 with
      | none => exact absurd h1' (ht g k hg)
      | some d =>
        cases σ2 with
        | none =>
          refine absurd ?_ (ht g (k + 1) hg)
          rw [stateAt_succ he, h1']
          exact h2'
        | some d' =>
          obtain ⟨-, -, -, hinv, -⟩ := fired_site_of hC hg hf
          exact hdec k d d' e he h1' hinv h2'

/-- **`BoundGoal` from ranks**: ranks on the machines' states that no step increases and every
counted event decreases, with initial ranks at most `n`, bound every consistent execution. Every
copy of a consistent execution is bounded in its destination by its 32-bit size operand
(`hcopy`), which bounds the asynchronous stages it contributes. -/
theorem bound_of_rank (hC : ∀ g < L.threads, (C g).Sound)
    (ht : ∀ X, Consistent L K A mem0 X → Tracked C X) (rank : (g : Nat) → (C g).D → Nat)
    (hdec : ∀ g < L.threads, ∀ d d' e, (C g).next d e = some (some d') →
      rank g d' + (if e.counts then 1 else 0) ≤ rank g d)
    (n : Nat) (hn : ∀ g < L.threads, rank g (C g).init ≤ n)
    (hcopy : ∀ X, Consistent L K A mem0 X → ∀ i s, X.Copy i s → s.dst.size ≤ 2 ^ 32) :
    BoundGoal K A L mem0 :=
  terminates_of_count (n + 2)
    (fun X hX g hg =>
      (count_le hC hX hg (ht X hX) (rank g) (fun _ => false) 0
        fun _ d d' e _ _ _ hn => by simpa using hdec g hg d d' e hn).trans
        (by have := hn g hg; simp only [Nat.zero_mul, Nat.add_zero]; omega))
    hcopy

end

end PTX.Frame
