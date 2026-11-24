-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Bound

@[expose] public section

/-!
# `BoundGoal` from ranks with resets that remember their program counter

`Frame.bound_of_rank` asks every machine step to lower the rank by its count, so a machine that
returns to an earlier state (the workers' dispatch loop, which every role leaves for the dispatch)
cannot be ranked. `Frame.count_le` allows a rank to rise by a budget at a reset event but its
step hypothesis does not say which event is a reset. Here the step hypothesis also gets the fact
that the event is at the program counter of the state it fires from (`Frame.event_pc`'s source,
`EventFrame.fires_source_pc`), so a reset can be named by the program counter of one site of the
machine (the dispatch's load of the role byte).

* `count_le_resets`: a thread's counted events are at most its initial rank, plus two, plus the
  budget for each reset event of its trace.
* `bound_of_rank_resets`: ranks on all the machines, a budget, and a bound on each thread's reset
  events, bound every consistent execution (`BoundGoal`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound
open PTX PTX.Flow PTX.Frame

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Flow.Code K A L g}

/-- **A thread's counted events are bounded by its initial rank and its resets.** The rank of
a state with its invariant, before an event at the state's program counter that leads to a state
with its invariant (every step of a sound machine does), may rise by `budget` at a reset event;
otherwise it falls by the event's count. -/
theorem count_le_resets {X : Execution} {g : Nat} (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) (ht : Tracked C X)
    (rank : (C g).D → Nat) (reset : Event → Bool) (budget : Nat)
    (hdec : ∀ d d' e, (C g).inv d → (C g).inv d' → e.pc = (C g).pc d →
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
          obtain ⟨t, ins, hat, hinv, hcode, hfi⟩ := fired_site_of hC hg hf
          have hn : (C g).next d e = some (some d') := h2'
          rcases ((hC g hg).steps d).step ins hat hinv hcode hfi with
            (hn' | ⟨d1, t', hn', -, hgood⟩) | ⟨hn', -⟩
          · rw [hn] at hn'
            cases hn'
          · rw [hn] at hn'
            obtain rfl := Option.some.inj (Option.some.inj hn')
            exact hdec d d' e hinv hgood.2 (EventFrame.fires_source_pc hfi) hn
          · rw [hn] at hn'
            cases hn'

/-- **`BoundGoal` from ranks with resets**: ranks on the machines' states that, at states with
their invariant and events at their program counter, fall by the event's count except for a
budget at a reset event, with initial ranks at most `n` and at most `R` reset events in each
thread's trace, bound every consistent execution (the step hypothesis also has the invariants of
both states, as `count_le_resets`). Every copy of a consistent execution is
bounded in its destination by its 32-bit size operand (`hcopy`). -/
theorem bound_of_rank_resets (hC : ∀ g < L.threads, (C g).Sound)
    (ht : ∀ X, Consistent L K A mem0 X → Tracked C X) (rank : (g : Nat) → (C g).D → Nat)
    (reset : Nat → Event → Bool) (budget R n : Nat)
    (hdec : ∀ g < L.threads, ∀ d d' e, (C g).inv d → (C g).inv d' → e.pc = (C g).pc d →
      (C g).next d e = some (some d') →
      rank g d' + (if e.counts then 1 else 0) ≤ rank g d + (if reset g e then budget else 0))
    (hn : ∀ g < L.threads, rank g (C g).init ≤ n)
    (hR : ∀ X, Consistent L K A mem0 X → ∀ g < L.threads, (X.tr g).countP (reset g) ≤ R)
    (hcopy : ∀ X, Consistent L K A mem0 X → ∀ i s, X.Copy i s → s.dst.size ≤ 2 ^ 32) :
    BoundGoal K A L mem0 :=
  terminates_of_count (n + 2 + budget * R)
    (fun X hX g hg =>
      (count_le_resets hC hX hg (ht X hX) (rank g) (reset g) budget (hdec g hg)).trans
        (by
          have h1 := hn g hg
          have h2 := Nat.mul_le_mul_left budget (hR X hX g hg)
          omega))
    hcopy

end

end PTX.Kernels.InklingRelDecode.Proof.Bound
