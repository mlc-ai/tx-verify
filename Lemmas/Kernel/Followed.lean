-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.ValuesByOrder

@[expose] public section

/-! # Every machine is followed, by induction on a justification order

A proof skeleton, generic over the kernel. Each thread `g` has a site machine `C g` that may stop
following its thread on a returned value it does not expect (`next d e = some none`). A kernel
gives

* `J g d`: the reference invariant of the followed states of thread `g`;
* an order `r` on the events of the execution with an induction principle (`Inductive X r`);
* `step`: an event fired from a followed state that satisfies `J`, none of whose `r`-predecessors
  is bad, makes a good step (`StepGood`): the machine does not stop, and the successor satisfies
  `J`.

Then no event is bad (`noBad`), and every thread whose first state satisfies `J` is followed at
every state, which satisfies `J` (`followed`). The hypothesis about the predecessors is used
through `followedAt_of_noBad`: a thread none of whose first `n` events is bad is followed, with
`J`, before its `n`-th event.

The never-stops statement uses "no predecessor is bad" rather than "every predecessor is
followed", so the order need not contain program order: program order is not inside base
causality for the elements of one vector access.

Orders with an induction principle: base causality on a consistent execution
(`inductive_causal`), and the order by a measure of the events with the trace position as the
tie-break (`inductive_lex`), such as the number of warp collectives up to an event. A smaller
order inherits the principle (`Inductive.mono`). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Flow.Code K A L g} {X : Execution}

/-- An induction principle on the events of `X` along `r`. -/
def Inductive (X : Execution) (r : EvId → EvId → Prop) : Prop :=
  ∀ Q : EvId → Prop,
    (∀ i e, X.get i = some e → (∀ j e', X.get j = some e' → r j i → Q j) → Q i) →
    ∀ i e, X.get i = some e → Q i

/-- Base causality has an induction principle on the events of a consistent execution. -/
theorem inductive_causal (hX : Consistent L K A mem0 X) : Inductive X (baseCausality L X) :=
  fun Q step => values_by_order hX Q step

/-- The order by a measure, with the position in the trace as the tie-break. -/
def lexOrder (μ : EvId → Nat) (j i : EvId) : Prop :=
  μ j < μ i ∨ (μ j = μ i ∧ j.2 < i.2)

theorem inductive_lex (μ : EvId → Nat) : Inductive X (lexOrder μ) := by
  intro Q step
  have wf : WellFounded (lexOrder μ) := by
    refine Subrelation.wf (r := InvImage (Prod.Lex (· < ·) (· < ·)) fun i : EvId => (μ i, i.2))
      ?_ (InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf))
    intro j i h
    rcases h with h | ⟨h1, h2⟩
    · exact Prod.Lex.left _ _ h
    · show Prod.Lex _ _ (μ j, j.2) (μ i, i.2)
      rw [h1]
      exact Prod.Lex.right _ h2
  intro i
  induction i using wf.induction with
  | h i ih => exact fun e he => step i e he fun j e' he' hr => ih j hr e' he'

/-- A smaller order inherits the induction principle. -/
theorem Inductive.mono {r r' : EvId → EvId → Prop} (h : Inductive X r)
    (hsub : ∀ j i, r' j i → r j i) : Inductive X r' :=
  fun Q step => h Q fun i e he ih => step i e he fun j e' he' hr => ih j e' he' (hsub j i hr)

/-- The machine follows thread `g` before its `k`-th event, at a state that satisfies `J`. -/
def FollowedAt (C : (g : Nat) → Flow.Code K A L g) (J : ∀ g, (C g).D → Prop) (X : Execution)
    (g k : Nat) : Prop :=
  stateAt C X g k ≠ some none ∧ ∀ d, stateAt C X g k = some (some d) → J g d

/-- A good step: the machine does not stop, and the successor satisfies `J`. -/
def StepGood (C : (g : Nat) → Flow.Code K A L g) (J : ∀ g, (C g).D → Prop) (g : Nat)
    (d : (C g).D) (e : Event) : Prop :=
  (C g).next d e ≠ some none ∧ ∀ d', (C g).next d e = some (some d') → J g d'

/-- A bad event: fired from a followed state that satisfies `J`, by a step that is not good. -/
def Bad (C : (g : Nat) → Flow.Code K A L g) (J : ∀ g, (C g).D → Prop) (X : Execution)
    (i : EvId) : Prop :=
  ∃ d e, X.get i = some e ∧ stateAt C X i.1 i.2 = some (some d) ∧ J i.1 d ∧
    ¬ StepGood C J i.1 d e

variable {J : ∀ g, (C g).D → Prop}

/-- **A thread none of whose first `n` events is bad is followed before its `n`-th event.** -/
theorem followedAt_of_noBad {g : Nat} (h0 : J g (C g).init) :
    ∀ n, (∀ j < n, ¬ Bad C J X (g, j)) → FollowedAt C J X g n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by rw [stateAt_zero]; simp, fun d hd => ?_⟩
    rw [stateAt_zero] at hd
    cases hd
    exact h0
  | succ n ih =>
    intro hb
    have hn := ih fun j hj => hb j (by omega)
    by_cases hlen : n < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[n]? = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
      unfold FollowedAt
      rw [stateAt_succ he]
      cases hσ : stateAt C X g n with
      | none =>
        simp only [Option.bind_none]
        exact ⟨(fun h => by cases h), (fun d hd => by cases hd)⟩
      | some σ =>
        cases σ with
        | none => exact absurd hσ hn.1
        | some d =>
          have hgood : StepGood C J g d e := by
            by_contra hbad
            exact hb n (Nat.lt_succ_self n) ⟨d, e, he, hσ, hn.2 d hσ, hbad⟩
          exact ⟨hgood.1, fun d' hd' => hgood.2 d' hd'⟩
    · unfold FollowedAt at hn ⊢
      rw [stateAt_of_le (by omega)]
      rw [stateAt_of_le (by omega)] at hn
      exact hn

/-- **No event is bad** when each event fired from a followed state that satisfies `J` makes a
good step once no `r`-predecessor is bad. -/
theorem noBad {r : EvId → EvId → Prop} (hr : Inductive X r)
    (step : ∀ g k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      (∀ j, r j (g, k) → ¬ Bad C J X j) → StepGood C J g d e) :
    ∀ i, ¬ Bad C J X i := by
  have claim := hr (fun i => ¬ Bad C J X i) fun i e he ih => by
    rintro ⟨d, e', he', hσ, hJ, hbad⟩
    refine hbad (step i.1 i.2 d e' he' hσ hJ fun j hj hB => ?_)
    obtain ⟨_, ej, hej, -⟩ := id hB
    exact ih j ej hej hj hB
  intro i hB
  obtain ⟨_, e, he, -⟩ := id hB
  exact claim i e he hB

/-- **Every machine is followed, at states that satisfy `J`.** -/
theorem followed {r : EvId → EvId → Prop} (hr : Inductive X r)
    (step : ∀ g k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      (∀ j, r j (g, k) → ¬ Bad C J X j) → StepGood C J g d e) {g : Nat}
    (h0 : J g (C g).init) (k : Nat) : FollowedAt C J X g k :=
  followedAt_of_noBad h0 k fun j _ => noBad hr step (g, j)

/-- The machines follow every launched thread. -/
theorem tracked_of_followed {r : EvId → EvId → Prop} (hr : Inductive X r)
    (h0 : ∀ g < L.threads, J g (C g).init)
    (step : ∀ g k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      (∀ j, r j (g, k) → ¬ Bad C J X j) → StepGood C J g d e) : Tracked C X :=
  fun g k hg => (followed hr step (h0 g hg) k).1

/-- With the order by a measure: a thread is followed through every event of smaller measure.
This is the form in which `step` uses its hypothesis about the predecessors of a warp
collective. -/
theorem followedAt_of_lex {μ : EvId → Nat} {i : EvId}
    (hprev : ∀ j, lexOrder μ j i → ¬ Bad C J X j) {h n : Nat} (h0 : J h (C h).init)
    (hn : ∀ j < n, μ (h, j) < μ i) : FollowedAt C J X h n :=
  followedAt_of_noBad h0 n fun j hj => hprev (h, j) (.inl (hn j hj))

/-- With the order by a measure that does not decrease along a thread: the thread of an event is
followed before the event. -/
theorem followedAt_self {μ : EvId → Nat} (hmono : ∀ g j j', j ≤ j' → μ (g, j) ≤ μ (g, j'))
    {g k : Nat} (h0 : J g (C g).init) (hprev : ∀ j, lexOrder μ j (g, k) → ¬ Bad C J X j) :
    FollowedAt C J X g k :=
  followedAt_of_noBad h0 k fun j hj => hprev (g, j) (by
    rcases Nat.lt_or_eq_of_le (hmono g j k (Nat.le_of_lt hj)) with h | h
    · exact .inl h
    · exact .inr ⟨h, hj⟩)

/-- **Every machine of a thread in `Q` is followed, at states that satisfy `J`**, when each
event of such a thread fired from a followed state that satisfies `J` makes a good step once no
`r`-predecessor in a thread of `Q` is bad (promoted from the tml-fa4 output warp's proof). The
form a kernel uses while some roles are stubs that stop at their first event: `Q` selects the
threads of the migrated roles, whose sources lie among themselves. -/
theorem followedOn {Q : Nat → Prop} {r : EvId → EvId → Prop} (hr : Inductive X r)
    (h0 : ∀ g, Q g → J g (C g).init)
    (step : ∀ g k d e, Q g → X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      (∀ j, r j (g, k) → Q j.1 → ¬ Bad C J X j) → StepGood C J g d e)
    {g : Nat} (hg : Q g) (k : Nat) : FollowedAt C J X g k := by
  have claim := hr (fun i => Q i.1 → ¬ Bad C J X i) fun i e he ih hQ => by
    rintro ⟨d, e', he', hσ, hJ, hbad⟩
    refine hbad (step i.1 i.2 d e' hQ he' hσ hJ fun j hj hQj hB => ?_)
    obtain ⟨_, ej, hej, -⟩ := id hB
    exact ih j ej hej hj hQj hB
  refine followedAt_of_noBad (h0 g hg) k fun j _ hB => ?_
  obtain ⟨_, e, he, -⟩ := id hB
  exact claim (g, j) e he hg hB

/-- With the order by a measure: a thread of `Q` is followed through every event of smaller
measure than `i`. -/
theorem followedAtOn_of_lex {Q : Nat → Prop} {μ : EvId → Nat} {i : EvId}
    (hprev : ∀ j, lexOrder μ j i → Q j.1 → ¬ Bad C J X j) {h n : Nat} (hQ : Q h)
    (h0 : J h (C h).init) (hn : ∀ j < n, μ (h, j) < μ i) : FollowedAt C J X h n :=
  followedAt_of_noBad h0 n fun j hj => hprev (h, j) (.inl (hn j hj)) hQ

end

end PTX.Frame
