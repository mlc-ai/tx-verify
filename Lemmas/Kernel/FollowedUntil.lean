-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed

@[expose] public section

/-! # Followed up to a stub

A proof tool, generic over the kernel. `Frame.followed` asks every state satisfying `J` to step
without stopping. A thread whose migrated fragment ends in a stub (a role not migrated yet, which
stops at its first event: the Inkling prologue's lanes reach the softmax stub) does stop there.
Here the states of a set `S` (the stubs' states) owe nothing: a thread is followed, with `J`, at
every position before which it has not been at a state of `S` (`followedUntil`), and `J` may
include `S` so that the stub's own state is reached with `J`. The order and the source obligation
are those of `followed` (`BadS`: a bad event outside `S`); `followedUntilOn` restricts to the
threads `Q`, as `followedOn`. Once the stub's role is migrated, `S` shrinks to nothing and the
statements are `followed`'s. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Flow.Code K A L g} {J S : ∀ g, (C g).D → Prop}

/-- A bad event outside `S`: fired from a followed state that satisfies `J` and is not in `S`, by a
step that is not good. -/
def BadS (C : (g : Nat) → Flow.Code K A L g) (J S : ∀ g, (C g).D → Prop) (X : Execution)
    (i : EvId) : Prop :=
  ∃ d e, X.get i = some e ∧ stateAt C X i.1 i.2 = some (some d) ∧ J i.1 d ∧ ¬ S i.1 d ∧
    ¬ StepGood C J i.1 d e

/-- The thread has not been at a state of `S` before position `k`. -/
def Before (C : (g : Nat) → Flow.Code K A L g) (S : ∀ g, (C g).D → Prop) (X : Execution)
    (g k : Nat) : Prop :=
  ∀ j < k, ∀ d, stateAt C X g j = some (some d) → ¬ S g d

/-- **A thread none of whose first `n` events is bad outside `S` is followed before its `n`-th
event, when it has not been at a state of `S` before.** -/
theorem followedAt_of_noBadS {g : Nat} (h0 : J g (C g).init) :
    ∀ n, (∀ j < n, ¬ BadS C J S X (g, j)) → Before C S X g n → FollowedAt C J X g n := by
  intro n
  induction n with
  | zero =>
    intro _ _
    refine ⟨by rw [stateAt_zero]; simp, fun d hd => ?_⟩
    rw [stateAt_zero] at hd
    cases hd
    exact h0
  | succ n ih =>
    intro hb hS
    have hn := ih (fun j hj => hb j (by omega)) (fun j hj => hS j (by omega))
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
            exact hb n (Nat.lt_succ_self n)
              ⟨d, e, he, hσ, hn.2 d hσ, hS n (Nat.lt_succ_self n) d hσ, hbad⟩
          exact ⟨hgood.1, fun d' hd' => hgood.2 d' hd'⟩
    · unfold FollowedAt at hn ⊢
      rw [stateAt_of_le (by omega)]
      rw [stateAt_of_le (by omega)] at hn
      exact hn

/-- **Every machine of a thread in `Q` is followed, at states that satisfy `J`, up to the first
state of `S`**, when each event of such a thread fired from a followed state that satisfies `J`
and is not in `S` makes a good step once no `r`-predecessor in a thread of `Q` is bad outside
`S`. -/
theorem followedUntilOn {Q : Nat → Prop} {r : EvId → EvId → Prop} (hr : Inductive X r)
    (h0 : ∀ g, Q g → J g (C g).init)
    (step : ∀ g k d e, Q g → X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      ¬ S g d → (∀ j, r j (g, k) → Q j.1 → ¬ BadS C J S X j) → StepGood C J g d e)
    {g : Nat} (hg : Q g) (k : Nat) (hS : Before C S X g k) : FollowedAt C J X g k := by
  have claim := hr (fun i => Q i.1 → ¬ BadS C J S X i) fun i e he ih hQ => by
    rintro ⟨d, e', he', hσ, hJ, hnS, hbad⟩
    refine hbad (step i.1 i.2 d e' hQ he' hσ hJ hnS fun j hj hQj hB => ?_)
    obtain ⟨_, ej, hej, -⟩ := id hB
    exact ih j ej hej hj hQj hB
  refine followedAt_of_noBadS (h0 g hg) k (fun j _ hB => ?_) hS
  obtain ⟨_, e, he, -⟩ := id hB
  exact claim (g, j) e he hg hB

/-- **Every machine is followed, at states that satisfy `J`, up to the first state of `S`.** -/
theorem followedUntil {r : EvId → EvId → Prop} (hr : Inductive X r)
    (h0 : ∀ g, J g (C g).init)
    (step : ∀ g k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) → J g d →
      ¬ S g d → (∀ j, r j (g, k) → ¬ BadS C J S X j) → StepGood C J g d e)
    (g k : Nat) (hS : Before C S X g k) : FollowedAt C J X g k :=
  followedUntilOn (Q := fun _ => True) hr (fun g _ => h0 g)
    (fun g k d e _ he hσ hJ hnS hpre => step g k d e he hσ hJ hnS fun j hj => hpre j hj trivial)
    trivial k hS

/-- With no stub states (`S` empty), every position is before one. -/
theorem before_of_empty {g k : Nat} (h : ∀ g d, ¬ S g d) : Before C S X g k :=
  fun _ _ d _ => h g d

end PTX.Frame
