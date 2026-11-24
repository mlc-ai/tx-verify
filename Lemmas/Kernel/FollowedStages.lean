-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed

@[expose] public section

/-! # Every machine is followed, in stages

A proof skeleton, generic over the kernel. When the source of one class of returned values needs
facts about the writers that only a weaker invariant gives (risk R4 of the role-machine plan: a
shared word read by a machine that stops on kinds needs its concurrent writers' footprints), the
reference invariant is proved in stages. Stage `i` has its invariant `J i` and its own order
`r i` with an induction principle; its step may use every earlier stage's invariant at every
followed state of every thread (`followed_stages`). A typical split: stage 0 proves that the
reads of a value class return values of the right kind (so no machine stops, and every write has
the footprint its shape table gives), along an order that contains the reads-from edges of input
bytes only; stage 1 proves the contents along base causality, with the footprints of all writers
from stage 0.

`followedAt_and` combines the stages of one thread into one invariant. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution}

/-- **Two invariants of one thread, followed, are followed together.** -/
theorem followedAt_and {J₁ J₂ : ∀ g, (C g).D → Prop} {g k : Nat}
    (h₁ : FollowedAt C J₁ X g k) (h₂ : FollowedAt C J₂ X g k) :
    FollowedAt C (fun g d => J₁ g d ∧ J₂ g d) X g k :=
  ⟨h₁.1, fun d hd => ⟨h₁.2 d hd, h₂.2 d hd⟩⟩

/-- **Every machine is followed, in stages.** Stage `i` proves its invariant `J i` by `followed`
along its order `r i`; its step may use the invariants of all earlier stages at every state of
every thread. Then every thread whose first state satisfies every stage's invariant is followed,
at states that satisfy every stage's invariant. -/
theorem followed_stages {J : Nat → ∀ g, (C g).D → Prop} {r : Nat → EvId → EvId → Prop}
    (hr : ∀ i, Inductive X (r i)) (h0 : ∀ i g, J i g (C g).init)
    (step : ∀ i g k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) →
      (∀ i' < i, ∀ g' k' d', stateAt C X g' k' = some (some d') → J i' g' d') → J i g d →
      (∀ j, r i j (g, k) → ¬ Bad C (J i) X j) → StepGood C (J i) g d e) :
    ∀ i g k, FollowedAt C (J i) X g k := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro g k
  refine followed (hr i) (fun g k d e he hσ hJ hprev => step i g k d e he hσ ?_ hJ hprev)
    (h0 i g) k
  intro i' hi g' k' d' hd'
  exact (ih i' hi g' k').2 d' hd'

/-- Every stage's invariant at every followed state. -/
theorem followed_stages_all {J : Nat → ∀ g, (C g).D → Prop} {r : Nat → EvId → EvId → Prop}
    (hr : ∀ i, Inductive X (r i)) (h0 : ∀ i g, J i g (C g).init)
    (step : ∀ i g k d e, X.get (g, k) = some e → stateAt C X g k = some (some d) →
      (∀ i' < i, ∀ g' k' d', stateAt C X g' k' = some (some d') → J i' g' d') → J i g d →
      (∀ j, r i j (g, k) → ¬ Bad C (J i) X j) → StepGood C (J i) g d e)
    {g k : Nat} {d : (C g).D} (hd : stateAt C X g k = some (some d)) : ∀ i, J i g d :=
  fun i => (followed_stages hr h0 step i g k).2 d hd

end

end PTX.Frame
