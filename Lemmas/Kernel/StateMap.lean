-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
public import Lemmas.Flow.Counted

@[expose] public section

/-! # Following along a map of machine states

A proof tool, generic over the kernel (Inkling request L-i). Two machine families `C'` and `C`
for the same kernel, and a map `φ g` from the states of `C' g` to those of `C g` that sends the
first state to the first state and commutes with the successor (`StepMap`: a stop or a death of
one is the other's, a successor maps to the successor). Then the state of `C` after any prefix
of a trace is the image of the state of `C'` (`stateAt_map`), and a thread that `C'` follows with
an invariant `J'` is followed by `C` with the image of `J'` (`followedAt_map`). A kernel that
rebuilds a role as a new machine and keeps facts proved about an old machine's states (its old
thread layer) reuses those facts at the image states, without the old machine's own following
proof. Forgetting a ghost ledger is one such map (`StepMap.counted`). -/

namespace PTX.Frame

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch}

/-- **A step map** from the states of `C'` to those of `C`: the first state to the first state,
and every successor (a stop, a death or a state) to the corresponding one. -/
structure StepMap (C' C : (g : Nat) → Code K A L g) (φ : ∀ g, (C' g).D → (C g).D) : Prop where
  init : ∀ g, φ g (C' g).init = (C g).init
  next : ∀ g d e, ((C' g).next d e).map (Option.map (φ g)) = (C g).next (φ g d) e

variable {C' C : (g : Nat) → Code K A L g} {φ : ∀ g, (C' g).D → (C g).D}

theorem StepMap.after (h : StepMap C' C φ) (g : Nat) (σ : Option (C' g).D) (es : List Event) :
    ((C' g).toMachine.after σ es).map (Option.map (φ g)) =
      (C g).toMachine.after (σ.map (φ g)) es := by
  induction es generalizing σ with
  | nil => rfl
  | cons e es ih =>
    cases σ with
    | none =>
      change (((C' g).toMachine.next none e).bind fun σ' => (C' g).toMachine.after σ' es).map
          (Option.map (φ g)) =
        ((C g).toMachine.next none e).bind fun σ' => (C g).toMachine.after σ' es
      exact ih none
    | some d =>
      change (((C' g).next d e).bind fun σ' => (C' g).toMachine.after σ' es).map
          (Option.map (φ g)) =
        ((C g).next (φ g d) e).bind fun σ' => (C g).toMachine.after σ' es
      rw [← h.next g d e]
      cases (C' g).next d e with
      | none => rfl
      | some o => exact ih o

/-- **The state of `C` is the image of the state of `C'`** after every prefix of a trace. -/
theorem stateAt_map (h : StepMap C' C φ) (X : Execution) (g k : Nat) :
    (stateAt C' X g k).map (Option.map (φ g)) = stateAt C X g k := by
  unfold stateAt
  rw [h.after g (some (C' g).init)]
  change (C g).toMachine.after (some (φ g (C' g).init)) _ = _
  rw [h.init g]

/-- The image of a state of `C'` is the state of `C`. -/
theorem stateAt_map_some (h : StepMap C' C φ) {X : Execution} {g k : Nat} {d : (C' g).D}
    (hd : stateAt C' X g k = some (some d)) : stateAt C X g k = some (some (φ g d)) := by
  rw [← stateAt_map h X g k, hd]
  rfl

/-- **A thread followed by `C'` with `J'` is followed by `C` with the image of `J'`.** -/
theorem followedAt_map (h : StepMap C' C φ) {J' : ∀ g, (C' g).D → Prop} {X : Execution}
    {g k : Nat} (hf : FollowedAt C' J' X g k) :
    FollowedAt C (fun g d => ∃ d', φ g d' = d ∧ J' g d') X g k := by
  have hm := stateAt_map h X g k
  refine ⟨fun hn => ?_, fun d hd => ?_⟩
  · rw [hn] at hm
    cases hs : stateAt C' X g k with
    | none => rw [hs] at hm; cases hm
    | some o =>
      cases o with
      | none => exact hf.1 hs
      | some d' => rw [hs] at hm; cases hm
  · rw [hd] at hm
    cases hs : stateAt C' X g k with
    | none => rw [hs] at hm; cases hm
    | some o =>
      cases o with
      | none => rw [hs] at hm; cases hm
      | some d' =>
        rw [hs] at hm
        simp only [Option.map_some, Option.some.injEq] at hm
        exact ⟨d', hm, hf.2 d' hs⟩

/-- **Forgetting a ghost ledger is a step map** (`Code.counted`): a thread followed by the counted
machine is followed by the machine itself. -/
theorem StepMap.counted (C : (g : Nat) → Code K A L g) {κ : Type}
    (cls : Nat → κ → Event → Bool) :
    StepMap (fun g => (C g).counted (cls g)) C (fun _ d => d.1) where
  init _ := rfl
  next g d e := by
    change (((C g).next d.1 e).map (Option.map fun d' => (d', Code.bump (cls g) d.2 e))).map
      (Option.map Prod.fst) = _
    cases (C g).next d.1 e with
    | none => rfl
    | some o => cases o <;> rfl

end PTX.Frame
