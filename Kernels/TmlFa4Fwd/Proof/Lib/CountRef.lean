-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section

/-! # A fact about a followed lane's state and the number of its earlier events of a class -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {X : Execution} {g : Nat}

/-- **A predicate of a lane's state and of a count of its earlier events, kept by its steps, holds
at all its states.** -/
theorem countRef {J : (g : Nat) → (thread p L g).D → Prop}
    (hG : ∀ k, Frame.FollowedAt (thread p L) J X g k) (c : Event → Bool)
    {P : (thread p L g).D → Nat → Prop} (h0 : P (thread p L g).init 0)
    (hstep : ∀ k d e d' n, X.get (g, k) = some e →
      Frame.stateAt (thread p L) X g k = some (some d) → J g d → P d n →
      (thread p L g).next d e = some (some d') → J g d' → P d' (n + if c e then 1 else 0)) :
    ∀ k d, Frame.stateAt (thread p L) X g k = some (some d) →
      P d (((X.tr g).take k).countP c) := by
  intro k
  induction k with
  | zero =>
    intro d hd
    rw [Frame.stateAt_zero] at hd
    cases hd
    simpa using h0
  | succ k ih =>
    intro d hd
    cases he : (X.tr g)[k]? with
    | none =>
      have hle : (X.tr g).length ≤ k := by simpa using he
      rw [Frame.stateAt_of_le (by omega)] at hd
      have h := ih d (by rw [Frame.stateAt_of_le hle]; exact hd)
      rw [List.take_of_length_le (by omega)] at h ⊢
      exact h
    | some e =>
      have hd' := hd
      rw [Frame.stateAt_succ he] at hd
      cases hs : Frame.stateAt (thread p L) X g k with
      | none => rw [hs] at hd; cases hd
      | some σ =>
        cases σ with
        | none => exact absurd hs (hG k).1
        | some d0 =>
          rw [hs] at hd
          have h := hstep k d0 e d _ he hs ((hG k).2 _ hs) (ih d0 hs) hd ((hG (k + 1)).2 d hd')
          rw [List.take_add_one, he, List.countP_append]
          simpa [List.countP_cons] using h

end PTX.Kernels.TmlFa4Fwd.Proof
