-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Earlier events of a followed thread -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.FollowedPrefix

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch}
variable {C : (g : Nat) → Flow.Code K A L g} {X : Execution} {g k n : Nat}

private theorem after_dismissed (c : Flow.Code K A L g) (events : List Event) :
    c.toMachine.after none events = some none := by
  induction events with
  | nil => rfl
  | cons e events ih => exact ih

/-- After a thread's machine is dismissed, it never returns to a followed state. -/
theorem dismissed_mono (h : Frame.stateAt C X g k = some none) (hk : k ≤ n) :
    Frame.stateAt C X g n = some none := by
  have hsplit := List.take_append_drop k ((X.tr g).take n)
  rw [List.take_take, Nat.min_eq_left hk] at hsplit
  unfold Frame.stateAt at h ⊢
  rw [← hsplit, (C g).toMachine.after_append (some (C g).init) _ _, h]
  exact after_dismissed _ _

/-- A followed state implies that every earlier prefix of that thread is followed. -/
theorem state_at {d : (C g).D}
    (hd : Frame.stateAt C X g n = some (some d)) (hk : k ≤ n) :
    ∃ q, Frame.stateAt C X g k = some (some q) := by
  cases hq : Frame.stateAt C X g k with
  | none => rw [Frame.stateAt_none_mono hq hk] at hd; cases hd
  | some s =>
    cases s with
    | none => rw [dismissed_mono hq hk] at hd; cases hd
    | some q => exact ⟨q, rfl⟩

/-- A real event strictly before a followed state has a followed source and successor. -/
theorem step_at {d : (C g).D} {e : Event}
    (hd : Frame.stateAt C X g n = some (some d)) (hk : k < n)
    (he : X.get (g, k) = some e) :
    ∃ q r, Frame.stateAt C X g k = some (some q) ∧
      Frame.stateAt C X g (k + 1) = some (some r) ∧ (C g).next q e = some (some r) := by
  obtain ⟨q, hq⟩ := state_at hd hk.le
  obtain ⟨r, hr⟩ := state_at hd hk
  refine ⟨q, r, hq, hr, ?_⟩
  rw [Frame.stateAt_succ he, hq, Option.bind_some] at hr
  exact hr

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.FollowedPrefix
