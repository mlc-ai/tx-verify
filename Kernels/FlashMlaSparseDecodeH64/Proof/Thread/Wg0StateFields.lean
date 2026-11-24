-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch

public section

/-! # Block and element positions across numerical updates -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow

/-- The peer maximum changes neither the block index nor its element. -/
theorem peer_preserves_sub {L : Launch} {d d' : Wg0.D} {v : Value}
    (h : Wg0.withPeerMax L d v = some d') : d'.block = d.block ∧ d'.sub = d.sub := by
  unfold Wg0.withPeerMax at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, rfl⟩

/-- The reference vote changes neither the block index nor its element. -/
theorem vote_preserves_sub {d d' : Wg0.D} {b : Bool}
    (h : Wg0.afterReferenceVote d b = some d') : d'.block = d.block ∧ d'.sub = d.sub := by
  rw [Wg0.afterReferenceVote_fields h]
  exact ⟨rfl, rfl⟩

/-- The probability update changes neither the block index nor its element. -/
theorem probability_preserves_sub {L : Launch} {g : Nat} {d d' : Wg0.D}
    (h : Wg0.probabilityUpdate L g d = some d') : d'.block = d.block ∧ d'.sub = d.sub := by
  simp only [Wg0.probabilityUpdate, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
