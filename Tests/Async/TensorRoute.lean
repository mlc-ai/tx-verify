-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.CtaPair

/-! Completion routing of 2D tensor copies (PROG-CTA-GROUP) in a cluster of four CTAs:
cta_group::2 completes on the destination's pair, never on another pair or cluster. -/
namespace PTX.Tests.TensorRoute

private def L : Launch := { grid := 8, block := 128, params := fun _ => none, clusterSize := 4 }
private def sm (cta addr : Nat) : Loc := ⟨.shared, cta, addr⟩

-- The production pattern: the peer CTA loads its own half and signals the leader's barrier.
example : TensorRoute L 1 true .two (sm 1 1024) (sm 0 64) := by decide
-- The leader may also load into the peer and signal its own barrier.
example : TensorRoute L 0 true .two (sm 1 1024) (sm 0 64) := by decide
-- Routing follows the destination's pair, which need not contain the issuer.
example : TensorRoute L 0 true .two (sm 3 1024) (sm 2 64) := by decide
-- A barrier in another pair of the same cluster is not a completion target.
example : ¬ TensorRoute L 1 true .two (sm 1 1024) (sm 2 64) := by decide
-- cta_group::1 completes only on the destination's own CTA.
example : ¬ TensorRoute L 1 true .one (sm 1 1024) (sm 0 64) := by decide
example : TensorRoute L 1 true .one (sm 0 1024) (sm 0 64) := by decide
-- shared::cta addressing keeps both locations in the issuer's CTA.
example : ¬ TensorRoute L 1 false .two (sm 1 1024) (sm 0 64) := by decide
example : TensorRoute L 1 false .two (sm 1 1024) (sm 1 64) := by decide
-- Nothing crosses the cluster boundary (CTAs 4–7 form the next cluster).
example : ¬ TensorRoute L 3 true .two (sm 4 1024) (sm 5 64) := by decide
example : ¬ TensorRoute L 5 true .two (sm 4 1024) (sm 5 64) → False := by
  intro h; exact h (by decide)
-- Global memory is never a destination or barrier.
example : ¬ TensorRoute L 0 true .two ⟨.global, 0, 1024⟩ (sm 0 64) := by decide
-- An invalid cluster configuration admits no route at all.
example : ¬ TensorRoute { L with grid := 6 } 0 true .two (sm 0 1024) (sm 0 64) := by decide

end PTX.Tests.TensorRoute
