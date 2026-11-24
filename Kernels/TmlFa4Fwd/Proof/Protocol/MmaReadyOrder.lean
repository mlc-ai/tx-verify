-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.MmaReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.MmaReady
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy Thread.Mma
open Thread.Mma.Observation (readyObject)

noncomputable section

/-- The next logical use is the sum of the observations across the three slots. -/
def uses (d : D) : Nat :=
  d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2

theorem Cursor.uses_eq {d : D} {use : Nat} (h : Cursor d use) : uses d = use := by
  unfold uses
  rw [h 0, h 1, h 2]
  change (use + 2) / 3 + (use + 1) / 3 + use / 3 = use
  omega

/-- The actual success events name the successive physical slots and request their round parity. -/
def FollowsOperands (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ index slot parity acquire scope, ReadyPoll l X g index slot parity acquire scope →
    let use := uses (atPrefix l X g index)
    slot = nextSlot use ∧ parity = nextParity use

/-- The whole abstract ring counter invariant follows from observed operand order alone. -/
theorem FollowsOperands.cursor {l : Launch} {X : Execution} {g : Nat}
    (h : FollowsOperands l X g) (index : Nat) :
    Cursor (atPrefix l X g index) (uses (atPrefix l X g index)) := by
  classical
  induction index with
  | zero =>
    have hZero : atPrefix l X g 0 = initial := rfl
    rw [hZero, initialCursor.uses_eq]
    exact initialCursor
  | succ index ih =>
    by_cases hPoll : ∃ slot parity acquire scope, ReadyPoll l X g index slot parity acquire scope
    · obtain ⟨slot, parity, acquire, scope, hPoll⟩ := hPoll
      obtain ⟨hSlot, _⟩ := h _ _ _ _ _ hPoll
      rw [hSlot] at hPoll
      have hNext := ih.advance hPoll
      rw [hNext.uses_eq]
      exact hNext
    · push Not at hPoll
      have hSame := readyCountsUnchanged hPoll
      have hUses : uses (atPrefix l X g (index + 1)) = uses (atPrefix l X g index) := by
        simp only [uses, hSame]
      rw [hUses]
      intro i
      exact (hSame i).trans (ih i)

theorem FollowsOperands.followsRing {l : Launch} {X : Execution} {g : Nat}
    (h : FollowsOperands l X g) : FollowsRing l X g := by
  intro index slot parity acquire scope hPoll
  exact ⟨uses (atPrefix l X g index), h.cursor index, h _ _ _ _ _ hPoll⟩

end
end PTX.Kernels.TmlFa4Fwd.Protocol.MmaReady
