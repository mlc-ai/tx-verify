-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
public import Lemmas.Protocol.RingIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.MmaReady
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy
open Thread.Mma
open Thread.Mma.Observation (readyObject emptyObject)

noncomputable section

/-- Number of completed uses of this physical slot before logical use `use`. -/
def priorUses (use : Nat) (slot : Fin 3) : Nat :=
  (use + (2 - slot.val)) / 3

/-- The physical slot addressed by the logical next use. -/
def nextSlot (use : Nat) : Fin 3 :=
  ⟨Index.slot 3 use, Nat.mod_lt _ (by decide)⟩

/-- The next use requests the parity of its own slot's generation. -/
def nextParity (use : Nat) : Nat :=
  Index.round 3 use % 2

/-- The lane has consumed the first `use` entries of the rotating K/V ring. -/
def Cursor (d : D) (use : Nat) : Prop :=
  ∀ i, d.kvAcquires i = priorUses use i

theorem initialCursor : Cursor initial 0 := by
  intro i
  fin_cases i <;> decide

private theorem priorUses_next (use : Nat) (i : Fin 3) :
    priorUses (use + 1) i = priorUses use i + if nextSlot use = i then 1 else 0 := by
  have hSlot (i : Fin 3) : nextSlot use = i ↔ use % 3 = i.val :=
    ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  simp only [hSlot]
  fin_cases i <;> simp only [priorUses] <;> split <;> omega

/-- The currently addressed slot's successful-poll ordinal is the ring round. -/
theorem Cursor.round {d : D} {use : Nat} (h : Cursor d use) :
    d.kvAcquires (nextSlot use) = Index.round 3 use := by
  rw [h]
  change (use + (2 - use % 3)) / 3 = use / 3
  omega

/-- An actual successful poll of the next slot advances every per-slot ordinal correctly. -/
theorem Cursor.advance {l : Launch} {X : Execution} {g index use parity : Nat}
    {acquire : Bool} {scope : MbarScope}
    (h : Cursor (atPrefix l X g index) use)
    (hPoll : ReadyPoll l X g index (nextSlot use) parity acquire scope) :
    Cursor (atPrefix l X g (index + 1)) (use + 1) := by
  intro i
  rw [hPoll.stepSlots, h i, priorUses_next]

/-- Operand order and parity for every successful ready poll observed by this lane. -/
def FollowsRing (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ index slot parity acquire scope, ReadyPoll l X g index slot parity acquire scope →
    ∃ use, Cursor (atPrefix l X g index) use ∧ slot = nextSlot use ∧ parity = nextParity use

/-- Ring order gives the per-slot alternating parity required by the object history. -/
theorem FollowsRing.alternates {l : Launch} {X : Execution} {g : Nat}
    (h : FollowsRing l X g) {index parity : Nat} {slot : Fin 3} {acquire : Bool}
    {scope : MbarScope} (hPoll : ReadyPoll l X g index slot parity acquire scope) :
    parity % 2 = (atPrefix l X g index).kvAcquires slot % 2 := by
  obtain ⟨use, hCursor, rfl, rfl⟩ := h _ _ _ _ _ hPoll
  rw [hCursor.round]
  simp [nextParity]

end
end PTX.Kernels.TmlFa4Fwd.Protocol.MmaReady
