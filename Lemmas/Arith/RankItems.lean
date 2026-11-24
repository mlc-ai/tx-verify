-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Arith.FastDivmod

@[expose] public section

/-! # Ranks over a count of items

A rank that counts down the items a role has left gives each item a block of `Q` (`Q * (B - i)`
for item `i` of `B`). Moving to the next item, guarded by `i + 1 < B`, frees one block, so any
in-item position below the block (`x < Q + y`) is a decrease (`item_step`). A static persistent
worker has at most as many items as there are in all (`StaticSchedule.count_le`). -/

namespace PTX.RankItems

/-- **Moving to the next item lowers the rank** by more than the new position's excess over the
old one, when that excess is below a block. -/
theorem item_step {Q B i x y : Nat} (h : i + 1 < B) (hx : x < Q + y) :
    Q * (B - (i + 1)) + x < Q * (B - i) + y := by
  have hb : B - i = B - (i + 1) + 1 := by omega
  rw [hb, Nat.mul_add, Nat.mul_one]
  omega

/-- One block more before item `i` than before item `i + 1`. -/
theorem mul_sub_succ (Q : Nat) {B i : Nat} (h : i + 1 < B) :
    Q * (B - i) = Q * (B - (i + 1)) + Q := by
  have hb : B - i = B - (i + 1) + 1 := by omega
  rw [hb, Nat.mul_add, Nat.mul_one]

/-- Item `i` of `B` takes at most `B` blocks of `Q`. -/
theorem mul_sub_le (Q B i : Nat) : Q * (B - i) ≤ Q * B :=
  Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end PTX.RankItems

namespace StaticSchedule

/-- A worker has at most as many items as there are in all. -/
theorem count_le (G T c : Nat) : count G T c ≤ T := by
  unfold count
  rcases Nat.eq_zero_or_pos G with rfl | hG
  · simp
  · rw [Nat.div_le_iff_le_mul_add_pred hG]
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · omega
    · have : T ≤ G * T := Nat.le_mul_of_pos_left T hG
      omega

end StaticSchedule
