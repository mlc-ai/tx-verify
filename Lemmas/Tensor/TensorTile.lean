-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fin.VecNotation
public import Core.Async.Tensor.TensorTile
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.TensorTile

/-- Enumeration reaches exactly the traversal samples inside the box. -/
theorem index_lt_count_iff {rank : Nat} (b : Box rank) (axis : Fin rank)
    (hs : 0 < step b axis) (index : Nat) :
    index < count b axis ↔ index * step b axis < b.size axis := by
  unfold count
  rw [Nat.lt_div_iff_mul_lt hs]
  omega

/-- Swizzling introduces no aliases between distinct padded-layout byte offsets. -/
theorem sharedByte_eq_iff {outer : Nat} (b : Box (outer + 1)) (elementBytes : Nat)
    (mode : TensorSwizzle.Mode) (base c r u c' r' v : Nat) :
    sharedByte b elementBytes mode base c r u = sharedByte b elementBytes mode base c' r' v ↔
      linearByte b elementBytes mode c r u = linearByte b elementBytes mode c' r' v := by
  unfold sharedByte
  rw [Nat.add_left_cancel_iff]
  exact (TensorSwizzle.offset_injective mode base).eq_iff

theorem indexOf_two (b : Box 2) (c r : Nat) : indexOf b c r = ![c, r] := by
  funext axis; fin_cases axis <;> rfl

/-- With every digit bound at most `B`, there are at most `B ^ k` rows. -/
theorem rowsOf_le : ∀ (k : Nat) (c : Fin k → Nat) (B : Nat), (∀ i, c i ≤ B) → rowsOf k c ≤ B ^ k
  | 0, _, _, _ => by simp [rowsOf]
  | 1, c, B, h => by simpa [rowsOf] using h 0
  | k + 2, c, B, h => by
    have ih := rowsOf_le (k + 1) (fun i => c i.succ) B (fun i => h i.succ)
    calc rowsOf (k + 2) c = c 0 * rowsOf (k + 1) (fun i => c i.succ) := rfl
      _ ≤ B * B ^ (k + 1) := Nat.mul_le_mul (h 0) ih
      _ = B ^ (k + 2) := by ring

/-- Positive digit bounds give a positive row count. -/
theorem rowsOf_pos : ∀ (k : Nat) (c : Fin k → Nat), (∀ i, 0 < c i) → 0 < rowsOf k c
  | 0, _, _ => by simp [rowsOf]
  | 1, c, h => h 0
  | k + 2, c, h => Nat.mul_pos (h 0) (rowsOf_pos (k + 1) (fun i => c i.succ) (fun i => h i.succ))

theorem rows_pos {outer : Nat} {b : Box (outer + 1)} (h : ∀ axis, 0 < count b axis) :
    0 < rows b :=
  rowsOf_pos outer _ fun i => h i.succ

end PTX.TensorTile
