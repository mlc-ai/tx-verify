-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fintype.Prod
public import Core.Async.Tensor.TensorTransfer
public import Lemmas.Tensor.TensorDescriptor
public import Lemmas.Tensor.TensorAddress
public import Lemmas.Tensor.TensorTile

@[expose] public section

namespace PTX.TensorTransfer

theorem slot_card {outer : Nat} (d : TensorDescriptor.Descriptor outer) :
    Fintype.card (Slot d) = bytes d := by
  simp [Slot, bytes, Nat.mul_assoc]

private theorem packed_injective {width x y u v : Nat} (hw : 0 < width)
    (hu : u < width) (hv : v < width) (h : x * width + u = y * width + v) :
    x = y ∧ u = v := by
  have hx := congrArg (fun n => n / width) h
  change (x * width + u) / width = (y * width + v) / width at hx
  rw [Nat.add_comm (x * width) u, Nat.add_comm (y * width) v,
    Nat.add_mul_div_right _ _ hw, Nat.add_mul_div_right _ _ hw,
    Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv, Nat.zero_add, Nat.zero_add] at hx
  subst y
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- Distinct slots of a box have distinct shared bytes. -/
theorem sharedByte_injective {outer : Nat} (d : TensorDescriptor.Descriptor outer) (base : Nat) :
    Function.Injective (fun slot : Slot d => TensorTile.sharedByte d.box d.format.bytes d.swizzle
      base slot.1.val slot.2.1.val slot.2.2.val) := by
  intro a b heq
  have hlin := (TensorTile.sharedByte_eq_iff d.box d.format.bytes d.swizzle base
    a.1.val a.2.1.val a.2.2.val b.1.val b.2.1.val b.2.2.val).mp heq
  have hw := TensorDescriptor.format_bytes_pos d.format
  have ha := a.1.isLt
  have hb := b.1.isLt
  have hu := a.2.2.isLt
  have hv := b.2.2.isLt
  have hp : TensorTile.count d.box 0 * d.format.bytes ≤
      TensorTile.rowBytes d.box d.format.bytes d.swizzle := Nat.le_max_left _ _
  have hpa : a.1.val * d.format.bytes + a.2.2.val <
      TensorTile.rowBytes d.box d.format.bytes d.swizzle := by nlinarith
  have hpb : b.1.val * d.format.bytes + b.2.2.val <
      TensorTile.rowBytes d.box d.format.bytes d.swizzle := by nlinarith
  have hpos : 0 < TensorTile.rowBytes d.box d.format.bytes d.swizzle := by omega
  change a.2.1.val * _ + a.1.val * _ + a.2.2.val =
    b.2.1.val * _ + b.1.val * _ + b.2.2.val at hlin
  rw [Nat.add_assoc, Nat.add_assoc] at hlin
  obtain ⟨hy, hr⟩ := packed_injective hpos hpa hpb hlin
  obtain ⟨hx, hz⟩ := packed_injective hw hu hv hr
  exact Prod.ext (Fin.ext hx) (Prod.ext (Fin.ext hy) (Fin.ext hz))

/-- A descriptor-wide bound from the host API box limits (256 per axis, rank at most 5) and
represented formats. -/
theorem bytes_le_of_valid {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (h : TensorDescriptor.Valid d) : bytes d ≤ 256 ^ 5 * 8 := by
  have h0 := (TensorDescriptor.count_le_box h 0).trans (h.2.2.2.2.1 0).2
  have hr : TensorTile.rows d.box ≤ 256 ^ outer :=
    TensorTile.rowsOf_le outer _ 256 fun i =>
      (TensorDescriptor.count_le_box h i.succ).trans (h.2.2.2.2.1 i.succ).2
  have ho : outer ≤ 4 := by have := h.1; omega
  have hp : 256 ^ outer ≤ 256 ^ 4 := Nat.pow_le_pow_right (by decide) ho
  have hf : d.format.bytes ≤ 8 := by cases d.format <;> decide
  calc bytes d = TensorTile.count d.box 0 * TensorTile.rows d.box * d.format.bytes := rfl
    _ ≤ 256 * 256 ^ 4 * 8 := Nat.mul_le_mul (Nat.mul_le_mul h0 (hr.trans hp)) hf
    _ = 256 ^ 5 * 8 := by norm_num

end PTX.TensorTransfer
