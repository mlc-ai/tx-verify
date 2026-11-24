-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.Ring
public import Core.Async.Tensor.TensorMemory
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Where a 64-column FP16 box with 128-byte swizzle writes

A proof tool (generalizing the production GEMM's `box_writeLoc` to any rank and row count). A
tensor load whose box has 64 FP16 columns per row (128-byte rows) and 128-byte swizzle writes
byte `byte` of element `(x, y)` at `base + offset .b128 base (128 y + 2 x + byte)` of its shared
destination (`box_writeLoc`). A written slot is in the box (`writeLoc_bounds`). Every byte of
the destination's `128 R` bytes is written by exactly one slot of an `R`-row box
(`box_writeLoc_surj`, `box_offset_inj`), and each slot's byte lies in them
(`box_offset_lt`). -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- **Where a 64-column FP16, 128-byte-swizzled box writes element `(x, y)`, byte `byte`.** -/
theorem box_writeLoc {s : Spec} {R x y byte : Nat}
    (h0 : TensorTile.count s.descriptor.box 0 = 64) (hR : TensorTile.rows s.descriptor.box = R)
    (hf : s.descriptor.format = .f16) (hsw : s.descriptor.swizzle = .b128)
    (hx : x < 64) (hy : y < R) (hb : byte < 2) :
    writeLoc s x y byte = some { s.sharedBase with
      addr := s.sharedBase.addr +
        TensorSwizzle.offset .b128 s.sharedBase.addr (128 * y + 2 * x + byte) } := by
  have hfb : s.descriptor.format.bytes = 2 := by rw [hf]; rfl
  unfold writeLoc TensorTransfer.slotAt
  rw [dite_eq_left (show x < TensorTile.count s.descriptor.box 0 by omega),
    dite_eq_left (show y < TensorTile.rows s.descriptor.box by omega),
    dite_eq_left (show byte < s.descriptor.format.bytes by omega), Option.map_some]
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, h0, hfb, hsw, TensorTile.swizzleWidth]
  rw [show y * max (64 * 2) 128 + x * 2 + byte = 128 * y + 2 * x + byte by
    simp only [Nat.reduceMul, max_self]; ring]

/-- A slot a tensor load writes is in its box. -/
theorem writeLoc_bounds {s : Spec} {x y byte : Nat} {l : Loc} (h : writeLoc s x y byte = some l) :
    x < TensorTile.count s.descriptor.box 0 ∧ y < TensorTile.rows s.descriptor.box ∧
      byte < s.descriptor.format.bytes := by
  unfold writeLoc TensorTransfer.slotAt at h
  by_cases hx : x < TensorTile.count s.descriptor.box 0
  · by_cases hy : y < TensorTile.rows s.descriptor.box
    · by_cases hb : byte < s.descriptor.format.bytes
      · exact ⟨hx, hy, hb⟩
      · simp [hx, hy, hb] at h
    · simp [hx, hy] at h
  · simp [hx] at h

/-- Each slot of an `R`-row box lies in the destination's first `128 R` bytes. -/
theorem box_offset_lt {base R x y byte : Nat} (hx : x < 64) (hy : y < R) (hb : byte < 2) :
    TensorSwizzle.offset .b128 base (128 * y + 2 * x + byte) < 128 * R := by
  have h := TensorSwizzle.offset_row .b128 base (128 * y + 2 * x + byte)
  have : (128 * y + 2 * x + byte) / 128 = y := by omega
  omega

/-- Distinct slots of a box write distinct bytes. -/
theorem box_offset_inj {base x y byte x' y' byte' : Nat} (hx : x < 64) (hb : byte < 2)
    (hx' : x' < 64) (hb' : byte' < 2)
    (h : TensorSwizzle.offset .b128 base (128 * y + 2 * x + byte) =
      TensorSwizzle.offset .b128 base (128 * y' + 2 * x' + byte')) :
    x = x' ∧ y = y' ∧ byte = byte' := by
  have := TensorSwizzle.offset_injective .b128 base h
  omega

/-- **Every byte of the destination's first `128 R` bytes is written by a slot.** -/
theorem box_writeLoc_surj {base R off : Nat} (ho : off < 128 * R) :
    ∃ x y byte, x < 64 ∧ y < R ∧ byte < 2 ∧
      TensorSwizzle.offset .b128 base (128 * y + 2 * x + byte) = off := by
  set o := TensorSwizzle.offset .b128 base off with hodef
  have hr := TensorSwizzle.offset_row .b128 base off
  refine ⟨o % 128 / 2, o / 128, o % 2, by omega, by omega, by omega, ?_⟩
  rw [show 128 * (o / 128) + 2 * (o % 128 / 2) + o % 2 = o by omega, hodef,
    TensorSwizzle.offset_involutive]

end PTX.TensorCopy
