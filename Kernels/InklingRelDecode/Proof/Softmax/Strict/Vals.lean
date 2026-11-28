-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Span
import Kernels.InklingRelDecode.Proof.Lib.MmaBits
@[expose] public section
/-! # More closers of the exact pieces of the softmax's control stretches
`late_vals2` is `late_vals` with the poll address of the loop (pcs 1251 to 1256). -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow
set_option maxRecDepth 100000

theorem trunc_lit (z : Int) (h0 : 0 ≤ z) (h : z < 2 ^ 32) :
    truncBits 32 (BitVec.ofInt 64 z) = BitVec.ofNat 64 z.toNat := by
  simp only [truncBits, BitVec.toNat_ofInt]
  congr 1
  omega

theorem val_504 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 504 = b32 (d.i % 2) := by
  simp [Control.valueOf, Control.scalarValue]

theorem val_505 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 505 = Control.u32 (L.sharedBase + d.i % 2 * 8) := by
  simp [Control.valueOf, Control.scalarValue]

theorem val_874 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 874 = Control.u32 (L.sharedBase + d.i % 2 * 8 + 213280) := by
  simp [Control.valueOf, Control.scalarValue]

theorem val_875 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 875 = b32 (d.i / 2 % 2) := by
  simp [Control.valueOf, Control.scalarValue]

theorem and1_val (i : Nat) : Value.bits 32 (truncBits 32 (truncBits 32 (truncBits 64
    (BitVec.ofNat 64 i))) &&& truncBits 32 (BitVec.ofInt 64 1)) = b32 (i % 2) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
  simp only [truncBits, BitVec.toNat_and, BitVec.toNat_ofNat, h1]
  have e1 : i % 2 ^ 64 % 2 ^ 64 % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 = i % 2 ^ 32 := by
    omega
  have e2 : 1 % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 = 1 := by norm_num
  rw [e1, e2, Nat.and_one_is_mod]
  omega

theorem inner_505 (sb i : Nat) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (sb % 2 ^ 32)) + truncBits 32 (if (truncBits 32
      (BitVec.ofInt 64 3)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32 (truncBits 32
      (truncBits 32 (truncBits 64 (BitVec.ofNat 64 i))) &&& truncBits 32 (BitVec.ofInt 64 1))
      <<< (truncBits 32 (BitVec.ofInt 64 3)).toNat))) = BitVec.ofNat 64 ((sb + i % 2 * 8) % 2 ^
      32) := by
  simp only [trunc_lit, Int.reducePow, Int.reduceLE, Int.reduceLT, Int.reduceToNat,
    Nat.reduceLeDiff, ↓reduceIte, ge_iff_le, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod]
  omega

theorem sum_505 (sb i : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (sb % 2 ^ 32)) + truncBits 32
      (if (truncBits 32 (BitVec.ofInt 64 3)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32
      (truncBits 32 (truncBits 32 (truncBits 64 (BitVec.ofNat 64 i))) &&& truncBits 32
      (BitVec.ofInt 64 1)) <<< (truncBits 32 (BitVec.ofInt 64 3)).toNat)))) = Control.u32 (sb +
      i % 2 * 8) := by
  rw [inner_505]
  simp [Control.u32, b32]

theorem sum_874 (sb i : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (sb
      % 2 ^ 32)) + truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 3)).toNat ≥ 32 then 0 else
      truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 64 (BitVec.ofNat 64
      i))) &&& truncBits 32 (BitVec.ofInt 64 1)) <<< (truncBits 32 (BitVec.ofInt 64
      3)).toNat)))) + truncBits 32 (BitVec.ofInt 64 213280))) = Control.u32 (sb + i % 2 * 8 +
      213280) := by
  rw [inner_505]
  simp only [Control.u32, b32, trunc_lit, Int.reduceLE, Int.reduceLT, Int.reducePow,
    Int.reduceToNat]
  refine congrArg (Value.bits 32) (BitVec.eq_of_toNat_eq ?_)
  simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem bfe_875 (i : Nat) : Value.bits 32 (BitVec.ofNat 64 (bfeBits IType.u 32 (truncBits 32
    (truncBits 32 (truncBits 64 (BitVec.ofNat 64 i)))).toNat ((truncBits 32
      (BitVec.ofInt 64 1)).toNat % 256) ((truncBits 32 (BitVec.ofInt 64 1)).toNat % 256))) =
        b32 (i / 2 % 2) := by
  simp only [b32, trunc_lit, Int.reducePow, Int.reduceLE, Int.reduceLT, Int.reduceToNat,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Lib.bfe_u32 _ _ _ (show 1 + 1 ≤ 32 by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- The closers of the poll address of the loop. -/
macro "late_poll" : tactic => `(tactic| first
  | (rw [val_504]; exact and1_val _)
  | (rw [val_505]; exact sum_505 _ _)
  | (rw [val_874]; exact sum_874 _ _)
  | (rw [val_875]; exact bfe_875 _))

macro "late_vals2" : tactic => `(tactic| first | late_vals | late_poll)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
