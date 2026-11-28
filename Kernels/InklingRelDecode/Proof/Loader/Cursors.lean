-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
import Lemmas.Flow.Bits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

private theorem widen (x : BitVec 64) : r32 x = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_setWidth]

private theorem narrow (x : BitVec 64) : (r32 x).setWidth 32 = x.setWidth 32 := by
  rw [widen, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

private theorem eq_r32 {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) :
    r32 x = r32 y := (widen x).trans ((congrArg (BitVec.setWidth 64) h).trans (widen y).symm)

/-- The ring cursor increments are modulo 32 bits, including the transition across 0. -/
theorem shift_succ (x : BitVec 64) (k : Nat) (hk : k < 32) :
    add32 (shl x k) (BitVec.ofNat 64 (2 ^ k)) = shl (r32 (x + 1)) k := by
  have hki : (i32 (k : Int)).toNat = k := by
    nf_simp [i32]
    omega
  simp only [shl, hki, Nat.not_le_of_gt hk, ↓reduceIte]
  unfold add32
  change r32 _ = r32 _
  apply eq_r32
  simp only [BitVec.setWidth_add _ _ (by decide : 32 ≤ 64), narrow,
    BitVec.setWidth_shiftLeft_of_le (by decide : 32 ≤ 64)]
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, BitVec.add_mul]
  have hp : (BitVec.ofNat 64 (2 ^ k)).setWidth 32 = BitVec.twoPow 32 k := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.twoPow_eq, Nat.shiftLeft_eq]
  rw [hp]
  simp [BitVec.twoPow_eq]

/-- Increasing the split block by one increments the slab cursor by the scaled stride. -/
theorem slab_succ (x stride cta : BitVec 64) :
    add32 (shl (mad32 stride x cta) 7) (shl stride 7) =
      shl (mad32 stride (r32 (x + 1)) cta) 7 := by
  have sh (v : BitVec 64) : shl v 7 = r32 (r32 v <<< 7) := rfl
  rw [sh, sh, sh]
  unfold add32
  apply eq_r32
  simp only [BitVec.setWidth_add _ _ (by decide : 32 ≤ 64), narrow,
    BitVec.setWidth_shiftLeft_of_le (by decide : 32 ≤ 64), mad32,
    BitVec.setWidth_mul _ _ (by decide : 32 ≤ 64)]
  simp only [BitVec.shiftLeft_eq_mul_twoPow, BitVec.add_mul, BitVec.mul_add]
  simp
  ac_rfl

end PTX.Kernels.InklingRelDecode.Proof.Loader
