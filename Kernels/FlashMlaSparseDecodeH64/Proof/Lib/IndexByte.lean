-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal

@[expose] public section

/-! # The validity byte of a quad of lanes

The lanes `4 o + j` (`j < 4`) of the index warp each hold the validity bits of their two positions
shifted to `2 j` (`ixQuadW`). The lane `4 o` stores the `or` of its own bits, the first received
word (lane `4 o + 1`'s, the butterfly of distance 1) and the second (lane `4 o + 2`'s `or`ed with
its first received word, lane `4 o + 3`'s): bit `2 j + e` of the byte is the lane `4 o + j`'s
test of its position `e` (`byte_bits`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

theorem trunc32_and (x : BitVec 64) : truncBits 32 x = x &&& 0xFFFFFFFF := by
  unfold truncBits
  apply BitVec.eq_of_toNat_eq
  have h := Nat.and_two_pow_sub_one_eq_mod x.toNat 32
  have h2 : x.toNat % 2 ^ 32 < 2 ^ 64 := by
    have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
    omega
  simp only [BitVec.toNat_ofNat, BitVec.toNat_and, Nat.reducePow, Nat.reduceSub] at h ⊢
  have h3 : x.toNat % 4294967296 < 18446744073709551616 := h2
  rw [Nat.mod_eq_of_lt h3]
  have h4 : BitVec.toNat (4294967295 : BitVec 64) = 4294967295 := rfl
  rw [h4]
  exact h.symm

theorem shift_core (t : BitVec 64) (j : Nat) (hj : j < 4) (h : t &&& 3 = BitVec.ofNat 64 j) :
    (((t &&& 0xFFFFFFFF) <<< 1 &&& 0xFFFFFFFF) &&& 0xFFFFFFFF) &&& 6#64 =
      BitVec.ofNat 64 (2 * j) := by
  have h0 := congrArg (·.getLsbD 0) h
  have h1 := congrArg (·.getLsbD 1) h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] at h0 h1 ⊢
  interval_cases j <;> interval_cases i <;> simp_all

theorem shift_lane (t : BitVec 64) (j : Nat) (hj : j < 4) (h : t &&& 3 = BitVec.ofNat 64 j) :
    andi (shl t 1) 6 = BitVec.ofNat 64 (2 * j) := by
  have e1 : i32 1 = 1#64 := rfl
  have e6 : i32 6 = 6#64 := rfl
  have hn : (1#64).toNat = 1 := rfl
  unfold andi shl
  rw [e1, e6, hn]
  simp only [r32, trunc32_and]
  have hnc : ¬ (1 ≥ 32) := by decide
  simp only [hnc, ↓reduceIte]
  exact shift_core t j hj h

noncomputable section

/-- A lane's shifted validity bits for the lane's place `j` in its quad. -/
abbrev quadW (a b : Bool) (j : Nat) : BitVec 64 :=
  shlr (or32 (sel b (i32 2) (i32 0)) (sel a (i32 1) (i32 0))) (BitVec.ofNat 64 (2 * j))

theorem tw_and3 (L : Launch) (g : Nat) : tw L g &&& 3 = BitVec.ofNat 64 (tidOf L g % 4) := by
  apply BitVec.eq_of_toNat_eq
  have h := Nat.and_two_pow_sub_one_eq_mod (tidOf L g % 2 ^ 64) 2
  simp only [BitVec.toNat_and, tw, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub] at h ⊢
  have e : (3 : BitVec 64).toNat = 3 := rfl
  rw [e, h]
  omega

/-- **The quad word of a lane** in place `j` of its quad. -/
theorem ixQuadW_lane (L : Launch) (g : Nat) {j : Nat} (hj : j < 4) (h : tidOf L g % 4 = j)
    (a b : Bool) : ixQuadW L g a b = quadW a b j := by
  unfold ixQuadW quadW
  rw [shift_lane (tw L g) j hj (by rw [tw_and3, h])]

/-- **Bit `i` of the quad's byte**: the lane `4 o`'s `or` of its own word, the first receive
(lane 1's) and the second (lane 2's `or`ed with lane 3's). -/
theorem byte_bits (a0 b0 a1 b1 a2 b2 a3 b3 : Bool) :
    ∀ i < 8, (truncBits 8 (or32 (or32 (rvw (cvts8 (quadW a1 b1 1))) (quadW a0 b0 0))
      (rvw (cvts8 (or32 (rvw (cvts8 (quadW a3 b3 3))) (quadW a2 b2 2)))))).toNat.testBit i =
      [a0, b0, a1, b1, a2, b2, a3, b3].getD i false := by
  intro i hi
  interval_cases i <;> cases a0 <;> cases b0 <;> cases a1 <;> cases b1 <;> cases a2 <;>
    cases b2 <;> cases a3 <;> cases b3 <;> decide +kernel

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
