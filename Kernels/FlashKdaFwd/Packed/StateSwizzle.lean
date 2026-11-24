-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.StateMap

@[expose] public section
namespace FlashKda.Packed.StateMap
open PTX

def swizzleWord (a : BitVec 64) := a ^^^ ((a >>> 3) &&& 16)

private def permute (n : Nat) := n ^^^ (n / 8 &&& 16)

private theorem byte_period (n : Nat) :
    permute n = 256 * (n / 256) + permute (n % 256) := by
  have lowmask (q : Nat) : q &&& 16 = (q % 32) &&& 16 := by
    have h : q &&& 16 < 32 := Nat.and_lt_two_pow (n := 5) _ (by decide)
    simpa only [Nat.mod_eq_of_lt h] using
      (Nat.and_mod_two_pow (a := q) (b := 16) (n := 5))
  have same : n / 8 &&& 16 = n % 256 / 8 &&& 16 := by
    rw [lowmask (n/8), show n / 8 % 32 = n % 256 / 8 by omega]
  have bound : n / 8 &&& 16 ≤ 16 := Nat.and_le_right
  have hi : permute n / 256 = n / 256 := by
    unfold permute
    rw [Nat.xor_div_two_pow (n := 8), Nat.div_eq_of_lt (show n/8 &&& 16 < 2^8 by omega)]
    simp
  have lo : permute n % 256 = permute (n%256) := by
    unfold permute
    rw [Nat.xor_mod_two_pow (n := 8), Nat.mod_eq_of_lt (show n/8 &&& 16 < 2^8 by omega),
      same]
  omega

private theorem small (n : Fin 256) :
    permute n = TensorSwizzle.offset .b32 0 n := by
  have all : ∀ k : Fin 256, permute k = TensorSwizzle.offset .b32 0 k := by decide +kernel
  exact all n

private theorem to_nat (x : BitVec 64) : (swizzleWord x).toNat = permute x.toNat := by
  simp [swizzleWord, permute, BitVec.toNat_xor, BitVec.toNat_and, Nat.shiftRight_eq_div_pow]

theorem swizzle_tensor (a : BitVec 64) :
    (swizzleWord a).toNat = TensorSwizzle.offset .b32 0 a.toNat := by
  rw [to_nat]
  rw [byte_period, small ⟨a.toNat%256, by omega⟩]
  have e := TensorSwizzle.offset_add_base .b32 (256*(a.toNat/256)) (a.toNat%256) (by omega)
  rw [show 256*(a.toNat/256) + a.toNat%256 = a.toNat by omega] at e
  rw [e]
  congr 1
  simp [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask, TensorSwizzle.sectors,
    Nat.add_mod]
  congr 1
  omega

theorem swizzle_window (base off : Nat) (aligned : base % 256 = 0) (fits : base+off < 2^64) :
    (swizzleWord (BitVec.ofNat 64 (base+off))).toNat =
      base + (swizzleWord (BitVec.ofNat 64 off)).toNat := by
  simp only [to_nat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt (show off < 2^64 by omega),
    byte_period (base+off), byte_period off, show (base+off)%256 = off%256 by omega]
  omega

theorem shared_word_address (base planes plane : Nat)
    (allocation : TensorDescriptor.AllocationClass) (smem : Loc) (i : Fin 16)
    (col : Fin 8) (row : Fin 128) (byte : Fin 4)
    (aligned : smem.addr % 128 = 0)
    (bound : smem.addr + 98304 ≤ 2^64) :
    let start := smem.addr + 32768 + 4096*i.val
    let loc := (strip base planes plane allocation smem i).sharedLoc
      (slot base planes allocation col row byte)
    (swizzleWord (BitVec.ofNat 64 (start + 32*row.val + 4*col.val + byte.val))).toNat =
      loc.addr := by
  dsimp only
  rw [swizzle_tensor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), shared_slot]
  have al : (smem.addr + 32768 + 4096*i.val) % 128 = 0 := by omega
  convert TensorSwizzle.offset_add_base .b32 (smem.addr + 32768 + 4096*i.val)
    (32*row.val + 4*col.val + byte.val) al using 2
  omega

end FlashKda.Packed.StateMap
