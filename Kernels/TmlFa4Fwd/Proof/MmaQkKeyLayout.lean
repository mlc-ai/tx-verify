-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkInputLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem kvSwizzleMask (addr : Nat) :
    (addr >>> 3) &&& 112 = 16 * ((addr / 128) % 8) := by
  let m := (addr >>> 3) &&& 112
  have hQuot : m / 16 = (addr / 128) % 8 := by
    dsimp only [m]
    rw [show 16 = 2 ^ 4 by decide, Nat.and_div_two_pow, Nat.shiftRight_eq_div_pow]
    have hq : addr / 2 ^ 3 / 2 ^ 4 = addr / 128 := by omega
    rw [hq, show (112 : Nat) / 2 ^ 4 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have hRem : m % 16 = 0 := by
    dsimp only [m]
    rw [show 16 = 2 ^ 4 by decide, Nat.and_mod_two_pow]
    simp
  change m = _
  omega

/-- The explicit loader bit instructions and the shared descriptor use the same swizzle. -/
theorem kvSwizzle_eq_offset (addr : Nat) :
    kvSwizzle addr = TensorSwizzle.offset .b128 0 addr := by
  let dest := kvSwizzle addr
  have hChunk : dest / 16 % 8 = (addr / 16 % 8) ^^^ ((addr / 128) % 8) := by
    change (addr ^^^ ((addr >>> 3) &&& 112)) / 16 % 8 = _
    rw [show 16 = 2 ^ 4 by decide, Nat.xor_div_two_pow, kvSwizzleMask]
    have hm : 16 * (addr / 128 % 8) / 2 ^ 4 = addr / 128 % 8 := by omega
    rw [hm, show 8 = 2 ^ 3 by decide, Nat.xor_mod_two_pow]
    have hm' : addr / 128 % 2 ^ 3 % 2 ^ 3 = addr / 128 % 2 ^ 3 := Nat.mod_mod _ _
    rw [hm']
  have hHi : dest / 128 = addr / 128 := by
    have hm := Nat.and_lt_two_pow (addr >>> 3) (show (112 : Nat) < 2 ^ 7 by decide)
    have hz : ((addr >>> 3) &&& 112) / 128 = 0 := by omega
    change (addr ^^^ ((addr >>> 3) &&& 112)) / 128 = _
    rw [show 128 = 2 ^ 7 by decide, Nat.xor_div_two_pow]
    simpa using congrArg (fun n => (addr / 128) ^^^ n) hz
  have hLo : dest % 16 = addr % 16 := by
    change (addr ^^^ ((addr >>> 3) &&& 112)) % 16 = _
    rw [show 16 = 2 ^ 4 by decide, Nat.xor_mod_two_pow, Nat.and_mod_two_pow]
    simp
  change dest = _
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask, TensorSwizzle.sectors,
    BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.zero_div, Nat.zero_add, Nat.reducePow]
  rw [Nat.mod_mod]
  omega

theorem kvSwizzle_add_period (a n : Nat) :
    kvSwizzle (a + 1024 * n) = kvSwizzle a + 1024 * n := by
  have hm : ((a + 1024 * n) / 128) % 8 = (a / 128) % 8 := by omega
  have hmask : ((a + 1024 * n) >>> 3) &&& 112 = (a >>> 3) &&& 112 := by
    rw [kvSwizzleMask, kvSwizzleMask, hm]
  have hHi : kvSwizzle (a + 1024 * n) / 1024 = kvSwizzle a / 1024 + n := by
    rw [kvSwizzle_div_1024, kvSwizzle_div_1024]
    omega
  have hLo : kvSwizzle (a + 1024 * n) % 1024 = kvSwizzle a % 1024 := by
    unfold kvSwizzle
    rw [hmask, show 1024 = 2 ^ 10 by decide, Nat.xor_mod_two_pow, Nat.xor_mod_two_pow]
    have hR : (a + 2 ^ 10 * n) % 2 ^ 10 = a % 2 ^ 10 := by omega
    rw [hR]
  omega

theorem kvSwizzle_byte (a byte : Nat) (ha : a % 16 = 0) (hb : byte < 16) :
    kvSwizzle (a + byte) = kvSwizzle a + byte := by
  rw [kvSwizzle_eq_offset, kvSwizzle_eq_offset]
  have hd : (a + byte) / 128 = a / 128 := by omega
  have hq : (a + byte) / 16 = a / 16 := by omega
  have hm : (a + byte) % 16 = byte := by omega
  simp [TensorSwizzle.offset, hd, hq, hm, ha]

/-- Lane among the two loader warps supplying a K operand vector. -/
def qkLoaderLane (step : Fin 8) (row k : Nat) : Nat :=
  8 * (row % 8) + qkPlaneColumn step k / 8

def qkLoaderByte (step : Fin 8) (k byte : Nat) : Nat := 2 * (qkPlaneColumn step k % 8) + byte

/-- Every QK B operand byte is a byte of the ordinary K packet of its selected ring phase. -/
theorem qkKCopyByteLoc (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat)
    (hBase : l.sharedBase % 1024 = 0)
    {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hb : byte < 2) :
    let lane := qkLoaderLane step row k
    let group := row / 8
    let upper := decide (4 ≤ step.val)
    (qkOperands l g block step use).byteLoc .b (qkByteIndex row k byte) =
      some ⟨.shared, g / l.block, kvCopyAddress l.sharedBase (kvSlot use) lane group upper +
        qkLoaderByte step k byte⟩ := by
  dsimp only
  rw [qkInputByteLoc l g block step use .b hr hk hb, ← kvSwizzle_eq_offset]
  change some (⟨.shared, g / l.block, kvSwizzle
    (kvStart l use + qkFragment step + 128 * row + 2 * k + byte)⟩ : Loc) = _
  let lane := qkLoaderLane step row k
  let grp := row / 8
  let low := l.sharedBase + 68608 + 1024 * (grp % 2) + 16 * (lane % 64)
  let off := qkLoaderByte step k byte
  let n := 32 * kvSlot use + 2 * (grp / 2) + if 4 ≤ step.val then 16 else 0
  have hPlane : qkPlane step = if 4 ≤ step.val then 1 else 0 := by
    have h := step.isLt
    unfold qkPlane
    split <;> omega
  have hLane : qkLoaderLane step row k < 64 := by
    dsimp only [qkLoaderLane]
    have hC := qkPlaneColumn_lt step hk
    omega
  have hRaw : kvStart l use + qkFragment step + 128 * row + 2 * k + byte =
      low + 1024 * n + off := by
    dsimp only [kvStart, qkFragment, low, n, grp, lane, off]
    rw [Nat.mod_eq_of_lt hLane]
    change _ + (_ + 16384 * qkPlane step) + 128 * row + 2 * k + byte = _
    dsimp only [qkLoaderLane, qkLoaderByte, qkPlaneColumn]
    rw [hPlane]
    split <;> omega
  have hA : (low + 1024 * n) % 16 = 0 := by dsimp only [low]; omega
  have hB : off < 16 := by dsimp [off, qkLoaderByte]; omega
  rw [hRaw, kvSwizzle_byte _ _ hA hB, kvSwizzle_add_period]
  congr 2
  simp only [kvCopyAddress, low, n, off, grp, lane, decide_eq_true_eq]
  split <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
