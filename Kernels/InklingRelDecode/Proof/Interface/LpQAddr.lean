-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LpQCross
public import Kernels.InklingRelDecode.Proof.Result.MmaLayout

@[expose] public section

/-!
# The query store that writes a byte of the query tile

`ProA.qStoreBase_form` gives the address of the prologue's query store `m` of a thread:
`sharedBase + 196608 + 2048 qGroup m + qSwz tid`. `Result.Mma.qAddr sb r d z` is the 128-byte
swizzled address of byte `z` of element `(r, d)` of the query tile. `qAddr_form` matches the two:
for a shared base aligned to 1024 bytes, the byte is in the four bytes of element `w = (d % 8) / 2`
of store `m = 2 (r / 16) + d / 64` of the thread `t = 8 (r % 16) + (d % 64) / 8`, at offset
`2 (d % 2) + z` (the lower bf16 value of a packed word is the even column).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The swizzled row offset of thread `8 R + c`: its row `R` and its 16-byte chunk `c` XOR
`R % 8`. -/
theorem qSwz_form : ∀ R < 16, ∀ c < 8, ProA.qSwz (8 * R + c) = 128 * R + 16 * (c ^^^ R % 8) := by
  decide +kernel

/-- The thread of the query tile's byte `(r, d, z)`. -/
def qThread (r d : Nat) : Nat := 8 * (r % 16) + d % 64 / 8

/-- The store of the query tile's byte `(r, d, z)`. -/
def qStore (r d : Nat) : Nat := 2 * (r / 16) + d / 64

/-- The element of that store. -/
def qElemIdx (d : Nat) : Nat := d % 8 / 2

theorem qThread_lt {r d : Nat} : qThread r d < 128 := by unfold qThread; omega

theorem qStore_lt {r d : Nat} (hr : r < 64) (hd : d < 128) : qStore r d < 8 := by
  unfold qStore; omega

theorem qElemIdx_lt {d : Nat} : qElemIdx d < 4 := by unfold qElemIdx; omega

/-- **The closed form of the query tile's address** against the query stores' addresses. -/
theorem qAddr_form {sb r d z : Nat} (hsb : sb % 1024 = 0) (hd : d < 128)
    (hz : z < 2) :
    Result.Mma.qAddr sb r d z = sb + 196608 + 2048 * ProA.qGroup (qStore r d) +
      ProA.qSwz (qThread r d) + 4 * qElemIdx d + (2 * (d % 2) + z) := by
  unfold Result.Mma.qAddr TensorSwizzle.offset TensorSwizzle.chunk TensorSwizzle.mask
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [TensorSwizzle.sectors, Nat.zero_div, Nat.zero_add]
  unfold qThread
  rw [qSwz_form (r % 16) (by omega) (d % 64 / 8) (by omega)]
  set x := sb + 196608 + 8192 * (d / 64) + 128 * r + 2 * (d % 64) + z with hx
  have h1 : x / 128 = sb / 128 + 1536 + 64 * (d / 64) + r := by omega
  have h2 : x / 16 % 2 ^ 3 = d % 64 / 8 := by omega
  have h3 : x / 128 % 8 % 2 ^ 3 = r % 16 % 8 := by omega
  have h4 : x % 16 = 2 * (d % 8) + z := by omega
  rw [h2, h3, h4, h1]
  unfold ProA.qGroup qStore qElemIdx
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
