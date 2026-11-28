-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
import Kernels.InklingRelDecode.Proof.Lib.Rows

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Arith32 Control

private theorem sx_small (n : Nat) (h : n < 2 ^ 31) : Lib.sx n = n := by
  unfold Lib.sx; omega

private theorem shift_small (n : Nat) (h : n < 2 ^ 31) :
    (shrs (W (n % 2 ^ 32)) 6).toNat = n / 64 := by
  rw [Nat.mod_eq_of_lt (by omega)]
  have := toNat_shrs_W h (k := 6) (by decide)
  have e : ((6 : Nat) : Int) = 6 := rfl
  rw [e] at this
  rw [this]
  simp only [W, BitVec.toNat_ofNat]
  omega

/-- The block-table address of the load of half `h` of preload `b`. -/
theorem block_ptr_eq {Q : Params} {req split b h : Nat} (hq : Q.seqK req + 511 < 2 ^ 31)
    (hb : b < 3) (hh : h < 2) (hlt : split + b * Q.splits < Q.blocks req)
    (hidx : req * Q.strideBt + (2 * (split + b * Q.splits) + h) < 2 ^ 31) :
    blockPtr Q req split b h =
      Q.btBase + 4 * (req * Q.strideBt + (2 * (split + b * Q.splits) + h)) := by
  have bl : Q.blocks req ≤ 2 ^ 24 := by unfold Params.blocks; omega
  have off : blkOff Q split b < 2 ^ 31 ∧ blkOff Q split b / 64 = 2 * (split + b * Q.splits) := by
    interval_cases b <;> simp only [blkOff] <;> constructor <;> omega
  have row : Lib.sx (Q.strideBt * req) = Q.strideBt * req := sx_small _ (by
    rw [Nat.mul_comm]; omega)
  unfold blockPtr btRow blkIx
  rw [shift_small _ off.1, off.2, sx_small _ (by omega), row]
  rw [Nat.mul_comm Q.strideBt req]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue
