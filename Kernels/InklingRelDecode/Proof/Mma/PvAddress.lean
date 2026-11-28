-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.Columns
public import Lemmas.Flow.TcMmaTs

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

/-- Register 565 after the 32-bit addition at PC 2523, for block `block`. -/
def pAddr (w : BitVec 32) (block : Nat) : Nat :=
  (w + BitVec.ofNat 32 (128 * (block % 2))).toNat

/-- The actual column check for each of the eight PV issues, including a wrapped register
addition. This case distinction is independent of the origin of the recorded word. -/
theorem pvOffset (w : BitVec 32) (block : Nat) (j : Fin 8) :
    tmemOffset (pAddr w block) (8 * (j.val : Int)) =
      if pAddr w block % 65536 + 8 * j.val < 65536 then
        .ok (pAddr w block + 8 * j.val) else .error .badValue := by
  split
  · exact PTX.Proof.tmemOffset_of (off := 8 * j.val) (by assumption)
  · simp only [tmemOffset]
    split
    · omega
    · rfl

/-- With the allocation's zero base every PV operand fits, in both parity buffers. -/
theorem pvOffset_alloc (block : Nat) (j : Fin 8) :
    tmemOffset (pAddr 0 block) (8 * (j.val : Int)) = .ok (128 * (block % 2) + 8 * j.val) := by
  rw [pvOffset]
  have ha : pAddr 0 block = 128 * (block % 2) := by
    simp [pAddr, BitVec.toNat_ofNat]
    omega
  rw [ha, ite_eq_left (by omega)]

theorem pvItem_inP (block : Nat) (j : Fin 8) (col : Fin 8) :
    Iface.InP 0 (block % 2) (128 * (block % 2) + 8 * j.val + col.val) := by
  unfold Iface.InP
  omega

end PTX.Kernels.InklingRelDecode.Proof.Mma
