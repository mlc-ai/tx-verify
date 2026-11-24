-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Loaded
import Lemmas.Flow.WordBound

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow.Arith32

/-- Read a mask word with the instruction used for the low, middle or high bit. -/
private def keepBit (x : BitVec 64) (i : Nat) : Bool :=
  if i = 0 then compare .ne .b 32 (r32 (andi x 1)) (i32 0)
  else if i < 31 then !compare .eq .b 32 (r32 (andi x (2^i))) (i32 0)
  else !compare .gt .s 32 (r32 x) (i32 (-1))

private theorem keep_shifted (n : Fin 33) (i : Fin 32) :
    keepBit (r32 (i32 (-1)) >>> n.val) i.val = decide (i.val+n.val < 32) := by
  revert n i
  decide +kernel

/-- The first-round instruction mask keeps exactly the columns below the signed count. -/
theorem diagonal_iff {m : BitVec 64} (hm : -256 ≤ toSigned 32 m) (hm' : toSigned 32 m ≤ 128)
    (k : Fin 4) (i : Fin 32) :
    diagonal m k.val i.val = decide ((32*k.val+i.val : Nat) < toSigned 32 m) := by
  let s := sub32 (i32 (32*(k.val+1))) m
  have imm : toSigned 32 (i32 (32*(k.val+1))) = 32*(k.val+1 : Int) := by
    fin_cases k <;> decide
  have es : toSigned 32 s = 32*(k.val+1 : Int) - toSigned 32 m := by
    rw [show toSigned 32 s = _ from toSigned_sub32 _ _
      (by rw [imm]; have := k.isLt; omega) (by rw [imm]; have := k.isLt; omega),imm]
  have trunc (x : BitVec 64) : toSigned 32 (r32 x) = toSigned 32 x := by
    simp only [toSigned, r32, truncBits, BitVec.toNat_ofNat]; split <;> split <;> omega
  have cs : (r32 (mshift k.val m)).toNat = (toSigned 32 s).toNat := by
    change (r32 (if compare .gt .s 32 (r32 s) (i32 0) then r32 s else i32 0)).toNat = _
    change (r32 (if decide (0 < toSigned 32 (r32 s)) then r32 s else i32 0)).toNat = _
    simp only [trunc, decide_eq_true_eq]
    split
    · rename_i h
      have h' := toNat_r32_of_toSigned (x := r32 s) (by rw [trunc]; omega)
      rw [trunc] at h'
      omega
    · have z : (r32 (i32 0)).toNat = 0 := rfl
      rw [z]
      omega
  change keepBit (mword k.val m) i.val = _
  rw [mword,cs]
  by_cases h : (toSigned 32 s).toNat ≥ 32
  · rw [ite_eq_left h]
    have bit := keep_shifted (32 : Fin 33) i
    change keepBit 0 i.val = decide (i.val+32 < 32) at bit
    rw [bit]
    congr 1
    push_cast
    apply propext
    omega
  · rw [ite_eq_right (by omega),keep_shifted ⟨_,by omega⟩ i]
    congr 1
    push_cast
    apply propext
    have := i.isLt
    constructor <;> omega

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
