-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.RawWord

@[expose] public section

/-! # The lane field a broadcast word selects

The softmax region and the epilogue broadcast the warp index from lane 0 (`shfl.sync.idx`) and
form the lane field of their Tensor Memory address from the received word:
`shl.b32 %a, %recv, 21` and `and.b32 %b, %a, 0x600000`. The received word is any value; where it
reads as the 32-bit number `m` (`Raw.word32Of`), the shift writes `m · 2 ^ 21 mod 2 ^ 32`
(`execInt_shl21`, a segment of one step: `seg_shl21`) and the mask keeps bits 21 and 22, the
number `m % 4` shifted to bit 21 (`and_lane`). Where it has no bits the shift faults
(`dead_shl21`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Raw
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The shift by 21 of a word that reads as `m`. -/
theorem execInt_shl21 {L : Launch} {g : Nat} {t : TState} {d r : Nat} {v : Value} {m : Nat}
    (hr : t.regs r = some v) (hw : word32Of v = some m) :
    execInt L g t ⟨.shl, .int .b 32, false, [some d], [.reg r, .imm 21]⟩ =
      .ok (PTX.next (setReg t d (b32 (m * 2097152 % 2 ^ 32)))) := by
  have hb := readBits_word32 (L := L) (g := g) hr hw
  have h21 : (truncBits 32 (BitVec.ofInt 64 21)).toNat = 21 := by
    simp [truncBits]
  have hx : truncBits 32 (truncBits 32 (BitVec.ofNat 64 m) <<< 21) =
      BitVec.ofNat 64 (m * 2097152 % 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  simp only [execInt, DType.width]
  simp only [hb, bind, Except.bind]
  simp only [readBits, pure, Except.pure, h21]
  simp [hx, b32]

/-- The shift by 21 of a word without bits faults. -/
theorem execInt_shl21_none {L : Launch} {g : Nat} {t : TState} {d r : Nat} {v : Value}
    (hr : t.regs r = some v) (hw : word32Of v = none) :
    ∃ f, execInt L g t ⟨.shl, .int .b 32, false, [some d], [.reg r, .imm 21]⟩ = .error f := by
  obtain ⟨f, hf⟩ := readBits_word32_none (L := L) (g := g) hr hw
  exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩

/-- **The mask of the shifted word**: bits 21 and 22 of `m · 2 ^ 21 mod 2 ^ 32` are `m % 4`. -/
theorem and_lane (m : Nat) :
    (m * 2097152 % 4294967296 &&& 6291456) % 4294967296 = m % 4 * 2097152 := by
  have h1 : m * 2097152 % 4294967296 = (m % 2048) <<< 21 := by
    rw [Nat.shiftLeft_eq]
    omega
  have h2 : (6291456 : Nat) = 3 <<< 21 := by rw [Nat.shiftLeft_eq]
  have h3 : (m % 2048) &&& 3 = m % 4 := by
    have := Nat.and_two_pow_sub_one_eq_mod (m % 2048) 2
    norm_num at this
    rw [this]
  rw [h1, h2, ← Nat.shiftLeft_and_distrib, h3, Nat.shiftLeft_eq]
  have : m % 4 < 4 := Nat.mod_lt _ (by decide)
  norm_num
  omega

/-- The lane bits of a received word that a `.16x32bx2` access of warp `w` accepts: the word reads
as `m` and `m % 4` is 0 or `w`. -/
def laneOk (w : Nat) (v : Value) : Option Nat :=
  match word32Of v with
  | some m => if m % 4 = 0 ∨ m % 4 = w then some (m % 4) else none
  | none => none

/-- The warp index below 4 is accepted with its own bits. -/
theorem laneOk_b32 {w : Nat} (hw : w < 4) : laneOk w (b32 w) = some w := by
  simp only [laneOk, word32Of_b32]
  have h : w % 2 ^ 32 % 4 = w := by omega
  rw [h]
  simp

end
end PTX.Kernels.InklingRelDecode.Proof.Raw
