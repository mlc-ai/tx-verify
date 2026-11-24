-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderRing

@[expose] public section

/-! # The instructions that read the loaded counter words

The two words of the `(num_pre, num_iters)` load stay in `%r1444` and `%r6` as they were loaded
(`Loader.wordI`, `Loader.wordN`), so the segment evaluator cannot read them. The seven
instructions that do are proved one at a time with `Raw.seg_int1`, from the number the word reads
as (`Raw.word32Of`): the signed entry test `setp.ge.s32 %p19` (pc 2347), the two shifts and the
`mad.lo` of the loop's setup (pcs 2360 to 2362), the `mul.hi.s32` of the slot (pc 2365), and at the
loop's end the increment `add.s32 %r1444` (pc 2413) and the test `setp.ne.b32 %p25` (pc 2417). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- A register of the facts holding a word that reads as `x`. -/
theorem rd_word {pc r x : Nat} {F : List (Nat × Value)} {v : Value} {t : TState}
    (h : At t pc F) (hm : (r, v) ∈ F) (hw : Raw.word32Of v = some x) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 (BitVec.ofNat 64 x)) :=
  Raw.readBits_word32 (holds_mem h.2.2.2.2 hm) hw

/-- A register of the facts holding a 32-bit literal. -/
theorem rd_b32 {pc r x : Nat} {F : List (Nat × Value)} {t : TState}
    (h : At t pc F) (hm : (r, b32 x) ∈ F) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 (BitVec.ofNat 64 x)) := by
  simp [readBits, readReg, holds_mem h.2.2.2.2 hm, b32, bind, Except.bind, pure, Except.pure]

theorem toSigned_word (x : Nat) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 x)) = sxI x := by
  unfold toSigned sxI truncBits
  simp only [BitVec.toNat_ofNat]
  have h1 : x % 2 ^ 64 % 2 ^ 32 = x % 2 ^ 32 := by omega
  rw [h1]
  split_ifs <;> push_cast <;> omega

variable {F G : List (Nat × Value)}

/-- **`setp.ge.s32 %p19, %r1444, %r6`** (pc 2347): the signed entry test of the loop. -/
theorem seg_p19 {vi vn : Value} {i n : Nat} (hi : (1905, vi) ∈ F) (hn : (467, vn) ∈ F)
    (hwi : Raw.word32Of vi = some i) (hwn : Raw.word32Of vn = some n)
    (hG : ∀ R, Holds R F → Holds (Function.update R 19 (some (.pred (decide (sxI n ≤ sxI i))))) G) :
    Seg kernel asms L g 1 2347 F 2348 G := by
  refine Raw.seg_int1 Flow.code_2347 rfl rfl (Raw.asms_segFree (by decide +kernel))
    (fun t h => ?_) hG
  have hil := Raw.word32Of_lt hwi
  have hnl := Raw.word32Of_lt hwn
  simp only [execInt, rd_word h hi hwi, rd_word h hn hwn, DType.width, bind, Except.bind, pure,
    Except.pure]
  simp only [PTX.compare, DType.kind?, Option.getD_some, toSigned_word i, toSigned_word n]

/-- **`shl.b32 dst, %r1444, s`** (pcs 2360, 2361). -/
theorem seg_shl {pc dst s i : Nat} {F G : List (Nat × Value)} {vi : Value}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.shl, .int .b 32, false, [some dst],
      [.reg 1905, .imm (s : Int)]⟩⟩) (hs : s < 32)
    (hsf : Assumption.SegFreePc asms pc) (hi : (1905, vi) ∈ F)
    (hwi : Raw.word32Of vi = some i)
    (hG : ∀ R, Holds R F → Holds (Function.update R dst (some (b32 (2 ^ s * i % 2 ^ 32)))) G) :
    Seg kernel asms L g 1 pc F (pc + 1) G := by
  refine Raw.seg_int1 hc rfl rfl hsf (fun t h => ?_) hG
  have hil := Raw.word32Of_lt hwi
  have hs' : readBits L g t 32 (.imm (s : Int)) = .ok (truncBits 32 (BitVec.ofInt 64 s)) := rfl
  simp only [execInt, rd_word h hi hwi, hs', DType.width, bind, Except.bind, pure, Except.pure]
  have hst : (truncBits 32 (BitVec.ofInt 64 (s : Int))).toNat = s := by
    simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  rw [hst]
  simp only [show ¬ s ≥ 32 by omega, ↓reduceIte, b32]
  congr 4
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have e1 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have e2 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt hil
  rw [e1, e2, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mul_comm,
    Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]

/-- **`mad.lo.s32 %r116, %r71, %r1444, %r7`** (pc 2362): the key row of the first block. -/
theorem seg_mad577 {vi : Value} {i w x : Nat} (h71 : (532, b32 w) ∈ F) (hi : (1905, vi) ∈ F)
    (hx : (468, b32 x) ∈ F) (hwi : Raw.word32Of vi = some i)
    (hG : ∀ R, Holds R F →
      Holds (Function.update R 577 (some (b32 ((w % 2 ^ 32 * (i % 2 ^ 32) + x) % 2 ^ 32)))) G) :
    Seg kernel asms L g 1 2362 F 2363 G := by
  refine Raw.seg_int1 Flow.code_2362 rfl rfl (Raw.asms_segFree (by decide +kernel))
    (fun t h => ?_) hG
  simp only [execInt, rd_b32 h h71, rd_word h hi hwi, rd_b32 h hx, DType.width, bind,
    Except.bind, pure, Except.pure, b32]
  congr 4
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul,
    Nat.reducePow, nf_mod64_32, nf_mod32_64]
  rw [Nat.mod_eq_of_lt (show w % 4294967296 * (i % 4294967296) < 18446744073709551616 by
    have := Nat.mul_le_mul (show w % 4294967296 ≤ 4294967295 by omega)
      (show i % 4294967296 ≤ 4294967295 by omega)
    omega)]
  generalize w % 4294967296 * (i % 4294967296) = a
  omega

/-- `mul.hi.s32` reads the low 32 bits of its operand. -/
theorem mulHiW_mod (i : Nat) (b : BitVec 64) :
    mulHiW (BitVec.ofNat 64 (i % 2 ^ 32)) b = mulHiW (BitVec.ofNat 64 i) b := by
  have h : rdW (BitVec.ofNat 64 (i % 2 ^ 32)) = rdW (BitVec.ofNat 64 i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [rdW, truncBits, BitVec.toNat_ofNat]
    omega
  unfold mulHiW
  rw [h]

/-- **`mul.hi.s32 %r136, %r1444, 1431655766`** (pc 2365): the head of the slot computation. -/
theorem seg_mulhi {vi : Value} {i : Nat} (hi : (1905, vi) ∈ F) (hwi : Raw.word32Of vi = some i)
    (hG : ∀ R, Holds R F → Holds (Function.update R 597
      (some (.bits 32 (mulHiW (BitVec.ofNat 64 i) (BitVec.ofInt 64 1431655766))))) G) :
    Seg kernel asms L g 1 2365 F 2366 G := by
  refine Raw.seg_int1 Flow.code_2365 rfl rfl (Raw.asms_segFree (by decide +kernel))
    (fun t h => ?_) hG
  have hs' : readBits L g t 32 (.imm 1431655766) =
      .ok (truncBits 32 (BitVec.ofInt 64 1431655766)) := rfl
  simp only [execInt, rd_word h hi hwi, hs', DType.width, bind, Except.bind, pure, Except.pure]
  rfl

/-- **`add.s32 %r1444, %r1444, 1`** (pc 2413): the counter register becomes the incremented
32-bit word. -/
theorem seg_inc {vi : Value} {i : Nat} (hi : (1905, vi) ∈ F) (hwi : Raw.word32Of vi = some i)
    (hG : ∀ R, Holds R F → Holds (Function.update R 1905 (some (b32 ((i + 1) % 2 ^ 32)))) G) :
    Seg kernel asms L g 1 2413 F 2414 G := by
  refine Raw.seg_int1 Flow.code_2413 rfl rfl (Raw.asms_segFree (by decide +kernel))
    (fun t h => ?_) hG
  rw [Raw.execInt_add_imm (holds_mem h.2.2.2.2 hi) hwi]
  simp only [b32]
  congr 4
  apply BitVec.eq_of_toNat_eq
  have hil := Raw.word32Of_lt hwi
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  norm_num

/-- **`setp.ne.b32 %p25, %r6, %r1444`** (pc 2417): the loop's end test. -/
theorem seg_p25 {vn : Value} {i n : Nat} (hn : (467, vn) ∈ F) (hi : (1905, b32 i) ∈ F)
    (hwn : Raw.word32Of vn = some n) (hil : i < 2 ^ 32)
    (hG : ∀ R, Holds R F → Holds (Function.update R 25 (some (.pred (decide (n ≠ i))))) G) :
    Seg kernel asms L g 1 2417 F 2418 G := by
  refine Raw.seg_int1 Flow.code_2417 rfl rfl (Raw.asms_segFree (by decide +kernel))
    (fun t h => ?_) hG
  have hnl := Raw.word32Of_lt hwn
  simp only [execInt, rd_word h hn hwn, rd_b32 h hi, DType.width, bind, Except.bind, pure,
    Except.pure]
  simp only [PTX.compare, DType.kind?, Option.getD_some]
  all_goals (try congr 4)
  all_goals (try (simp only [truncBits, BitVec.toNat_ofNat, decide_eq_decide]; omega))

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
