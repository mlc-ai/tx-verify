-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Lemmas.Flow.LoadShared

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000
-- These instructions' values reduce by the segment checker.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-- The role keeps the actual mask word returned by the scalar read. -/
theorem at_maskRead_word {d : D} {t u : TState} {bytes : List (Option Byte)} {w : BitVec 64}
    (hd : d.site = .maskRead) (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hu : u = afterLoad t [1002] bytes) (hw : rebuild 3 bytes = .ok (.bits 32 w)) :
    At u 290 ((1002, .bits 32 w) :: factsFrom ((Flow.live 289).filter
      (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have hsub : d.sub = 0 := by
    have hs := hinv.subLt
    simpa [hd, Site.elems] using hs
  have ht : At t 289 (factsFrom ((Flow.live 289).filter (fun r => tracked.contains r))
      (valueOf P L g d)) := by
    refine ⟨?_, hat.2.1.trans hsub, hat.2.2.1.trans (siteAcc_nil d hsub), hat.2.2.2.1, ?_⟩
    · simpa only [code, hd, Site.pc] using hat.1
    · simpa only [code, facts, hd, Site.pc] using hat.2.2.2.2
  have hset := ht.set (r := 1002) (v := .bits 32 w) (by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact fun he => (by decide +kernel : 1002 ∉ (Flow.live 289).filter
      (fun r => tracked.contains r)) (he ▸ hr))
  rw [hu, afterLoad_ok ht.2.1 ht.2.2.1 hw]
  simpa only [PTX.next, setReg, ht.2.1, ht.2.2.1] using hset

/-- Split out the two low mask fields before testing individual valid bits. -/
theorem run_290_292 (d : D) (w : BitVec 64) {t : TState}
    (h : At t 290 ((1002, .bits 32 w) :: factsFrom ((Flow.live 289).filter
      (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 2 t = some u ∧
      At u 292 ((155, (MemExt.sign 16).extendBits 8
          (cvtIntBits false .s 8 .s 32 (truncBits 32 w))) ::
        (156, .bits 16 (truncBits 16 (truncBits 32 w))) ::
        (1002, .bits 32 w) ::
        factsFrom ((Flow.live 292).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  seg_fp h using skip

/-- The sign-extended byte read by the signed high-bit tests. -/
def maskSignedByte (w : BitVec 64) (offset : Nat) : Value :=
  let extract := BitVec.ofNat 64 (bfeBits .s 32 (truncBits 32 w).toNat offset 8)
  (MemExt.sign 16).extendBits 8 (cvtIntBits false .s 8 .s 32 (truncBits 32 extract))

/-- Retain the unsigned mask byte fields and the sign-extended bytes for bits 15 and 23. -/
theorem run_292_299 (d : D) (w : BitVec 64) {t : TState}
    (h : At t 292 ((155, (MemExt.sign 16).extendBits 8
          (cvtIntBits false .s 8 .s 32 (truncBits 32 w))) ::
        (156, .bits 16 (truncBits 16 (truncBits 32 w))) ::
        (1002, .bits 32 w) ::
        factsFrom ((Flow.live 292).filter (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 7 t = some u ∧
      At u 299 ((155, (MemExt.sign 16).extendBits 8
          (cvtIntBits false .s 8 .s 32 (truncBits 32 w))) ::
        (156, .bits 16 (truncBits 16 (truncBits 32 w))) ::
        (157, maskSignedByte w 8) ::
        (158, .bits 16 (truncBits 16 (truncBits 32 (truncBits 32 w >>> 8)))) ::
        (159, maskSignedByte w 16) ::
        (1002, .bits 32 w) ::
        (1003, .bits 32 (truncBits 32 w >>> 8)) ::
        (1005, .bits 32 (truncBits 32 w >>> 16)) ::
        factsFrom ((Flow.live 299).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  seg_fp h using rfl

/-- The mask unpack keeps only the upper sixteen bits. -/
theorem run_299_300 {t : TState} {F : List (Nat × Value)} {w : BitVec 64} (h : At t 299 F)
    (hmask : t.regs 1002 = some (.bits 32 w)) (hkeep : ∀ p ∈ F, p.1 ≠ 160) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u 300 ((160, (splitValue 32 (.bits 32 w)).2) :: F) := by
  have hstep : execLocalA asms L g t
      (.move ⟨.unpack, .int .b 32, [none, some 160], [.reg 1002]⟩) =
      .ok (PTX.next (setReg t 160 (splitValue 32 (.bits 32 w)).2)) := by
    rw [Assumption.SegFreePc.exec (by seg_free_pc) h.1, execLocalRule_of_none
      (Thread.asms_localRule_move (by rw [h.1]; decide) (by rw [h.1]; decide)
        (by rw [h.1]; decide)), execLocal_move (by rfl)]
    simp [execMove, readValue, readReg, hmask, splitValue, DType.width, Value.bytes, setDst,
      bind, Except.bind, pure, Except.pure]
  exact ⟨_, run_local (K := kernel) Flow.code_299 rfl h hstep, h.set hkeep⟩

theorem and_mask_bit (x j : Nat) : x &&& (2 ^ j) = if x.testBit j then 2 ^ j else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : j = i
  · subst i
    cases hb : x.testBit j <;> simp [Nat.testBit_and, Nat.testBit_two_pow_self, hb]
  · simp only [Nat.testBit_and, Nat.testBit_two_pow_of_ne h, Bool.and_false]
    split <;> simp [Nat.testBit_two_pow_of_ne h]

/-- An integer AND followed by a nonzero comparison tests a single bit. -/
theorem mask_testBit (w : BitVec 64) {width j : Nat} (hj : j < width) (hw : width ≤ 64) :
    compare .ne .b width
      (truncBits width (truncBits width w &&& BitVec.ofNat 64 (2 ^ j))) 0 =
        w.toNat.testBit j := by
  have hx : (truncBits width w).toNat = w.toNat % 2 ^ width := by
    simp only [truncBits, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) hw))
  have hn : (2 : Nat) ^ j < 2 ^ width := Nat.pow_lt_pow_right (by decide) hj
  have hz : (BitVec.ofNat 64 (2 ^ j)).toNat = 2 ^ j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hw)
  have hand : (truncBits width w &&& BitVec.ofNat 64 (2 ^ j)).toNat =
      if w.toNat.testBit j then 2 ^ j else 0 := by
    rw [BitVec.toNat_and, hx, hz, and_mask_bit, Nat.testBit_mod_two_pow]
    simp [hj]
  have h64 := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hw)
  have ht : (truncBits width (truncBits width w &&& BitVec.ofNat 64 (2 ^ j))).toNat =
      if w.toNat.testBit j then 2 ^ j else 0 := by
    change (BitVec.ofNat 64
      ((truncBits width w &&& BitVec.ofNat 64 (2 ^ j)).toNat % 2 ^ width)).toNat = _
    rw [BitVec.toNat_ofNat, hand]
    cases w.toNat.testBit j <;> simp [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h64]
  change (decide (((truncBits width
    (truncBits width w &&& BitVec.ofNat 64 (2 ^ j))).toNat : Int) ≠ 0)) = _
  rw [ht]
  cases w.toNat.testBit j <;> simp


/-- The score mask selects the score payload or the negative-infinity word. -/
theorem run_mask_select {site dst src p : Nat} {t : TState} {F : List (Nat × Value)}
    (direct bit : Bool) (v : Value) (hpc : 304 ≤ site ∧ site ≤ 393)
    (hc : kernel.code[site]? = some ⟨none, .int ⟨.selp, .int .b 32, false, [some dst],
      [if direct then .reg src else .imm (-8388608),
        if direct then .imm (-8388608) else .reg src, .reg p]⟩⟩)
    (hat : At t site F) (hp : t.regs p = some (.pred (bit == direct)))
    (hr : t.regs src = some v) (hbytes : v.bytes = 4) (hkeep : ∀ q ∈ F, q.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (site + 1) ((dst, if bit then v else negInf) :: F) := by
  let i : IntInstr := ⟨.selp, .int .b 32, false, [some dst],
    [if direct then .reg src else .imm (-8388608),
      if direct then .imm (-8388608) else .reg src, .reg p]⟩
  have hp1 : t.pc ∉ paramAdds := by rw [hat.1]; simp [paramAdds]; omega
  have hp2 : t.pc ∉ prefetchTensorMapSites := by rw [hat.1]; simp [prefetchTensorMapSites]; omega
  have hshared : t.pc ∉ Assumptions.sharedBitsSites := by
    rw [hat.1]
    simp [Assumptions.sharedBitsSites]
    omega
  have hL := Thread.asms_localRule_int (L := L) (g := g) (i := i) hp1 hp2 hshared rfl
  have hlocal : i.rule = some .threadMove := by cases direct <;> rfl
  have hx : execLocalA asms L g t (.int i) =
      .ok (PTX.next (setReg t dst (if bit then v else negInf))) := by
    rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hL,
      execLocal_selp hlocal]
    cases direct <;> cases bit <;> simp [i, execMove, DType.width, readValue, readBits, readReg,
      hp, hr, hbytes, negInf, Value.bytes, bind, Except.bind, pure, Except.pure]
    all_goals rfl
  exact ⟨_, run_local (K := kernel) hc (by cases direct <;> rfl) hat hx, hat.set hkeep⟩

/-- Mask operations use ordinary local rules. -/
theorem mask_local_sites {t : TState} (h : 302 ≤ t.pc ∧ t.pc ≤ 393) :
    t.pc ∉ paramAdds ∧ t.pc ∉ prefetchTensorMapSites ∧ t.pc ∉ Assumptions.sharedBitsSites := by
  simp [paramAdds, prefetchTensorMapSites, Assumptions.sharedBitsSites]
  omega

/-- Execute the two-operand integer predicate selected by the frozen mask program. -/
theorem run_mask_cmp {site dst src width : Nat} {t : TState} {F : List (Nat × Value)}
    (kind : IType) (cmp : Cmp) (imm : Int) (w : BitVec 64)
    (hpc : 302 ≤ site ∧ site ≤ 393) (hwidth : width = 16 ∨ width = 32)
    (hc : kernel.code[site]? = some ⟨none, .int
      ⟨.setp cmp none, .int kind width, false, [some dst], [.reg src, .imm imm]⟩⟩)
    (hrule : (⟨.setp cmp none, .int kind width, false, [some dst], [.reg src, .imm imm]⟩ :
      IntInstr).rule = some .threadInt)
    (hat : At t site F) (hr : t.regs src = some (.bits width w))
    (hkeep : ∀ q ∈ F, q.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (site + 1) ((dst, .pred (compare cmp kind width (truncBits width w)
        (truncBits width (BitVec.ofInt 64 imm)))) :: F) := by
  let i : IntInstr := ⟨.setp cmp none, .int kind width, false, [some dst], [.reg src, .imm imm]⟩
  obtain ⟨hp1, hp2, hshared⟩ := mask_local_sites (by rw [hat.1]; exact hpc)
  have hL := Thread.asms_localRule_int (L := L) (g := g) (i := i) hp1 hp2 hshared rfl
  have hx : execLocalA asms L g t (.int i) = .ok (PTX.next (setReg t dst
      (.pred (compare cmp kind width (truncBits width w)
        (truncBits width (BitVec.ofInt 64 imm)))))) := by
    rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hL,
      execLocal_int hrule]
    rcases hwidth with rfl | rfl <;> simp [execInt, DType.width, DType.kind?, readBits,
      readReg, hr, bind, Except.bind, pure, Except.pure]
  exact ⟨_, run_local (K := kernel) hc (by rfl) hat hx, hat.set hkeep⟩

/-- Preserve the masked word for the next predicate without requiring its value to be concrete. -/
theorem run_mask_and {site dst src width : Nat} {t : TState} {F : List (Nat × Value)}
    (imm : Int) (w : BitVec 64) (hpc : 302 ≤ site ∧ site ≤ 393) (hwidth : width = 16 ∨ width = 32)
    (hc : kernel.code[site]? = some ⟨none, .int
        ⟨.and, .int .b width, false, [some dst], [.reg src, .imm imm]⟩⟩)
    (hat : At t site F) (hr : t.regs src = some (.bits width w))
    (hkeep : ∀ q ∈ F, q.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (site + 1)
      ((dst, .bits width (truncBits width w &&& truncBits width (BitVec.ofInt 64 imm))) :: F) := by
  let i : IntInstr := ⟨.and, .int .b width, false, [some dst], [.reg src, .imm imm]⟩
  obtain ⟨hp1, hp2, hshared⟩ := mask_local_sites (by rw [hat.1]; exact hpc)
  have hL := Thread.asms_localRule_int (L := L) (g := g) (i := i) hp1 hp2 hshared rfl
  have hx : execLocalA asms L g t (.int i) = .ok (PTX.next (setReg t dst
      (.bits width (truncBits width w &&& truncBits width (BitVec.ofInt 64 imm))))) := by
    have hi : i.rule = some .threadInt := by rcases hwidth with rfl | rfl <;> rfl
    rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hL,
      execLocal_int hi]
    rcases hwidth with rfl | rfl <;> simp [i, execInt, DType.width, readBits, readReg, hr,
      bind, Except.bind, pure, Except.pure]
  exact ⟨_, run_local (K := kernel) hc (by rfl) hat hx, hat.set hkeep⟩


/-- End of the three-instruction mask test, or two instructions for a sign bit. -/
def maskSelectSite (j : Fin 32) : Nat := 304 + 3 * j.val - (j.val + 1) / 8

/-- The predicate guarding this score. -/
def maskPredicate (j : Fin 32) : Nat := 77 + j.val

/-- The width of the input to the predicate. -/
def maskTestWidth (j : Fin 32) : Nat := if j.val % 8 = 0 ∨ j.val = 31 then 32 else 16

/-- Each eighth predicate tests the sign of a signed field. -/
def maskTestKind (j : Fin 32) : IType := if j.val % 8 = 7 then .s else .b

/-- Low-bit tests use the direct predicate, signed and intermediate-bit tests use its inverse. -/
def maskTestCmp (j : Fin 32) : Cmp :=
  if j.val % 8 = 0 then .ne else if j.val % 8 = 7 then .gt else .eq

/-- Sign tests compare against -1, and all other tests compare against zero. -/
def maskTestImm (j : Fin 32) : Int := if j.val % 8 = 7 then -1 else 0

/-- The sign field, or the temporary AND result for every other bit. -/
def maskTestReg (j : Fin 32) : Nat :=
  if j.val % 8 = 0 then 1008 + 9 * (j.val / 8)
  else if j.val % 8 = 7 then [155, 157, 159, 1002].getD (j.val / 8) 0
  else 161 + 6 * (j.val / 8) + j.val % 8

/-- The register from which the preceding AND picks a bit. -/
def maskAndSrc (j : Fin 32) : Nat :=
  if j.val % 8 = 0 then [1002, 1003, 1005, 1007].getD (j.val / 8) 0
  else [156, 158, 160, 161].getD (j.val / 8) 0

/-- The decoded selection preserves the supplied score exactly when its bit is valid. -/
theorem maskSelect_matches (j : Fin 32) :
    kernel.code[maskSelectSite j]? = some ⟨none, .int
      ⟨.selp, .int .b 32, false, [some (maskSelectDst j)],
        [if j.val % 8 = 0 then .reg (2918 + j.val) else .imm (-8388608),
          if j.val % 8 = 0 then .imm (-8388608) else .reg (2918 + j.val),
          .reg (maskPredicate j)]⟩⟩ := by
  fin_cases j <;> kernel_rfl

/-- The comparison instruction selects the indicated signed or unsigned field. -/
theorem maskTest_matches (j : Fin 32) :
    kernel.code[maskSelectSite j - 1]? = some ⟨none, .int
      ⟨.setp (maskTestCmp j) none, .int (maskTestKind j) (maskTestWidth j), false,
        [some (maskPredicate j)], [.reg (maskTestReg j), .imm (maskTestImm j)]⟩⟩ := by
  fin_cases j <;> kernel_rfl

/-- Every unsigned test first masks its source with a single positive power of two. -/
theorem maskAnd_matches (j : Fin 32) (h : j.val % 8 < 7) :
    kernel.code[maskSelectSite j - 2]? = some ⟨none, .int
      ⟨.and, .int .b (maskTestWidth j), false, [some (maskTestReg j)],
        [.reg (maskAndSrc j), .imm (Int.ofNat (2 ^ (j.val % 8)))]⟩⟩ := by
  fin_cases j <;> first | contradiction | kernel_rfl

private theorem mask_trunc_toNat (w : BitVec 64) {n : Nat} (hn : n ≤ 64) :
    (truncBits n w).toNat = w.toNat % 2 ^ n := by
  have h : w.toNat % 2 ^ n < 2 ^ 64 :=
    (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) hn)
  rw [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The low bits of a mask word are preserved by Core's truncation. -/
theorem mask_bit_trunc (w : BitVec 64) {n j : Nat} (hn : n ≤ 64) (hj : j < n) :
    (truncBits n w).toNat.testBit j = w.toNat.testBit j := by
  rw [mask_trunc_toNat _ hn, Nat.testBit_mod_two_pow]
  simp [hj]

/-- A sign-bit comparison with -1 succeeds precisely when the sign bit is clear. -/
theorem mask_cmp_sign32 (w : BitVec 64) :
    compare .gt .s 32 (truncBits 32 w) (truncBits 32 (BitVec.ofInt 64 (-1))) =
      !(w.toNat.testBit 31) := by
  have hm : w.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have ht : (truncBits 32 w).toNat = w.toNat % 4294967296 :=
    mask_trunc_toNat _ (by decide)
  have hd : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  change decide (toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) <
    toSigned 32 (truncBits 32 w)) = _
  rw [← mask_bit_trunc w (n := 32) (by decide) (by decide)]
  rw [Nat.testBit_eq_decide_div_mod_eq, hd, toSigned, ht]
  norm_num only [Nat.reduceSub, Nat.reducePow, Nat.mod_mod, Int.reducePow]
  by_cases hh : w.toNat % 4294967296 < 2147483648
  · have hb : ¬(w.toNat % 4294967296 / 2147483648 % 2 = 1) := by omega
    simp [hh, hb]
    omega
  · have hb : w.toNat % 4294967296 / 2147483648 % 2 = 1 := by omega
    simp [hh, hb]
    omega

private theorem fold_bits_add (f : Nat → Bool) (l : List Nat) (a : Nat) :
    l.foldr (fun j s => if f j then s + 2 ^ j else s) a =
      l.foldr (fun j s => if f j then s + 2 ^ j else s) 0 + a := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldr_cons, ih]
    split <;> omega

private theorem bitsFrom_next (f : Nat → Bool) (n : Nat) :
    bitsFrom (n+1) f = bitsFrom n f + if f n then 2^n else 0 := by
  simp only [bitsFrom, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
  rw [fold_bits_add]
  cases f n <;> simp

private theorem bitsFrom_lt (f : Nat → Bool) (n : Nat) : bitsFrom n f < 2 ^ n := by
  induction n with
  | zero => simp [bitsFrom]
  | succ n ih =>
    rw [bitsFrom_next, Nat.pow_succ]
    cases f n <;> simp_all <;> omega

/-- The source bit selected by Core's positional bit builder. -/
theorem mask_bitsFrom_testBit (f : Nat → Bool) (n i : Nat) (hi : i < n) :
    (bitsFrom n f).testBit i = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bitsFrom_next]
    have hn := bitsFrom_lt f n
    by_cases he : i = n
    · subst n
      cases hf : f i
      · simp [Nat.testBit_lt_two_pow hn]
      · simp only [↓reduceIte]
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hd : (bitsFrom i f + 2 ^ i) / 2 ^ i = 1 :=
          Nat.div_eq_of_lt_le (by simp) (by omega)
        simp [hd]
    · have hlt : i < n := by omega
      cases hf : f n
      · simpa [hf] using ih hlt
      · rw [ite_eq_left rfl, Nat.add_comm, Nat.testBit_two_pow_add_gt hlt]
        exact ih hlt

/-- The extracted byte's sign is the corresponding bit of the original mask word. -/
theorem bfe_mask_sign (w : BitVec 64) {off : Nat} (hoff : off + 7 < 32) :
    (bfeBits .s 32 (truncBits 32 w).toNat off 8).testBit 7 = w.toNat.testBit (off+7) := by
  unfold bfeBits
  rw [mask_bitsFrom_testBit _ 32 7 (by decide)]
  have h : off + 7 ≤ 31 := by omega
  simp [h, mask_bit_trunc _ (by decide) hoff]


/-- For narrowing to a byte, the original word's signed interpretation leaves the low bits. -/
theorem signed_narrow_byte (w : BitVec 64) :
    (cvtIntBits false .s 8 .s 32 (truncBits 32 w)).toNat = w.toNat % 256 := by
  change (truncBits 8 (BitVec.ofInt 64 (toSigned 32 (truncBits 32 w)))).toNat = _
  rw [mask_trunc_toNat _ (by decide), BitVec.toNat_ofInt]
  have ht : (truncBits 32 w).toNat = w.toNat % 4294967296 := mask_trunc_toNat _ (by decide)
  simp only [toSigned, ht, Nat.reducePow, Nat.reduceSub, Nat.mod_mod, Int.reducePow]
  split <;> omega

/-- A sign-extended byte compares greater than -1 precisely when its sign bit is clear. -/
theorem mask_sign_extend (bits : BitVec 64) :
    compare .gt .s 16 (truncBits 16 (BitVec.ofInt 64 (toSigned 8 bits)))
      (truncBits 16 (BitVec.ofInt 64 (-1))) = !(bits.toNat.testBit 7) := by
  have h : toSigned 16 (truncBits 16 (BitVec.ofInt 64 (-1))) = -1 := rfl
  change decide (_ < _) = _
  rw [h, Nat.testBit_eq_decide_div_mod_eq, toSigned, mask_trunc_toNat _ (by decide),
    BitVec.toNat_ofInt]
  simp only [toSigned, Nat.reducePow, Nat.reduceSub, Nat.mod_mod, Int.reducePow]
  have hb := Nat.mod_lt bits.toNat (by decide : 0 < 256)
  have hc : bits.toNat / 128 % 2 = bits.toNat % 256 / 128 := by omega
  rw [hc]
  split_ifs <;> (rw [← decide_not, decide_eq_decide]; omega)

/-- Extract the word from the sign-extension of a mask byte. -/
def extendMaskByte (bits : BitVec 64) : BitVec 64 :=
  truncBits 16 (BitVec.ofInt 64 (toSigned 8 bits))

/-- The source of a sign test, following the initial signed byte or the two BFE operations. -/
def maskSignBits (w : BitVec 64) (group : Nat) : BitVec 64 :=
  let source := if group = 0 then w else
    BitVec.ofNat 64 (bfeBits .s 32 (truncBits 32 w).toNat (8 * group) 8)
  extendMaskByte (cvtIntBits false .s 8 .s 32 (truncBits 32 source))

/-- The exact words produced by the mask prelude. -/
def maskFields (w : BitVec 64) : List (Nat × Value) :=
  let x := truncBits 32 w
  [(1002, .bits 32 w), (155, .bits 16 (maskSignBits w 0)), (156, .bits 16 (truncBits 16 x)),
   (1003, .bits 32 (x >>> 8)), (157, .bits 16 (maskSignBits w 1)),
   (158, .bits 16 (truncBits 16 (truncBits 32 (x >>> 8)))),
   (1005, .bits 32 (x >>> 16)), (159, .bits 16 (maskSignBits w 2)),
   (160, (splitValue 32 (.bits 32 w)).2), (1007, .bits 32 (x >>> 24)),
   (161, .bits 16 (truncBits 16 (truncBits 32 (x >>> 24))))]

/-- The exact source bits of one of the 28 unsigned bit tests. -/
def maskAndBits (w : BitVec 64) (j : Fin 32) : BitVec 64 :=
  let x := truncBits 32 w
  if j.val % 8 = 0 then [w, x >>> 8, x >>> 16, x >>> 24].getD (j.val / 8) 0
  else [truncBits 16 x, truncBits 16 (truncBits 32 (x >>> 8)), truncBits 16 (w >>> 16),
    truncBits 16 (truncBits 32 (x >>> 24))].getD (j.val / 8) 0

/-- The unsigned source field comes from the matching prelude register. -/
theorem maskAndField (w : BitVec 64) (j : Fin 32) (h : j.val % 8 < 7) :
    (maskAndSrc j, .bits (maskTestWidth j) (maskAndBits w j)) ∈ maskFields w := by
  fin_cases j <;> first | contradiction | simp [maskAndSrc, maskTestWidth, maskAndBits, maskFields,
    List.getD, splitValue]
  all_goals
    have hb : w >>> 16 = BitVec.ofNat 64 (w.toNat / 65536) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      have hw := w.isLt
      omega
    rw [hb]

/-- Each unsigned source field preserves the bit tested by the corresponding AND. -/
theorem maskAndBit (w : BitVec 64) (j : Fin 32) (h : j.val % 8 < 7) :
    (maskAndBits w j).toNat.testBit (j.val % 8) = w.toNat.testBit j.val := by
  fin_cases j <;> first | contradiction | (simp (disch := decide) only [maskAndBits, List.getD,
    ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, BitVec.toNat_ushiftRight, Nat.testBit_shiftRight,
    mask_bit_trunc, Nat.reduceAdd])

private theorem trunc_mask_idem (w : BitVec 64) {n : Nat} (hn : n ≤ 64) :
    truncBits n (truncBits n w) = truncBits n w := by
  apply BitVec.eq_of_toNat_eq
  simp only [mask_trunc_toNat _ hn, Nat.mod_mod]

/-- The signed mask-byte comparison uses the sign of the selected byte. -/
theorem maskCmpSignByte (w : BitVec 64) (group : Nat) (hg : group < 3) :
    compare .gt .s 16 (truncBits 16 (maskSignBits w group)) (truncBits 16 (BitVec.ofInt 64 (-1))) =
      !(w.toNat.testBit (8 * group + 7)) := by
  unfold maskSignBits extendMaskByte
  rw [trunc_mask_idem _ (by decide), mask_sign_extend, signed_narrow_byte]
  have hbit (x : Nat) : (x % 256).testBit 7 = x.testBit 7 := by
    change (x % 2 ^ 8).testBit 7 = x.testBit 7
    simp only [Nat.testBit_mod_two_pow, Nat.reduceLT, decide_true, Bool.true_and]
  rw [hbit]
  apply congrArg Bool.not
  by_cases hz : group = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hbits : bfeBits .s 32 (truncBits 32 w).toNat (8 * group) 8 < 2^64 :=
      (bitsFrom_lt _ 32).trans (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbits, bfe_mask_sign w (by omega)]

/-- The signed top-bit test reads either a sign-extended byte or the original 32-bit word. -/
def maskCmpBits (w : BitVec 64) (j : Fin 32) : BitVec 64 :=
  if j.val = 31 then w else maskSignBits w (j.val / 8)

/-- Every sign test uses the matching signed prelude register. -/
theorem maskCmpField (w : BitVec 64) (j : Fin 32) (h : j.val % 8 = 7) :
    (maskTestReg j, .bits (maskTestWidth j) (maskCmpBits w j)) ∈ maskFields w := by
  fin_cases j <;> first | contradiction | simp [maskTestReg, maskTestWidth, maskCmpBits, maskFields,
    List.getD]

/-- Signed comparisons supply the inverse predicate of exactly the targeted mask bit. -/
theorem maskCmpBit (w : BitVec 64) (j : Fin 32) (h : j.val % 8 = 7) :
    compare (maskTestCmp j) (maskTestKind j) (maskTestWidth j)
        (truncBits (maskTestWidth j) (maskCmpBits w j))
        (truncBits (maskTestWidth j) (BitVec.ofInt 64 (maskTestImm j))) =
      !(w.toNat.testBit j.val) := by
  fin_cases j <;> first
  | contradiction
  | exact mask_cmp_sign32 w
  | exact maskCmpSignByte w _ (by decide)

/-- Start of this slot's contiguous mask instructions. -/
def maskStart (j : Fin 32) : Nat := maskSelectSite j - if j.val % 8 = 7 then 1 else 2

/-- The number of local instructions from one slot's test through its selection. -/
def maskSteps (j : Fin 32) : Nat := if j.val % 8 = 7 then 2 else 3

private theorem maskChoice_bounds (j : Fin 32) : 304 ≤ maskSelectSite j ∧
    maskSelectSite j ≤ 393 := by fin_cases j <;> decide

private theorem maskChoice_width (j : Fin 32) :
    maskTestWidth j = 16 ∨ maskTestWidth j = 32 := by fin_cases j <;> decide

private theorem maskChoice_distinct (j : Fin 32) : maskTestReg j ≠ maskPredicate j ∧
    maskTestReg j ≠ maskSelectDst j ∧ maskPredicate j ≠ maskSelectDst j := by
  fin_cases j <;> decide

/-- The unsigned comparison supplies the mask bit in the polarity of the following select. -/
theorem maskUnsigned_cmp (w : BitVec 64) (j : Fin 32) (hj : j.val % 8 < 7) :
    let n := maskTestWidth j
    let x := truncBits n (maskAndBits w j) &&&
      truncBits n (BitVec.ofInt 64 (Int.ofNat (2 ^ (j.val % 8))))
    compare (maskTestCmp j) (maskTestKind j) n (truncBits n x)
      (truncBits n (BitVec.ofInt 64 (maskTestImm j))) =
      (w.toNat.testBit j.val == decide (j.val % 8 = 0)) := by
  have hk : maskTestKind j = .b := by simp [maskTestKind, show j.val % 8 ≠ 7 by omega]
  have hi : maskTestImm j = 0 := by simp [maskTestImm, show j.val % 8 ≠ 7 by omega]
  have hpow : truncBits (maskTestWidth j) (BitVec.ofInt 64 (Int.ofNat (2 ^ (j.val % 8)))) =
      BitVec.ofNat 64 (2 ^ (j.val % 8)) := by fin_cases j <;> rfl
  have hw : maskTestWidth j ≤ 64 := by rcases maskChoice_width j with h | h <;> omega
  have hp : j.val % 8 < maskTestWidth j := by rcases maskChoice_width j with h | h <;> omega
  have h := (mask_testBit (maskAndBits w j) hp hw).trans (maskAndBit w j hj)
  have hzero : truncBits (maskTestWidth j) (BitVec.ofInt 64 0) = 0 := by
    fin_cases j <;> rfl
  dsimp only
  rw [hk, hi, hzero, hpow]
  by_cases hz : j.val % 8 = 0
  · simpa [maskTestCmp, hz] using h
  · simp only [maskTestCmp, hz, show j.val % 8 ≠ 7 by omega, ↓reduceIte]
    have hn (x : BitVec 64) : compare .eq .b (maskTestWidth j) x 0 =
        !compare .ne .b (maskTestWidth j) x 0 := by simp [compare]
    rw [hn, h]
    simp

/-- Execute one mask test and preserve the input facts and the selected score. -/
theorem run_maskChoice (j : Fin 32) (w : BitVec 64) {t : TState} {F : List (Nat × Value)}
    {score : Value} (hat : At t (maskStart j) F) (hr : (2918 + j.val, score) ∈ F)
    (hbytes : score.bytes = 4) (hmask : ∀ q ∈ maskFields w, q ∈ F)
    (hframe : ∀ q ∈ F, q.1 ≠ maskPredicate j ∧ q.1 ≠ maskSelectDst j ∧
      (j.val % 8 < 7 → q.1 ≠ maskTestReg j)) :
    ∃ u, run kernel asms L g (maskSteps j) t = some u ∧ At u (maskSelectSite j + 1)
      ((maskSelectDst j, if w.toNat.testBit j.val then score else negInf) :: F) := by
  let direct := decide (j.val % 8 = 0)
  have hpc := maskChoice_bounds j
  have hw := maskChoice_width j
  have hsep := maskChoice_distinct j
  have ht : 302 ≤ maskSelectSite j - 1 ∧ maskSelectSite j - 1 ≤ 393 := by omega
  have he : maskSelectSite j - 1 + 1 = maskSelectSite j := by omega
  have hrule : (⟨.setp (maskTestCmp j) none, .int (maskTestKind j) (maskTestWidth j), false,
      [some (maskPredicate j)], [.reg (maskTestReg j), .imm (maskTestImm j)]⟩ :
        IntInstr).rule = some .threadInt := by fin_cases j <;> rfl
  have hsel : kernel.code[maskSelectSite j]? = some ⟨none, .int ⟨.selp, .int .b 32, false,
    [some (maskSelectDst j)],
    [if direct then .reg (2918 + j.val) else .imm (-8388608),
      if direct then .imm (-8388608) else .reg (2918 + j.val),
      .reg (maskPredicate j)]⟩⟩ := by
    simpa [direct] using maskSelect_matches j
  let pick := w.toNat.testBit j.val
  have hfinish {v : TState}
      (hav : At v (maskSelectSite j)
        ((maskPredicate j, .pred (pick == direct)) :: F)) :
      ∃ u, run kernel asms L g 1 v = some u ∧ At u (maskSelectSite j + 1)
        ((maskSelectDst j, if pick then score else negInf) :: F) := by
    have hk : ∀ q ∈ ((maskPredicate j, .pred (pick == direct)) :: F),
        q.1 ≠ maskSelectDst j := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hsep.2.2
      · exact (hframe q hq).2.1
    obtain ⟨u, hu, hau⟩ := run_mask_select (L := L) (g := g) direct pick score hpc hsel hav
      hav.2.2.2.2.1 (holds_mem hav.2.2.2.2.2 hr) hbytes hk
    exact ⟨u, hu, hau.mono ⟨hau.2.2.2.2.1, hau.2.2.2.2.2.2⟩⟩
  by_cases hj : j.val % 8 < 7
  · have hnot : j.val % 8 ≠ 7 := by omega
    have ha : At t (maskSelectSite j - 2) F := by simpa [maskStart, hnot] using hat
    have hstart : 302 ≤ maskSelectSite j - 2 ∧ maskSelectSite j - 2 ≤ 393 := by omega
    have hdst := holds_mem ha.2.2.2.2 (hmask _ (maskAndField w j hj))
    obtain ⟨u, hu, hau⟩ := run_mask_and (L := L) (g := g)
      (Int.ofNat (2 ^ (j.val % 8))) (maskAndBits w j) hstart hw (maskAnd_matches j hj)
      ha hdst (fun q hq => (hframe q hq).2.2 hj)
    let x := truncBits (maskTestWidth j) (maskAndBits w j) &&&
      truncBits (maskTestWidth j) (BitVec.ofInt 64 (Int.ofNat (2 ^ (j.val % 8))))
    have hau' : At u (maskSelectSite j - 1) ((maskTestReg j, .bits (maskTestWidth j) x) :: F) := by
      rw [show maskSelectSite j - 1 = maskSelectSite j - 2 + 1 by omega]
      exact hau
    obtain ⟨v, hv, hav⟩ := run_mask_cmp (L := L) (g := g) (maskTestKind j) (maskTestCmp j)
      (maskTestImm j) x ht hw (maskTest_matches j) hrule hau' hau'.2.2.2.2.1 (by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hsep.1
        · exact (hframe q hq).1)
    rw [he, maskUnsigned_cmp w j hj] at hav
    have hav' : At v (maskSelectSite j) ((maskPredicate j, .pred (pick == direct)) :: F) :=
      hav.mono ⟨hav.2.2.2.2.1, hav.2.2.2.2.2.2⟩
    obtain ⟨u', hrun, hat'⟩ := hfinish hav'
    exact ⟨u', by simpa [maskSteps, hnot] using run_comp (run_comp hu hv) hrun, hat'⟩
  · have hs : j.val % 8 = 7 := by have := Nat.mod_lt j.val (by decide : 0 < 8); omega
    have hat' : At t (maskSelectSite j - 1) F := by simpa [maskStart, hs] using hat
    have hr' := holds_mem hat'.2.2.2.2 (hmask _ (maskCmpField w j hs))
    obtain ⟨v, hv, hav⟩ := run_mask_cmp (L := L) (g := g) (maskTestKind j) (maskTestCmp j)
      (maskTestImm j) (maskCmpBits w j) ht hw (maskTest_matches j) hrule hat' hr'
      (fun q hq => (hframe q hq).1)
    rw [he, maskCmpBit w j hs] at hav
    have hav' : At v (maskSelectSite j) ((maskPredicate j, .pred (pick == direct)) :: F) := by
      simpa [direct, pick, hs] using hav
    obtain ⟨u, hu, hau⟩ := hfinish hav'
    exact ⟨u, by simpa [maskSteps, hs] using run_comp hv hu, hau⟩

/-- The fields used by all mask tests are extracted from the actual returned word. -/
theorem run_maskFields (d : D) (w : BitVec 64) {t : TState}
    (hat : At t 290 ((1002, .bits 32 w) :: factsFrom ((Flow.live 289).filter tracked.contains)
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 12 t = some u ∧
      At u 302 (maskFields w ++ factsFrom ((Flow.live 302).filter tracked.contains)
        (valueOf P L g d)) := by
  obtain ⟨t', ht', hat'⟩ := run_290_292 d w hat
  obtain ⟨t'', ht'', hat''⟩ := run_292_299 d w hat'
  obtain ⟨t₃, ht₃, hat₃⟩ := run_299_300 hat'' (w := w) (by
    exact holds_mem hat''.2.2.2.2 (by simp)) (by
    rintro ⟨r, v⟩ hv
    simp only [List.mem_cons, Prod.mk.injEq] at hv
    rcases hv with h | h | h | h | h | h | h | h | h
    all_goals first
      | (change r ≠ 160; simp [h.1])
      | (obtain ⟨r', hr', hh⟩ := List.mem_map.mp h
         obtain rfl : r' = r := congrArg Prod.fst hh
         exact fun he => (by decide +kernel : 160 ∉ (Flow.live 299).filter
           tracked.contains) (he ▸ hr')))
  obtain ⟨t₄, ht₄, hat₄⟩ : ∃ u, run kernel asms L g 2 t₃ = some u ∧
      At u 302 ((1002, .bits 32 w) :: (155, .bits 16 (maskSignBits w 0)) ::
        (156, .bits 16 (truncBits 16 (truncBits 32 w))) ::
        (1003, .bits 32 (truncBits 32 w >>> 8)) :: (157, .bits 16 (maskSignBits w 1)) ::
        (158, .bits 16 (truncBits 16 (truncBits 32 (truncBits 32 w >>> 8)))) ::
        (1005, .bits 32 (truncBits 32 w >>> 16)) :: (159, .bits 16 (maskSignBits w 2)) ::
        (160, (splitValue 32 (.bits 32 w)).2) ::
        (1007, .bits 32 (truncBits 32 w >>> 24)) ::
        (161, .bits 16 (truncBits 16 (truncBits 32 (truncBits 32 w >>> 24)))) ::
        factsFrom ((Flow.live 302).filter tracked.contains) (valueOf P L g d)) := by
    seg_fp hat₃ using rfl
  exact ⟨t₄, run_comp (run_comp (run_comp ht' ht'') ht₃) ht₄, hat₄⟩

private theorem mask_holds_of_mem {r : Nat → Option Value} {F : List (Nat × Value)}
    (h : ∀ q ∈ F, r q.1 = some q.2) : Holds r F := by
  induction F with
  | nil => trivial
  | cons q qs ih => exact ⟨h q (by simp), ih (fun a ha => h a (List.mem_cons_of_mem _ ha))⟩

/-- Register facts produced by the first `n` mask selections. -/
def maskedPrefix (d : D) (w : BitVec 64) (n : Nat) : List (Nat × Value) :=
  ((List.finRange 32).filter fun j => j.val < n).map fun j =>
    (maskSelectDst j, if w.toNat.testBit j.val then d.ownScores.getD j.val (b32 0) else negInf)

/-- The next selection, or the first local instruction of the shared exchange. -/
def maskBoundary (n : Nat) : Nat := if h : n < 32 then maskStart ⟨n, h⟩ else 394

private theorem maskBoundary_succ (j : Fin 32) : maskSelectSite j + 1 = maskBoundary (j.val+1) := by
  fin_cases j <;> rfl

private theorem mask_prior_distinct (i j : Fin 32) (h : i.val < j.val) :
    maskSelectDst i ≠ maskPredicate j ∧ maskSelectDst i ≠ maskSelectDst j ∧
      (j.val % 8 < 7 → maskSelectDst i ≠ maskTestReg j) := by
  revert i j
  decide +kernel

private theorem maskPrefix_mem (d : D) (w : BitVec 64) {n : Nat} {q : Nat × Value}
    (h : q ∈ maskedPrefix d w n) :
    ∃ j : Fin 32, j.val < n ∧
      q = (maskSelectDst j, if w.toNat.testBit j.val then d.ownScores.getD j.val (b32 0)
        else negInf) := by
  obtain ⟨j, hj, hq⟩ := List.mem_map.mp h
  exact ⟨j, of_decide_eq_true (List.mem_filter.mp hj).2, hq.symm⟩

/-- All 32 choices execute from the shared prelude, retaining the selected values. -/
theorem run_maskChoices (d : D) (w : BitVec 64) {t : TState} {F : List (Nat × Value)}
    (hat : At t 302 F) (hmask : ∀ q ∈ maskFields w, q ∈ F)
    (hscores : ∀ j : Fin 32, (2918 + j.val, d.ownScores.getD j.val (b32 0)) ∈ F)
    (hready : exchangeReady d = true)
    (hframe : ∀ (j : Fin 32) q, q ∈ F → q.1 ≠ maskPredicate j ∧ q.1 ≠ maskSelectDst j ∧
      (j.val % 8 < 7 → q.1 ≠ maskTestReg j)) :
    ∃ u n, run kernel asms L g n t = some u ∧ At u 394 (maskedPrefix d w 32 ++ F) := by
  have hw := (Bool.and_eq_true_iff.mp hready).1
  have runPrefix (count : Nat) (hc : count ≤ 32) :
      ∃ u n, run kernel asms L g n t = some u ∧
        At u (maskBoundary count) (maskedPrefix d w count ++ F) := by
    induction count with
    | zero => exact ⟨t, 0, rfl, hat⟩
    | succ n ih =>
      obtain ⟨v, fuel, hrun, hav⟩ := ih (by omega)
      let j : Fin 32 := ⟨n, by omega⟩
      have ha : At v (maskStart j) (maskedPrefix d w n ++ F) := by
        simpa [maskBoundary, j, show n < 32 by omega] using hav
      have hkeep : ∀ q ∈ maskedPrefix d w n ++ F,
          q.1 ≠ maskPredicate j ∧ q.1 ≠ maskSelectDst j ∧
            (j.val % 8 < 7 → q.1 ≠ maskTestReg j) := by
        intro q hq
        rcases List.mem_append.mp hq with h | h
        · obtain ⟨i, hi, rfl⟩ := maskPrefix_mem d w h
          exact mask_prior_distinct i j hi
        · exact hframe j q h
      obtain ⟨u, hu, hau⟩ := run_maskChoice (L := L) (g := g) j w ha
        (List.mem_append_right _ (hscores j))
        (Assumptions.scoreHalf_bytes (scoreHalf_getD hw j.val))
        (fun q hq => List.mem_append_right _ (hmask q hq)) hkeep
      refine ⟨u, fuel + maskSteps j, run_comp hrun hu, ?_⟩
      rw [← maskBoundary_succ j]
      refine hau.mono (mask_holds_of_mem fun q hq => ?_)
      rcases List.mem_append.mp hq with hn | hf
      · obtain ⟨k, hk, rfl⟩ := maskPrefix_mem d w hn
        by_cases he : k.val < n
        · exact holds_mem hau.2.2.2.2.2 (List.mem_append_left _
            (List.mem_map.mpr ⟨k, by simpa using he, rfl⟩))
        · have heq : k = j := Fin.ext (by dsimp [j]; omega)
          subst k
          exact hau.2.2.2.2.1
      · obtain ⟨r, v⟩ := q
        exact holds_mem hau.2.2.2.2.2 (List.mem_append_right _ hf)
  exact runPrefix 32 (by decide)

private def maskLive : List Nat := (Flow.live 302).filter tracked.contains

private theorem maskInput_frame (j : Fin 32) (r : Nat)
    (hr : r ∈ [1002, 155, 156, 1003, 157, 158, 1005, 159, 160, 1007, 161] ++ maskLive) :
    r ≠ maskPredicate j ∧ r ≠ maskSelectDst j ∧
      (j.val % 8 < 7 → r ≠ maskTestReg j) := by
  revert j r
  decide +kernel

private theorem ownMask_value (d : D) (w : BitVec 64) (j : Fin 32) :
    valueOf P L g { d with maskWord := w } (maskSelectDst j) =
      (if w.toNat.testBit j.val then d.ownScores.getD j.val (b32 0) else negInf) := by
  fin_cases j <;> rfl

private theorem mask_after_choices (d : D) (w : BitVec 64) {t : TState}
    (hat : At t 394 (maskedPrefix d w 32 ++
      (maskFields w ++ factsFrom maskLive (valueOf P L g d)))) :
    At t 394 (factsFrom (exchangeLive 0) (valueOf P L g { d with maskWord := w })) := by
  apply hat.mono
  refine holds_of_pointwise fun r hr => ?_
  by_cases h : r ∈ (List.finRange 32).map maskSelectDst
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
    have hp : (maskSelectDst j,
        if w.toNat.testBit j.val then d.ownScores.getD j.val (b32 0) else negInf) ∈
        maskedPrefix d w 32 := by
      apply List.mem_map.mpr
      exact ⟨j, List.mem_filter.mpr ⟨hj, decide_eq_true j.isLt⟩, rfl⟩
    rw [ownMask_value]
    exact holds_mem hat.2.2.2.2 (List.mem_append_left _ hp)
  · have hranges : ¬ (1009 ≤ r ∧ r ≤ 1043) ∧
        ¬ (3145 ≤ r ∧ r ≤ 3173 ∧ (r - 3145) % 4 = 0) ∧ r ∈ maskLive :=
      (by decide +kernel : ∀ r ∈ exchangeLive 0, r ∉ (List.finRange 32).map maskSelectDst →
        ¬ (1009 ≤ r ∧ r ≤ 1043) ∧
        ¬ (3145 ≤ r ∧ r ≤ 3173 ∧ (r - 3145) % 4 = 0) ∧ r ∈ maskLive) r hr h
    have hv : valueOf P L g { d with maskWord := w } r = valueOf P L g d r := by
      simp only [valueOf, hranges.1, hranges.2.1, ↓reduceIte]
      rfl
    rw [hv]
    exact holds_mem hat.2.2.2.2 (List.mem_append_right _
      (List.mem_append_right _ (mem_factsFrom hranges.2.2)))

/-- Run the mask and the first peer pack from a successfully rebuilt shared mask. -/
theorem run_mask_exchange (d : D) (w : BitVec 64) {t : TState}
    (hready : exchangeReady d = true)
    (hat : At t 290 ((1002, .bits 32 w) :: factsFrom ((Flow.live 289).filter tracked.contains)
      (valueOf P L g d))) :
    ∃ u fuel, run kernel asms L g fuel t = some u ∧ At u 403
      (facts P L g { d with site := .exchStore 0, maskWord := w }) := by
  obtain ⟨u, hu, hau⟩ := run_maskFields d w hat
  have hscores (j : Fin 32) :
      (2918 + j.val, d.ownScores.getD j.val (b32 0)) ∈
        maskFields w ++ factsFrom maskLive (valueOf P L g d) := by
    apply List.mem_append_right
    have hj : 2918 + j.val ∈ maskLive := by
      revert j
      decide +kernel
    have hv : valueOf P L g d (2918 + j.val) = d.ownScores.getD j.val (b32 0) := by
      have h : 2918 ≤ 2918 + j.val ∧ 2918 + j.val < 2950 := by have := j.isLt; omega
      rw [valueOf, ite_eq_left h, Nat.add_sub_cancel_left]
    rw [← hv]
    exact mem_factsFrom hj
  obtain ⟨v, n, hv, hav⟩ := run_maskChoices d w hau (fun q hq => List.mem_append_left _ hq)
    hscores hready (by
      intro j q hq
      apply maskInput_frame j q.1
      rcases List.mem_append.mp hq with h | h
      · apply List.mem_append_left
        exact (show q.1 ∈ (maskFields w).map Prod.fst from
          List.mem_map.mpr ⟨q, h, rfl⟩)
      · apply List.mem_append_right
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact hr)
  obtain ⟨z, hz, haz⟩ := run_to_exchange 0 { d with maskWord := w } hready
    (mask_after_choices d w hav)
  exact ⟨z, 12 + n + 9, run_comp (run_comp hu hv) hz, haz⟩

/-- The shared mask read reaches the first peer store with the exact selected scores. -/
theorem step_maskRead (hpre : Pre P L mem0) (d : D) (hd : d.site = .maskRead) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hi hc hf => by
    obtain ⟨a, bytes, he, hloc, hsize, hu⟩ := fires_maskRead hpre hd hat hi hc hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
    have hl : siteLoc L g .maskRead d.block d.sub = some a.loc := by
      simpa only [hd] using hloc
    simp only [next, nextSite, hd, he, hl, hsize, Site.elemBytes, true_and, ↓reduceIte]
    split
    · rename_i w hw
      split_ifs with hready
      · let d' : D := { d with site := .exchStore 0, maskWord := w }
        have hword := at_maskRead_word hd hat hi hu hw
        obtain ⟨v, n, hr, hav⟩ := run_mask_exchange d w hready hword
        refine Or.inl (Or.inr ⟨d', v, rfl, run_rtg hr, ?_, ?_⟩)
        · exact ⟨hav.1, hav.2.1.trans hsub.symm,
            hav.2.2.1.trans (siteAcc_nil d' hsub).symm, hav.2.2.2.1, hav.2.2.2.2⟩
        · refine { hi with
            epilogueLast := ?_, rescaleArm := ?_, subLt := ?_, armSite := ?_,
            exitWarp := ?_, preloop := ?_, rowTotal := ?_, exchangeWords := ?_ }
          all_goals simp [d', Site.inEpilogue, Site.inRescale, Site.elems, hsub]
          exact hready
      · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
