-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Steps

@[expose] public section

/-! # The reference invariant of the startup phase is kept: the scan of the offsets array

The 21 loads of `cu_seqlens` (instructions 115 to 291) and the code between them: the two
entries of the thread's own sequence, then the tile counts of the sequences before it, added
up by a loop unrolled eight times (`load_3` to `load_10`, loop head at instruction 129 with the
carried registers `%r1791`, `%r1792`, `%r1793`, `%rd1166`), a block of four (`load_11` to
`load_15`), a block of two (`load_17` to `load_19`) and a last single sequence (`load_16`,
`load_20`).

One lemma per load, in the form `LoadOK`: the load reads entry `b + k` of the array through a
pointer register that holds `cu_seqlens + 8 b` (this is what places the read in the array: it
is the input of the tracking theorem and of the assumption `inputReadOnly`), and when the
loaded word is that entry the state the transition gives is at a position of the phase with
its invariant. The closed form at the loop head (`AtPos` at `load 3`): with `i` the sequence
index the loop has reached (`i % 8 = 0`, `i + 8 ≤ seq`),

    %r1791 = %r1792 = i,   %r1793 = ft i,   %rd1166 = cu i,   %rd20 = cu_seqlens + 8 i

where `cu i` is entry `i` and `ft i` the number of tiles of the sequences before `i`.

Each proof decides the branch conditions of the transition in closed form first (they compare
the sequence index, its remainders modulo 8, 4 and 2 and the loop counter), then closes the
four parts of the successor's invariant with the facts of the position, the equations of
`Arith` instantiated at the entries involved (`cu_r32`, `step_word`, `ptr_word`, `len_word`,
`tiles_word`) and `omega` for the index arithmetic. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

/-- **A load of the scan**: it reads entry `b + k` through the pointer register `ptr`, and the
transition `aft` on that entry keeps the invariant. -/
def LoadOK (P : Params) (g : Nat) (j : Fin 21) (ptr k : Nat) (w : Nat → BitVec 64)
    (aft : BitVec 64 → D) : Prop :=
  ∃ b, w ptr = W (P.offsetsBase + 8 * b) ∧ b + k ≤ P.sequences ∧
    Succ P g (.load j) w ⟨0, 0, 0, 0, 0, 0⟩ (aft (W (cu P (b + k))))

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

/-- `scan_pre`: the facts of a load position, with `s` for the sequence index. -/
syntax "scan_pre" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| scan_pre) => `(tactic| (
      have e0 := h.base.offs
      dsimp only at e0
      obtain ⟨-, hb, h⟩ := h
      have hsq := seq_lt hpre g
      have hN := hpre.sequencesLt
      obtain ⟨s, hs⟩ : ∃ s, seqOf P g = s := ⟨_, rfl⟩
      simp only [AtPos, finVal, Flags, flagsOf, Cta, Own, Loop8, Mid, hs] at h hsq))

/-- `scan_pos [lemmas]`: register facts of the successor, with the index arithmetic by
`omega`. -/
syntax "scan_pos" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| scan_pos [$ls,*]) => `(tactic| (
      (try file_simp [AtPos, finVal, Flags, flagsOf, Scan, Cta, Own, Loop8, Mid,
        Bool.false_eq_true, ↓reduceIte, and_self, and_true, true_and, hs, e0, i32_zero,
        Nat.add_zero, Nat.mul_zero, Bool.not_true, Bool.not_false, $ls,*]) <;>
      (try w32_norm) <;> (try simp only [and_self, and_true, true_and]) <;>
      (try ((repeat' apply And.intro) <;> first | omega | rfl | (congr 1; omega)))))

/-- `scan_at pos [lemmas]`: the successor is at `pos`. -/
syntax "scan_at " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| scan_at $pos [$ls,*]) => `(tactic| (
      refine ⟨$pos, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · ref_site [hs, e0, i32_zero, Bool.not_true, Bool.not_false, $ls,*]
      · ref_base [hs, e0, i32_zero, Bool.not_true, Bool.not_false, $ls,*]
      · scan_pos [$ls,*]
      · ref_led
      · ref_el
      · ref_left))

/-! ### The two entries of the thread's sequence -/

theorem st_load_0 (hpre : Pre P L mem0) (h : RefAt P g (.load 0) ⟨.load 0, w, p, x⟩) :
    LoadOK P g 0 2264 0 w (after_load_0 L g ⟨.load 0, w, p, x⟩) := by
  scan_pre
  refine ⟨s, h.2.2.2, by omega, ?_⟩
  scan_at (.load 1) [after_load_0, h]

theorem st_load_1 (hpre : Pre P L mem0) (h : RefAt P g (.load 1) ⟨.load 1, w, p, x⟩) :
    LoadOK P g 1 2264 1 w (after_load_1 L g ⟨.load 1, w, p, x⟩) := by
  scan_pre
  refine ⟨s, h.2.2.2.1, by omega, ?_⟩
  have hs32 : s < 2 ^ 32 := by omega
  have r1 := cu_r32 hpre (i := s + 1) (by omega)
  have r0 := cu_r32 hpre (i := s) (by omega)
  have l0 := len_word hpre (i := s) hsq
  have t0 := tiles_word hpre (i := s) hsq
  have p0 := ptr_word hpre (j := 0) (by omega)
  have a7 := and7 hs32
  have a3 := and3 hs32
  have a8 := and8 (s := s) (by omega)
  have m8 : s % 8 < 2 ^ 32 := by omega
  have m4 : s % 4 < 2 ^ 32 := by omega
  by_cases h0 : s = 0
  · have c15 := (cmp_eq0 hs32).trans (decide_eq_true h0)
    have ef : ft P s = 0 := by rw [h0]; exact ft_zero P
    scan_at (.elect 4) [after_load_1, h, c15, r1, r0, l0, t0, ef]
  · have c15 := (cmp_eq0 hs32).trans (decide_eq_false h0)
    by_cases h8 : s < 8
    · have c16 := (cmp_lt8 hs32).trans (decide_eq_true h8)
      by_cases h4 : s % 8 < 4
      · have c19 := (cmp_lt4 m8).trans (decide_eq_true h4)
        by_cases h1 : s % 4 ≠ 1
        · have c21 := (cmp_ne1 m4).trans (decide_eq_true h1)
          have e4 : s - s % 4 = 0 := by omega
          scan_at (.load 17) [after_load_1, h, c15, c16, c19, c21, a7, a3, p0, e4,
            ft_zero]
        · have c21 := (cmp_ne1 m4).trans (decide_eq_false h1)
          have e4 : s - 1 = 0 := by omega
          scan_at (.load 16) [after_load_1, h, c15, c16, c19, c21, a7, a3, p0, e4,
            ft_zero]
      · have c19 := (cmp_lt4 m8).trans (decide_eq_false h4)
        have e8 : s - s % 8 = 0 := by omega
        scan_at (.load 11) [after_load_1, h, c15, c16, c19, a7, a3, p0, e8, ft_zero]
    · have c16 := (cmp_lt8 hs32).trans (decide_eq_false h8)
      scan_at (.load 2) [after_load_1, h, c15, c16, a7, a8]

/-! ### The loop of eight -/

theorem st_load_2 (hpre : Pre P L mem0) (h : RefAt P g (.load 2) ⟨.load 2, w, p, x⟩) :
    LoadOK P g 2 2247 0 w (after_load_2 L g ⟨.load 2, w, p, x⟩) := by
  scan_pre
  refine ⟨0, by simpa using e0, by omega, ?_⟩
  have p0 := ptr_word hpre (j := 0) (by omega)
  refine ⟨.load 3, ⟨rfl, ?_, ?_⟩, by ref_led, by ref_el, by ref_left⟩
  · ref_base [after_load_2]
  · simp only [AtPos, finVal]
    refine ⟨?_, ?_, ?_, ?_, 0, ?_, ?_, ?_, ?_⟩ <;>
      scan_pos [after_load_2, h, p0, ft_zero]

/-- `loop_step j k prev acc after`: the load `j` inside the loop of eight reads entry
`i + k + 1`; its predecessor entry `i + k` is in the register the position names. -/
syntax "loop_step " term:max num " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| loop_step $pos $k [$ls,*]) => `(tactic| (
      scan_pre
      obtain ⟨hf, hr, hc, ho, i, hl, h98, hm⟩ := h
      refine ⟨i, hl.2.2.2.2.2, by omega, ?_⟩
      have r1 := cu_r32 hpre (i := i + ($k + 1)) (by omega)
      have r0 := cu_r32 hpre (i := i + $k) (by omega)
      have sw := step_word hpre (i := i + $k) (j := i + ($k + 1)) (by omega) (by omega)
      simp only [Nat.add_zero, Nat.reduceAdd] at r1 r0 sw
      refine ⟨$pos, ⟨rfl, ?_, ?_⟩, by ref_led, by ref_el, (by
        simp only [leftP, loopOf, pcOf, finVal, getLit]
        (try file_simp [$ls,*])
        omega)⟩
      · ref_base [$ls,*]
      · simp only [AtPos, finVal]
        refine ⟨?_, ?_, ?_, ?_, i, ?_, ?_, ?_⟩ <;>
          scan_pos [$ls,*, hf, hr, hc, ho, hl, h98, hm, r1, r0, sw]))

theorem st_load_3 (hpre : Pre P L mem0) (h : RefAt P g (.load 3) ⟨.load 3, w, p, x⟩) :
    LoadOK P g 3 2266 1 w (after_load_3 L g ⟨.load 3, w, p, x⟩) := by
  loop_step (.load 4) 0 [after_load_3]

theorem st_load_4 (hpre : Pre P L mem0) (h : RefAt P g (.load 4) ⟨.load 4, w, p, x⟩) :
    LoadOK P g 4 2266 2 w (after_load_4 L g ⟨.load 4, w, p, x⟩) := by
  loop_step (.load 5) 1 [after_load_4]

theorem st_load_5 (hpre : Pre P L mem0) (h : RefAt P g (.load 5) ⟨.load 5, w, p, x⟩) :
    LoadOK P g 5 2266 3 w (after_load_5 L g ⟨.load 5, w, p, x⟩) := by
  loop_step (.load 6) 2 [after_load_5]

theorem st_load_6 (hpre : Pre P L mem0) (h : RefAt P g (.load 6) ⟨.load 6, w, p, x⟩) :
    LoadOK P g 6 2266 4 w (after_load_6 L g ⟨.load 6, w, p, x⟩) := by
  loop_step (.load 7) 3 [after_load_6]

theorem st_load_7 (hpre : Pre P L mem0) (h : RefAt P g (.load 7) ⟨.load 7, w, p, x⟩) :
    LoadOK P g 7 2266 5 w (after_load_7 L g ⟨.load 7, w, p, x⟩) := by
  loop_step (.load 8) 4 [after_load_7]

theorem st_load_8 (hpre : Pre P L mem0) (h : RefAt P g (.load 8) ⟨.load 8, w, p, x⟩) :
    LoadOK P g 8 2266 6 w (after_load_8 L g ⟨.load 8, w, p, x⟩) := by
  loop_step (.load 9) 5 [after_load_8]

theorem st_load_9 (hpre : Pre P L mem0) (h : RefAt P g (.load 9) ⟨.load 9, w, p, x⟩) :
    LoadOK P g 9 2266 7 w (after_load_9 L g ⟨.load 9, w, p, x⟩) := by
  loop_step (.load 10) 6 [after_load_9]

/-- The back edge of the loop of eight, and its exits to the remainder blocks. -/
theorem st_load_10 (hpre : Pre P L mem0) (h : RefAt P g (.load 10) ⟨.load 10, w, p, x⟩) :
    LoadOK P g 10 2266 8 w (after_load_10 L g ⟨.load 10, w, p, x⟩) := by
  scan_pre
  obtain ⟨hf, hr, hc, ho, i, hl, h98, hm⟩ := h
  refine ⟨i, hl.2.2.2.2.2, by omega, ?_⟩
  have hs32 : s < 2 ^ 32 := by omega
  have m8 : s % 8 < 2 ^ 32 := by omega
  have m4 : s % 4 < 2 ^ 32 := by omega
  have r1 := cu_r32 hpre (i := i + 8) (by omega)
  have r0 := cu_r32 hpre (i := i + 7) (by omega)
  have sw := step_word hpre (i := i + 7) (j := i + 8) (by omega) (by omega)
  have e97 := addi8 (a := i) (by omega)
  have c17 := cmp_ne (a := i + 8) (b := s - s % 8) (by omega) (by omega)
  have pw := ptr_word hpre (j := i + 8) (by omega)
  have r1s := cu_r32 hpre (i := s + 1) (by omega)
  have r0s := cu_r32 hpre (i := s) (by omega)
  have l0 := len_word hpre (i := s) hsq
  have t0 := tiles_word hpre (i := s) hsq
  have a3 := and3 hs32
  by_cases hne : i + 8 ≠ s - s % 8
  · have c17t := c17.trans (decide_eq_true hne)
    have h97 : (after_load_10 L g ⟨.load 10, w, p, x⟩ (W (cu P (i + 8)))).w 2097 = W (i + 8) := by
      scan_pos [after_load_10, hf, hr, hc, ho, hl, h98, hm, e97, c17t, r1, r0, sw, pw]
    have h97' : w 2097 = W i := hl.2.2.2.2.1
    refine ⟨.load 3, ⟨?_, ?_, ?_⟩, by ref_led, by ref_el, (by
      simp only [leftP, loopOf, pcOf, finVal, getLit, h97, h97', W, BitVec.toNat_ofNat]
      omega)⟩
    · ref_site [after_load_10, hl, h98, hm, e97, c17t]
    · ref_base [after_load_10, hl, h98, hm, e97, c17t]
    · simp only [AtPos, finVal]
      refine ⟨?_, ?_, ?_, ?_, i + 8, ?_, ?_, ?_, ?_⟩ <;>
        scan_pos [after_load_10, hf, hr, hc, ho, hl, h98, hm, e97, c17t, r1, r0, sw, pw]
  · have c17f := c17.trans (decide_eq_false hne)
    have he : i + 8 = s - s % 8 := by omega
    by_cases h80 : s % 8 = 0
    · have c18 := (cmp_eq0 m8).trans (decide_eq_true h80)
      have es : ft P (i + 8) = ft P s := by rw [show i + 8 = s by omega]
      scan_at (.elect 4) [after_load_10, hf, hr, hc, ho, hl, h98, hm, e97, c17f, c18, r1,
        r0, sw, r1s, r0s, l0, t0, es]
    · have c18 := (cmp_eq0 m8).trans (decide_eq_false h80)
      by_cases h84 : s % 8 < 4
      · have c19 := (cmp_lt4 m8).trans (decide_eq_true h84)
        by_cases h41 : s % 4 ≠ 1
        · have c21 := (cmp_ne1 m4).trans (decide_eq_true h41)
          have e4 : s - s % 4 = i + 8 := by omega
          scan_at (.load 17) [after_load_10, hf, hr, hc, ho, hl, h98, hm, e97, c17f, c18,
            c19, c21, a3, r1, r0, sw, pw, e4]
        · have c21 := (cmp_ne1 m4).trans (decide_eq_false h41)
          have e4 : s - 1 = i + 8 := by omega
          scan_at (.load 16) [after_load_10, hf, hr, hc, ho, hl, h98, hm, e97, c17f, c18,
            c19, c21, a3, r1, r0, sw, pw, e4]
      · have c19 := (cmp_lt4 m8).trans (decide_eq_false h84)
        have e8 : s - s % 8 = i + 8 := by omega
        have c17g := c17f
        rw [e8] at c17g
        scan_at (.load 11) [after_load_10, hf, hr, hc, ho, hl, h98, hm, e97, c17f, c17g,
          c18, c19, a3, r1, r0, sw, pw, e8]

/-! ### The block of four -/

theorem st_load_11 (hpre : Pre P L mem0) (h : RefAt P g (.load 11) ⟨.load 11, w, p, x⟩) :
    LoadOK P g 11 2275 1 w (after_load_11 L g ⟨.load 11, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 8, h.2.2.2.2.2.2.1, by omega, ?_⟩
  scan_at (.load 12) [after_load_11, h]

/-- `block_step pos b k`: a load inside a remainder block whose base index is `b`: it reads
entry `b + k`, and the sum advances from entry `b + m` to `b + m + 1`. -/
syntax "block_step " term:max term:max num " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| block_step $pos $b $m [$ls,*]) => `(tactic| (
      have hs32 : s < 2 ^ 32 := by omega
      have r1 := cu_r32 hpre (i := $b + ($m + 1)) (by omega)
      have r0 := cu_r32 hpre (i := $b + $m) (by omega)
      have sw := step_word hpre (i := $b + $m) (j := $b + ($m + 1)) (by omega) (by omega)
      have e94 := addi4 (a := $b) (by omega)
      have e92 := addi2 (a := $b) (by omega)
      simp only [Nat.add_zero, Nat.reduceAdd] at r1 r0 sw
      scan_at $pos [$ls,*, h, r1, r0, sw, e94, e92]))

theorem st_load_12 (hpre : Pre P L mem0) (h : RefAt P g (.load 12) ⟨.load 12, w, p, x⟩) :
    LoadOK P g 12 2275 0 w (after_load_12 L g ⟨.load 12, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 8, h.2.2.2.2.2.2.1, by omega, ?_⟩
  block_step (.load 13) (s - s % 8) 0 [after_load_12]

theorem st_load_13 (hpre : Pre P L mem0) (h : RefAt P g (.load 13) ⟨.load 13, w, p, x⟩) :
    LoadOK P g 13 2275 2 w (after_load_13 L g ⟨.load 13, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 8, h.2.2.2.2.2.2.1, by omega, ?_⟩
  block_step (.load 14) (s - s % 8) 1 [after_load_13]

theorem st_load_14 (hpre : Pre P L mem0) (h : RefAt P g (.load 14) ⟨.load 14, w, p, x⟩) :
    LoadOK P g 14 2275 3 w (after_load_14 L g ⟨.load 14, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 8, h.2.2.2.2.2.2.1, by omega, ?_⟩
  block_step (.load 15) (s - s % 8) 2 [after_load_14]

theorem st_load_15 (hpre : Pre P L mem0) (h : RefAt P g (.load 15) ⟨.load 15, w, p, x⟩) :
    LoadOK P g 15 2275 4 w (after_load_15 L g ⟨.load 15, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 8, h.2.2.2.2.2.2.1, by omega, ?_⟩
  have hs32 : s < 2 ^ 32 := by omega
  have m4 : s % 4 < 2 ^ 32 := by omega
  have r1 := cu_r32 hpre (i := s - s % 8 + 4) (by omega)
  have r0 := cu_r32 hpre (i := s - s % 8 + 3) (by omega)
  have sw := step_word hpre (i := s - s % 8 + 3) (j := s - s % 8 + 4) (by omega) (by omega)
  have pw := ptr_word hpre (j := s - s % 8 + 4) (by omega)
  have r1s := cu_r32 hpre (i := s + 1) (by omega)
  have r0s := cu_r32 hpre (i := s) (by omega)
  have l0 := len_word hpre (i := s) hsq
  have t0 := tiles_word hpre (i := s) hsq
  by_cases h40 : s % 4 = 0
  · have c20 := (cmp_eq0 m4).trans (decide_eq_true h40)
    have es : ft P (s - s % 8 + 4) = ft P s := by rw [show s - s % 8 + 4 = s by omega]
    scan_at (.elect 4) [after_load_15, h, c20, r1, r0, sw, r1s, r0s, l0, t0, es]
  · have c20 := (cmp_eq0 m4).trans (decide_eq_false h40)
    by_cases h41 : s % 4 ≠ 1
    · have c21 := (cmp_ne1 m4).trans (decide_eq_true h41)
      have e4 : s - s % 4 = s - s % 8 + 4 := by omega
      scan_at (.load 17) [after_load_15, h, c20, c21, r1, r0, sw, pw, e4]
    · have c21 := (cmp_ne1 m4).trans (decide_eq_false h41)
      have e4 : s - 1 = s - s % 8 + 4 := by omega
      scan_at (.load 16) [after_load_15, h, c20, c21, r1, r0, sw, pw, e4]

/-! ### The block of two and the last sequence -/

theorem st_load_16 (hpre : Pre P L mem0) (h : RefAt P g (.load 16) ⟨.load 16, w, p, x⟩) :
    LoadOK P g 16 2286 0 w (after_load_16 L g ⟨.load 16, w, p, x⟩) := by
  scan_pre
  refine ⟨s - 1, h.2.2.2.2.2.1, by omega, ?_⟩
  have pw := ptr_word hpre (j := s - 1) (by omega)
  scan_at (.load 20) [after_load_16, h, pw]

theorem st_load_17 (hpre : Pre P L mem0) (h : RefAt P g (.load 17) ⟨.load 17, w, p, x⟩) :
    LoadOK P g 17 2282 1 w (after_load_17 L g ⟨.load 17, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 4, h.2.2.2.2.2.1, by omega, ?_⟩
  scan_at (.load 18) [after_load_17, h]

theorem st_load_18 (hpre : Pre P L mem0) (h : RefAt P g (.load 18) ⟨.load 18, w, p, x⟩) :
    LoadOK P g 18 2282 0 w (after_load_18 L g ⟨.load 18, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 4, h.2.2.2.2.2.1, by omega, ?_⟩
  block_step (.load 19) (s - s % 4) 0 [after_load_18]

theorem st_load_19 (hpre : Pre P L mem0) (h : RefAt P g (.load 19) ⟨.load 19, w, p, x⟩) :
    LoadOK P g 19 2282 2 w (after_load_19 L g ⟨.load 19, w, p, x⟩) := by
  scan_pre
  refine ⟨s - s % 4, h.2.2.2.2.2.1, by omega, ?_⟩
  have hs32 : s < 2 ^ 32 := by omega
  have m2 : s % 2 < 2 ^ 32 := by omega
  have r1 := cu_r32 hpre (i := s - s % 4 + 2) (by omega)
  have r0 := cu_r32 hpre (i := s - s % 4 + 1) (by omega)
  have sw := step_word hpre (i := s - s % 4 + 1) (j := s - s % 4 + 2) (by omega) (by omega)
  have pw := ptr_word hpre (j := s - s % 4 + 2) (by omega)
  have r1s := cu_r32 hpre (i := s + 1) (by omega)
  have r0s := cu_r32 hpre (i := s) (by omega)
  have l0 := len_word hpre (i := s) hsq
  have t0 := tiles_word hpre (i := s) hsq
  have a1 := and1 hs32
  by_cases hodd : s % 2 ≠ 0
  · have c22 := (cmp_ne0 m2).trans (decide_eq_true hodd)
    have e1 : s - 1 = s - s % 4 + 2 := by omega
    scan_at (.load 20) [after_load_19, h, a1, c22, r1, r0, sw, pw, e1]
  · have c22 := (cmp_ne0 m2).trans (decide_eq_false hodd)
    have es : ft P (s - s % 4 + 2) = ft P s := by rw [show s - s % 4 + 2 = s by omega]
    scan_at (.elect 4) [after_load_19, h, a1, c22, r1, r0, sw, r1s, r0s, l0, t0, es]

theorem st_load_20 (hpre : Pre P L mem0) (h : RefAt P g (.load 20) ⟨.load 20, w, p, x⟩) :
    LoadOK P g 20 2288 1 w (after_load_20 L g ⟨.load 20, w, p, x⟩) := by
  scan_pre
  refine ⟨s - 1, h.2.2.2.2.2.1, by omega, ?_⟩
  have e : s - 1 + 1 = s := by omega
  have r1 := cu_r32 hpre (i := s) (by omega)
  have r0 := cu_r32 hpre (i := s - 1) (by omega)
  have sw := step_word hpre (i := s - 1) (j := s) (by omega) (by omega)
  have r1s := cu_r32 hpre (i := s + 1) (by omega)
  have l0 := len_word hpre (i := s) hsq
  have t0 := tiles_word hpre (i := s) hsq
  scan_at (.elect 4) [after_load_20, h, e, r1, r0, sw, r1s, l0, t0]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
