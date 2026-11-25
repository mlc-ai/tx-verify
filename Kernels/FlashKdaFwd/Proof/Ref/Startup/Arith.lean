-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Inv

@[expose] public section

/-! # The arithmetic of the scan of the offsets array

The scan (instructions 113 to 311) computes, in signed 32-bit arithmetic on the low words of
the loaded 64-bit entries, the number of tiles of each sequence before the thread's own and
adds them up. This file has the closed forms the invariant needs, each proved once:

* `tile_word`: the five instructions `sub.s32`, `add.s32 15`, `shr.s32 31`, `shr.u32 28`,
  `add.s32`, `shr.s32 4` (a signed division by 16 that rounds towards zero) on two entries
  `a ≤ b` give `tiles (b - a) = (b - a + 15) / 16`;
* `cu_succ`, `ft_succ`, `cu_mono`, `cu_le`, `ft_le`: entry `i + 1` is entry `i` plus the
  length of sequence `i`, the tile counts add up, and under `Pre` every entry is at most
  `P.total` and every partial tile count at most `P.totalTiles` (both below `2 ^ 31`);
* `step_word`: one step of the sum, as the code computes it;
* `ptr_word`: the pointer `cu_seqlens + 8 * j` (`mul.wide.u32` and `add.s64`);
* `and7`, `and3`, `and1`, `and8`: the masks of the sequence index (`%r5 = seq & 7`,
  `%r7 = seq & 3`, `seq & 1`, `%r6 = seq & 0x7ffffff8`).

The bounds come from `Pre`: `tokensRange` (`P.total + 15 < 2 ^ 31`), `slotsRange` with
`headsPos` (`P.totalTiles < 2 ^ 31`), `tilesFit`, `offsetsRange`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **The tile count of a sequence from its two entries**, as the code computes it. -/
theorem tile_word {a b : Nat} (hab : a ≤ b) (hb : b + 15 < 2 ^ 31) :
    shrs (add32 (addi (sub32 (W b) (W a)) 15)
      (shru (shrs (addi (sub32 (W b) (W a)) 15) 31) 28)) 4 = W (tiles (b - a)) := by
  have h1 : (b - a + 15) / 2147483648 = 0 := Nat.div_eq_of_lt (by omega)
  w32_norm [h1]
  rfl

theorem cu_succ (P : Params) (i : Nat) : cu P (i + 1) = cu P i + P.length i := by
  simp [cu, firstToken, Finset.sum_range_succ]

theorem ft_succ (P : Params) (i : Nat) : ft P (i + 1) = ft P i + tiles (P.length i) := by
  simp [ft, firstTile, Finset.sum_range_succ]

theorem cu_mono (P : Params) {i j : Nat} (h : i ≤ j) : cu P i ≤ cu P j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem ft_mono (P : Params) {i j : Nat} (h : i ≤ j) : ft P i ≤ ft P j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Every entry of the offsets array is at most the number of tokens. -/
theorem cu_le (P : Params) {i : Nat} (h : i ≤ P.sequences) : cu P i ≤ P.total := cu_mono P h

/-- The number of tokens, padded, fits a signed 32-bit number. -/
theorem total_lt (hpre : Pre P L mem0) : P.total + 15 < 2 ^ 31 := hpre.tokensRange

/-- The tile counts fit a signed 32-bit number. -/
theorem ft_lt (hpre : Pre P L mem0) {i : Nat} (h : i ≤ P.sequences) : ft P i < 2 ^ 31 := by
  have h1 := ft_mono P h
  have h2 := hpre.tilesFit
  have h3 := hpre.slotsRange
  have h4 := hpre.headsPos
  have h5 : P.totalTiles ≤ P.heads * P.totalTiles := Nat.le_mul_of_pos_left _ h4
  simp only [ft] at h1 ⊢
  omega

/-- The sequence index of the thread's block and its successor are entries of the array. -/
theorem seq_lt (hpre : Pre P L mem0) (g : Nat) : seqOf P g < P.sequences := seqOf_lt hpre g

/-- **One step of the sum**: with the tile count of the sequences before `i` in `acc`, the
code's sum over the entries `i` and `j = i + 1` is the tile count of the sequences before
`j`. -/
theorem step_word (hpre : Pre P L mem0) {i j : Nat} (hj : j = i + 1) (hi : i < P.sequences) :
    add32 (shrs (add32 (addi (sub32 (W (cu P j)) (W (cu P i))) 15)
      (shru (shrs (addi (sub32 (W (cu P j)) (W (cu P i))) 15) 31) 28)) 4) (W (ft P i)) =
      W (ft P j) := by
  subst hj
  have h1 := cu_le P (show i + 1 ≤ P.sequences by omega)
  have h2 := total_lt hpre
  have h3 := ft_lt hpre (show i + 1 ≤ P.sequences by omega)
  rw [tile_word (cu_mono P (Nat.le_add_right i 1)) (by omega), cu_succ, Nat.add_sub_cancel_left,
    ft_succ] at *
  rw [add32_W (by omega), Nat.add_comm]

/-- The length of the thread's sequence, from its two entries. -/
theorem len_word (hpre : Pre P L mem0) {i : Nat} (hi : i < P.sequences) :
    sub32 (W (cu P (i + 1))) (W (cu P i)) = W (P.length i) := by
  have h1 := cu_le P (show i + 1 ≤ P.sequences by omega)
  have h2 := total_lt hpre
  rw [sub32_W (cu_mono P (Nat.le_add_right i 1)) (by omega), cu_succ, Nat.add_sub_cancel_left]

/-- The number of tiles of the thread's sequence, as the code computes it from the length. -/
theorem tiles_word (hpre : Pre P L mem0) {i : Nat} (hi : i < P.sequences) :
    shrs (add32 (addi (W (P.length i)) 15) (shru (shrs (addi (W (P.length i)) 15) 31) 28)) 4 =
      W (tiles (P.length i)) := by
  have h := tile_word (cu_mono P (Nat.le_add_right i 1)) (by
    have h1 := cu_le P (show i + 1 ≤ P.sequences by omega)
    have h2 := total_lt hpre
    omega)
  rwa [len_word hpre hi, cu_succ, Nat.add_sub_cancel_left] at h

/-- The low word of an entry is the entry (`cvt.u32.u64` of a loaded 64-bit entry). -/
theorem cu_r32 (hpre : Pre P L mem0) {i : Nat} (hi : i ≤ P.sequences) :
    low32 (W (cu P i)) = W (cu P i) := by
  have h1 := cu_le P hi
  have h2 := total_lt hpre
  have h64 : truncBits 64 (W (cu P i)) = W (cu P i) := by
    apply BitVec.eq_of_toNat_eq
    simp [truncBits, W]
  show truncBits 32 (truncBits 64 (W (cu P i))) = _
  rw [h64]
  exact r32_W (by omega)

/-- **The address of entry `j`**: `mul.wide.u32 %rd, j, 8` and `add.s64` to the pointer. -/
theorem ptr_word (hpre : Pre P L mem0) {j : Nat} (hj : j ≤ P.sequences) :
    add64 (W P.offsetsBase) (mulWide .u (W j) 8) = W (P.offsetsBase + 8 * j) := by
  have h1 := hpre.sequencesLt
  rw [mulWide_u_W (by omega) (by decide) (by decide), add64_W]
  congr 1
  simp only [Int.reduceToNat]
  omega

/-- The scalar parameter 13 (the number of heads), as `ld.param.b32` reads it. -/
theorem headsWord (hpre : Pre P L mem0) : r32 (paramBits L 13) = W P.heads := by
  rw [paramBits, paramName_13, hpre.paramHeads]
  exact r32_W (by have := hpre.headsLt; omega)

/-- The plane `H * seq + head` of the state arrays (`mad.lo.s32` at instruction 328). -/
theorem plane_word (hpre : Pre P L mem0) (hg : g < L.threads) :
    mad32 (W P.heads) (W (seqOf P g)) (W (headOf P g)) =
      W (P.heads * seqOf P g + headOf P g) := by
  have h1 := plane_lt hpre hg
  have h2 := hpre.planesRange
  have h3 := hpre.headsLt
  have h4 := hpre.sequencesLt
  have h5 := seqOf_lt hpre g
  exact mad32_W (by omega) (by omega) (by omega)

theorem ft_zero (P : Params) : ft P 0 = 0 := by simp [ft, firstTile]

theorem and7 {s : Nat} (hs : s < 2 ^ 32) : andi (W s) 7 = W (s % 8) :=
  andi_W_low (k := 3) hs (by norm_num)

theorem and3 {s : Nat} (hs : s < 2 ^ 32) : andi (W s) 3 = W (s % 4) :=
  andi_W_low (k := 2) hs (by norm_num)

theorem and1 {s : Nat} (hs : s < 2 ^ 32) : andi (W s) 1 = W (s % 2) :=
  andi_W_low (k := 1) hs (by norm_num)

/-- `and.b32 %r6, %r3, 2147483640`: the sequence index rounded down to a multiple of 8. -/
theorem and8 {s : Nat} (hs : s < 2 ^ 31) : andi (W s) 2147483640 = W (s - s % 8) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : s &&& 2147483640 = s - s % 8 := by
    have h2 : s &&& 2147483647 = s := by
      rw [show 2147483647 = 2 ^ 31 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hs]
    have h3 := and_negpow (a := s) (k := 3) (by omega) (by norm_num)
    have h4 : (2147483647 : Nat) &&& (2 ^ 32 - 2 ^ 3) = 2147483640 := by decide
    rw [← h4, ← Nat.and_assoc, h2, h3]
    norm_num
  have h5 : s - s % 8 < 2 ^ 64 := by omega
  have hi : (i32 2147483640).toNat = 2147483640 := by decide
  simp only [andi, BitVec.toNat_and, r32_W (show s < 2 ^ 32 by omega), hi,
    toNat_W (show s < 2 ^ 64 by omega), toNat_W h5, h1]

/-! ### The branch conditions of the scan, as decided propositions -/

theorem cmp_eq0 {a : Nat} (ha : a < 2 ^ 32) : scmpi .eq .b (W a) 0 = decide (a = 0) := by
  rw [scmpi_eq_b_W ha (by decide) (by decide)]; rfl

theorem cmp_ne0 {a : Nat} (ha : a < 2 ^ 32) : scmpi .ne .b (W a) 0 = decide (a ≠ 0) := by
  rw [scmpi_ne_b_W ha (by decide) (by decide)]; rfl

theorem cmp_ne1 {a : Nat} (ha : a < 2 ^ 32) : scmpi .ne .b (W a) 1 = decide (a ≠ 1) := by
  rw [scmpi_ne_b_W ha (by decide) (by decide)]; rfl

theorem cmp_lt8 {a : Nat} (ha : a < 2 ^ 32) : scmpi .lt .u (W a) 8 = decide (a < 8) := by
  rw [scmpi_lt_u_W ha (by decide) (by decide)]; rfl

theorem cmp_lt4 {a : Nat} (ha : a < 2 ^ 32) : scmpi .lt .u (W a) 4 = decide (a < 4) := by
  rw [scmpi_lt_u_W ha (by decide) (by decide)]; rfl

theorem cmp_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    scmp .ne .b (W a) (W b) = decide (a ≠ b) := scmp_ne_b_W ha hb

/-- `add.s32 %r, %r, 8` (and 4, 2) on a small word: the steps of the scan's index. -/
theorem addi8 {a : Nat} (h : a + 8 < 2 ^ 32) : addi (W a) 8 = W (a + 8) :=
  addi_W (n := 8) (by decide) h

theorem addi4 {a : Nat} (h : a + 4 < 2 ^ 32) : addi (W a) 4 = W (a + 4) :=
  addi_W (n := 4) (by decide) h

theorem addi2 {a : Nat} (h : a + 2 < 2 ^ 32) : addi (W a) 2 = W (a + 2) :=
  addi_W (n := 2) (by decide) h

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
