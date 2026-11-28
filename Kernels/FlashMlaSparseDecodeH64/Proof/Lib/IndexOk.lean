-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWord

@[expose] public section

/-! # The index warp's validity test is the slot's validity

The test `ixOk` of an index word at a position below the length (`ixOk_true` gives only the forward
direction) holds exactly for a valid slot (`ixOk_main_iff`, `ixOk_extra_iff`): the word is the
int32 of the slot's index (`ixWdM`, `ixWdX`), which for a valid slot is a nonnegative number below
the cache's tokens, so not the `-1` word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The validity test of numbers: not the word `-1`, below the length. -/
theorem ixOk_iff {a p len : Nat} (ha : a < 2 ^ 32) (hp : p < 2 ^ 31) (hl : len < 2 ^ 31) :
    ixOk (W a) (W p) (W len) = true ↔ a ≠ 2 ^ 32 - 1 ∧ p < len := by
  constructor
  · exact ixOk_true ha hp hl
  · rintro ⟨h1, h2⟩
    simp only [ixOk, Bool.and_eq_true]
    refine ⟨?_, by rw [scmp_lt_W hp hl]; simpa using h2⟩
    have : i32 (-1) = W (2 ^ 32 - 1) := by decide
    simp only [scmpi, PTX.compare, r32_W ha, this,
      toNat_W (show a < 2 ^ 64 by omega), toNat_W (show 2 ^ 32 - 1 < 2 ^ 64 by omega),
      decide_eq_true_eq]
    exact_mod_cast h1

/-- **The test of a main position is the slot's validity.** -/
theorem ixOk_main_iff (hp : Pre P L m) {pos : Nat} {x p len : BitVec 64}
    (hx : x = ixWdM P L g pos) (hpos : p = W pos) (hlen : len = W (P.topkLen (ctaidY L g)))
    (hlt : pos < 2 ^ 31) :
    ixOk x p len = true ↔ slotValid P (ctaidY L g) (ctaidX L g) false pos := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  obtain ⟨-, -, -, hle, -⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hle
  have hl31 : P.topkLen (ctaidY L g) < 2 ^ 31 := by have := hp.topkAdd63Lt; omega
  subst hx hpos hlen
  rw [show ixWdM P L g pos = W (i32Bits (P.idx (ctaidY L g) (ctaidX L g) pos)) from rfl,
    ixOk_iff (i32Bits_lt _) hlt hl31]
  constructor
  · rintro ⟨hne, hpl⟩
    refine ⟨hpl, fun h => hne ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [h]
    decide
  · intro hv
    refine ⟨?_, hv.1⟩
    obtain ⟨h0, hlt'⟩ := hp.idxRange _ he _ hq _ hv
    have hr := hp.rowsRange
    have hfit := hp.pageFits
    have hn : P.numBlocks * P.page ≤ P.numBlocks * (P.blockStride / 528) :=
      Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 hfit)
    rw [i32Bits_of_nonneg h0 (by omega)]
    omega

/-- **The test of an extra position is the slot's validity** . -/
theorem ixOk_extra_iff (hp : Pre P L m) {pos : Nat} {x p len : BitVec 64}
    (hx : x = ixWdX P L g pos) (hpos : p = W pos) (hlen : len = W (P.extraTopkLen (ctaidY L g)))
    (hlt : pos < 2 ^ 31) :
    ixOk x p len = true ↔ slotValid P (ctaidY L g) (ctaidX L g) true pos := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  obtain ⟨-, -, hr, -, hle⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hle hr
  have hl31 : P.extraTopkLen (ctaidY L g) < 2 ^ 31 := by
    have := hp.paddedRange (ctaidY L g) he
    simp only [FlashMlaSparseDecodeH64.origPadded, FlashMlaSparseDecodeH64.ceilToMultiple,
      FlashMlaSparseDecodeH64.topkBlock] at this
    omega
  subst hx hpos hlen
  rw [show ixWdX P L g pos = W (i32Bits (P.extraIdx (ctaidY L g) (ctaidX L g) pos)) from rfl,
    ixOk_iff (i32Bits_lt _) hlt hl31]
  constructor
  · rintro ⟨hne, hpl⟩
    refine ⟨hpl, fun h => hne ?_⟩
    simp only [↓reduceIte] at h
    rw [h]
    decide
  · intro hv
    have hon : 0 < P.extra_topk := by
      have := hv.1
      simp only [↓reduceIte] at this
      omega
    refine ⟨?_, hv.1⟩
    obtain ⟨h0, hlt'⟩ := hp.extraIdxRange _ he _ hq _ hv
    have hr := hp.extraRowsRange
    obtain ⟨hpg, -, -, hfit⟩ := hp.extraPos hon
    have hn : P.extraNumBlocks * P.extraPage ≤ P.extraNumBlocks * (P.extraBlockStride / 528) :=
      Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 hfit)
    rw [i32Bits_of_nonneg h0 (by omega)]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
