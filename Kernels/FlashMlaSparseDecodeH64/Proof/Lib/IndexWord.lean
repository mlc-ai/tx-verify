-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.StoredFull
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexAddr
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.Arith32Norm
public import Lemmas.Flow.DivStep

@[expose] public section

/-! # The index words and the coordinate words as numbers

`ixWdM P L g pos`, `ixWdX P L g pos`: the word the lane's pair load returns for position `pos`
of the main (extra) index row, the int32 of `P.idx e q pos` (`P.extraIdx e q pos`) with `e`, `q`
the CTA's batch row and query. The coordinate word the code stores for such a word
(`ixCoord`, `Lib/IndexVal.lean`) is the row `coordRow` of a valid word (`ixCoord_true`) or `-1`;
the validity test `ixOk` holds only for a word that is not `-1` at a position below the length
(`ixOk_true`). -/

/-! # The arithmetic of a coordinate word

The index warp turns an index word `w` (an int32, `i32Bits`) into the coordinate word
`(w / page) * s + (w - (w / page) * page)` (`div.u32`, `mul.lo.s32`, `sub.s32`, `mad.lo.s32` at
pcs 2432-2437, 2449-2463 and 2520-2552), with `s = blockStride / 528` the block's token rows, and
stores `-1` instead unless the index is not `-1` and its position is below the row's length.

This file is the pure arithmetic of that step, for either cache: for a selected slot
(`slotValid`) the index is a nonnegative int32 below the cache's tokens (`Pre.idxRange`), so the
code's word is `tokenRow` (`coordRow_eq`), which is below the cache's rows
(`coordRow_lt`) and so below `2 ^ 31`: the word is the row as a signed int32
(`coordInt_eq`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- The coordinate row the code computes from the index word `w`, the page size `pg` and the
block's token rows `s`: `w / pg * s + (w - w / pg * pg)`. -/
def coordRow (w pg s : Nat) : Nat := w / pg * s + (w - w / pg * pg)

/-- The index word of a nonnegative index below `2 ^ 32` is its natural number. -/
theorem i32Bits_of_nonneg {z : Int} (h0 : 0 ≤ z) (h1 : z.toNat < 2 ^ 32) :
    i32Bits z = z.toNat := by
  unfold i32Bits
  have : z % 2 ^ 32 = z := Int.emod_eq_of_lt h0 (by omega)
  rw [this]

/-- **The code's word is the token row**: for a nonnegative index below `2 ^ 32`. -/
theorem coordRow_eq {idx : Int} {pg bs : Nat} (h0 : 0 ≤ idx) (h1 : idx.toNat < 2 ^ 32)
    (_hpg : 0 < pg) : coordRow (i32Bits idx) pg (bs / 528) = tokenRow pg bs idx := by
  rw [i32Bits_of_nonneg h0 h1]
  unfold coordRow tokenRow
  have : idx.toNat - idx.toNat / pg * pg = idx.toNat % pg := by
    have := Nat.div_add_mod idx.toNat pg
    have h2 : pg * (idx.toNat / pg) = idx.toNat / pg * pg := Nat.mul_comm _ _
    omega
  rw [this]

/-- A token row of an index below the cache's tokens is below the cache's rows. -/
theorem tokenRow_lt {idx : Int} {pg bs n : Nat} (hpg : 0 < pg)
    (hlt : idx.toNat < n * pg) (hfit : pg * 528 ≤ bs) : tokenRow pg bs idx < n * (bs / 528) := by
  unfold tokenRow
  have hq : idx.toNat / pg < n := (Nat.div_lt_iff_lt_mul hpg).2 hlt
  have hm : idx.toNat % pg < pg := Nat.mod_lt _ hpg
  have hs : pg ≤ bs / 528 := (Nat.le_div_iff_mul_le (by norm_num)).2 hfit
  have h1 : (idx.toNat / pg + 1) * (bs / 528) ≤ n * (bs / 528) :=
    Nat.mul_le_mul_right _ hq
  have h2 : (idx.toNat / pg + 1) * (bs / 528) = idx.toNat / pg * (bs / 528) + bs / 528 := by ring
  omega

/-- **A selected slot of the main cache**: the code's coordinate row is the slot's token row,
below the cache's rows. -/
theorem coordRow_main {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) {e q j : Nat}
    (he : e < P.b) (hq : q < P.s_q) (hv : slotValid P e q false j) :
    coordRow (i32Bits (P.idx e q j)) P.page (P.blockStride / 528) =
        tokenRow P.page P.blockStride (P.idx e q j) ∧
      tokenRow P.page P.blockStride (P.idx e q j) < 2 ^ 31 := by
  obtain ⟨h0, hlt⟩ := hp.idxRange e he q hq j hv
  have hr := hp.rowsRange
  have hfit := hp.pageFits
  have hpg := hp.pagePos
  have hn : P.numBlocks * P.page ≤ P.numBlocks * (P.blockStride / 528) :=
    Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 hfit)
  have h32 : (P.idx e q j).toNat < 2 ^ 32 := by omega
  exact ⟨coordRow_eq h0 h32 hpg, by
    have := tokenRow_lt (bs := P.blockStride) hpg hlt hfit
    omega⟩

/-- **A selected slot of the extra cache**: the same for the extra cache, which is on
(`extra_topk > 0`). -/
theorem coordRow_extra {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) {e q j : Nat}
    (hpos : 0 < P.extra_topk) (he : e < P.b) (hq : q < P.s_q) (hv : slotValid P e q true j) :
    coordRow (i32Bits (P.extraIdx e q j)) P.extraPage (P.extraBlockStride / 528) =
        tokenRow P.extraPage P.extraBlockStride (P.extraIdx e q j) ∧
      tokenRow P.extraPage P.extraBlockStride (P.extraIdx e q j) < 2 ^ 31 := by
  obtain ⟨h0, hlt⟩ := hp.extraIdxRange e he q hq j hv
  have hr := hp.extraRowsRange
  obtain ⟨hpg, -, -, hfit⟩ := hp.extraPos hpos
  have hn : P.extraNumBlocks * P.extraPage ≤ P.extraNumBlocks * (P.extraBlockStride / 528) :=
    Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 hfit)
  have h32 : (P.extraIdx e q j).toNat < 2 ^ 32 := by omega
  exact ⟨coordRow_eq h0 h32 hpg, by
    have := tokenRow_lt (bs := P.extraBlockStride) hpg hlt hfit
    omega⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The word a main pair load returns for position `pos` of the lane's row. -/
def ixWdM (P : Params) (L : Launch) (g pos : Nat) : BitVec 64 :=
  W (i32Bits (P.idx (ctaidY L g) (ctaidX L g) pos))

/-- The word an extra pair load returns for position `pos` of the lane's row. -/
def ixWdX (P : Params) (L : Launch) (g pos : Nat) : BitVec 64 :=
  W (i32Bits (P.extraIdx (ctaidY L g) (ctaidX L g) pos))

/-- `div.u32` of two words below `2 ^ 32` by a nonzero one. -/
theorem divu32_W {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (h0 : 0 < y) :
    divu32 (W x) (W y) = W (x / y) := by
  have hq : x / y ≤ x := Nat.div_le_self _ _
  have h1 : intOf .u 32 (r32 (W x)) = x := by
    simp only [intOf, r32_W hx, W, BitVec.toNat_ofNat]
    simp only [reduceCtorEq, ↓reduceIte]
    omega
  have h2 : intOf .u 32 (r32 (W y)) = y := by
    simp only [intOf, r32_W hy, W, BitVec.toNat_ofNat]
    simp only [reduceCtorEq, ↓reduceIte]
    omega
  have h3 : (x : Int).tdiv y = ((x / y : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; norm_cast
  show intBits 32 ((intOf .u 32 (r32 (W x))).tdiv (intOf .u 32 (r32 (W y)))) = _
  rw [h1, h2, h3]
  simp only [intBits, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, W, BitVec.toNat_ofNat]
  generalize x / y = q at hq ⊢
  omega

/-- The code's division by 528 (a multiplication by the magic constant) on a word below
`2 ^ 31`. -/
theorem div528_W {x : Nat} (hx : x < 2 ^ 31) : ixDiv528 (W x) = W (x / 528) := by
  have h1 : mulhi (W x) 1041204193 = W (x * 1041204193 / 2 ^ 32) := by
    have hl : x * 1041204193 / 2 ^ 32 < 2 ^ 32 := by omega
    simp only [mulhi, r32_W (show x < 2 ^ 32 by omega), toSigned_W hx]
    have h2 : toSigned 32 (i32 1041204193) = 1041204193 := by
      rw [show i32 1041204193 = W 1041204193 by decide]
      exact toSigned_W (by norm_num)
    simp only [h2, beq_self_eq_true, ↓reduceIte]
    have : ((x : Int) * 1041204193 / 2 ^ 32) = ((x * 1041204193 / 2 ^ 32 : Nat) : Int) := by
      omega
    rw [this, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, W, BitVec.toNat_ofNat]
    generalize x * 1041204193 / 2 ^ 32 = q at hl ⊢
    omega
  have h2 : x * 1041204193 / 2 ^ 32 < 2 ^ 31 := by omega
  simp only [ixDiv528, h1]
  rw [shrs_int h2 (by decide) (by decide), shru_int (by omega) (by decide) (by decide)]
  have h3 : x * 1041204193 / 2 ^ 32 / 2 ^ (31 : Int).toNat = 0 := by
    simp only [Int.reduceToNat]; omega
  have h4 : x * 1041204193 / 2 ^ 32 / 2 ^ (7 : Int).toNat = x / 528 := by
    simp only [Int.reduceToNat]; omega
  rw [h3, h4]
  simpa using add32_W (a := x / 528) (b := 0) (by omega)

/-- **The code's coordinate word of a valid index**: the row `coordRow`. -/
theorem ixCoord_true {x pg s : Nat} (hx : x < 2 ^ 32) (hpg : 0 < pg) (hpg32 : pg < 2 ^ 32)
    (hs : s < 2 ^ 32) (hr : coordRow x pg s < 2 ^ 31) :
    ixCoord (W x) (W pg) (W s) true = W (coordRow x pg s) := by
  have hq : x / pg * pg ≤ x := Nat.div_mul_le_self x pg
  have hq32 : x / pg < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hqs : x / pg * s + (x - x / pg * pg) < 2 ^ 32 := by
    unfold coordRow at hr; omega
  simp only [ixCoord, sel, ↓reduceIte, divu32_W hx hpg32 hpg, mul32_W hq32 hpg32 (by omega),
    sub32_W hq hx, mad32_W hq32 hs hqs]
  rfl

/-- **The code's coordinate word of an invalid slot**: `-1`. -/
theorem ixCoord_false (x pg s : BitVec 64) : ixCoord x pg s false = i32 (-1) := by
  simp only [ixCoord, sel, Bool.false_eq_true, ↓reduceIte]

/-- The validity test holds only for a word that is not `-1`, below the length. -/
theorem ixOk_true {a p len : Nat} (ha : a < 2 ^ 32) (hp : p < 2 ^ 31) (hl : len < 2 ^ 31)
    (h : ixOk (W a) (W p) (W len) = true) : a ≠ 2 ^ 32 - 1 ∧ p < len := by
  simp only [ixOk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [scmp_lt_W hp hl] at h2
  refine ⟨?_, by simpa using h2⟩
  have : i32 (-1) = W (2 ^ 32 - 1) := by decide
  simp only [scmpi, PTX.compare, r32_W ha, this,
    toNat_W (show a < 2 ^ 64 by omega), toNat_W (show 2 ^ 32 - 1 < 2 ^ 64 by omega),
    decide_eq_true_eq] at h1
  exact_mod_cast h1

/-- A word below `2 ^ 31` is its number as the signed coordinate a gather records. -/
theorem wordInt_W {r : Nat} (h : r < 2 ^ 31) : wordInt (.bits 32 (W r)) = (r : Int) := by
  simp only [wordInt, truncBits, W, BitVec.toNat_ofNat]
  have e : r % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 = r := by omega
  rw [e, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

/-- The word `-1` is the coordinate `-1`. -/
theorem wordInt_neg : wordInt (.bits 32 (i32 (-1))) = -1 := by decide

/-- The int32 of an index is below `2 ^ 32`. -/
theorem i32Bits_lt (z : Int) : i32Bits z < 2 ^ 32 := by
  unfold i32Bits; omega

/-- **The code's coordinate word of a selected main slot** is its token row, below `2 ^ 31`. -/
theorem ixCoord_main (hp : Pre P L m) {e q j : Nat} (he : e < P.b) (hq : q < P.s_q)
    (hv : slotValid P e q false j) :
    ixCoord (W (i32Bits (P.idx e q j))) (pw P.page) (ixDiv528 (pw P.blockStride)) true =
        W (tokenRow P.page P.blockStride (P.idx e q j)) ∧
      tokenRow P.page P.blockStride (P.idx e q j) < 2 ^ 31 := by
  obtain ⟨hcr, hlt⟩ := coordRow_main hp he hq hv
  have h1 := hp.pageFits
  have h2 := hp.blockStrideRange
  have h3 := hp.pagePos
  refine ⟨?_, hlt⟩
  rw [ixA_pw (by omega : P.page < 2 ^ 32), ixA_pw (by omega : P.blockStride < 2 ^ 32),
    div528_W h2, ← hcr]
  exact ixCoord_true (i32Bits_lt _) h3 (by omega) (by omega) (by rw [hcr]; exact hlt)

/-- **The same for a selected extra slot** (the extra cache is on). -/
theorem ixCoord_extra (hp : Pre P L m) {e q j : Nat} (hpos : 0 < P.extra_topk) (he : e < P.b)
    (hq : q < P.s_q) (hv : slotValid P e q true j) :
    ixCoord (W (i32Bits (P.extraIdx e q j))) (pw P.extraPage) (ixDiv528 (pw P.extraBlockStride))
        true = W (tokenRow P.extraPage P.extraBlockStride (P.extraIdx e q j)) ∧
      tokenRow P.extraPage P.extraBlockStride (P.extraIdx e q j) < 2 ^ 31 := by
  obtain ⟨hcr, hlt⟩ := coordRow_extra hp hpos he hq hv
  obtain ⟨h3, -, -, h1⟩ := hp.extraPos hpos
  have h2 := hp.extraBlockStrideRange
  refine ⟨?_, hlt⟩
  rw [ixA_pw (by omega : P.extraPage < 2 ^ 32), ixA_pw (by omega : P.extraBlockStride < 2 ^ 32),
    div528_W h2, ← hcr]
  exact ixCoord_true (i32Bits_lt _) h3 (by omega) (by omega) (by rw [hcr]; exact hlt)

/-- A negative immediate subtracts within a small word. -/
theorem addi_negW {a k : Nat} (hk : k ≤ a) (ha : a < 2 ^ 31) :
    addi (W a) (-(k : Int)) = W (a - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

/-- The validity test holds for a word that is not `-1`, below the length. -/
theorem ixOk_of {a p len : Nat} (ha : a < 2 ^ 32) (hp : p < 2 ^ 31) (hl : len < 2 ^ 31)
    (hne : a ≠ 2 ^ 32 - 1) (hlt : p < len) : ixOk (W a) (W p) (W len) = true := by
  simp only [ixOk, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have : i32 (-1) = W (2 ^ 32 - 1) := by decide
    simp only [scmpi, PTX.compare, r32_W ha, this,
      toNat_W (show a < 2 ^ 64 by omega), toNat_W (show 2 ^ 32 - 1 < 2 ^ 64 by omega),
      decide_eq_true_eq]
    exact_mod_cast hne
  · rw [scmp_lt_W hp hl]
    simpa using hlt

/-- The word of a selected main slot is not the pattern of `-1`. -/
theorem valid_ne_main (hp : Pre P L m) {e q j : Nat} (he : e < P.b) (hq : q < P.s_q)
    (hv : slotValid P e q false j) : i32Bits (P.idx e q j) ≠ 2 ^ 32 - 1 := by
  obtain ⟨h0, hlt⟩ := hp.idxRange e he q hq j hv
  have hr := hp.rowsRange
  have hfit := hp.pageFits
  have hn : P.numBlocks * P.page ≤ P.numBlocks * (P.blockStride / 528) :=
    Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 hfit)
  have h32 : (P.idx e q j).toNat < 2 ^ 32 := by omega
  rw [i32Bits_of_nonneg h0 h32]
  omega

/-- The word of a selected extra slot is not the pattern of `-1`. -/
theorem valid_ne_extra (hp : Pre P L m) {e q j : Nat} (hpos : 0 < P.extra_topk) (he : e < P.b)
    (hq : q < P.s_q) (hv : slotValid P e q true j) : i32Bits (P.extraIdx e q j) ≠ 2 ^ 32 - 1 := by
  obtain ⟨h0, hlt⟩ := hp.extraIdxRange e he q hq j hv
  have hr := hp.extraRowsRange
  obtain ⟨-, -, -, hfit⟩ := hp.extraPos hpos
  have hn : P.extraNumBlocks * P.extraPage ≤ P.extraNumBlocks * (P.extraBlockStride / 528) :=
    Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 hfit)
  have h32 : (P.extraIdx e q j).toNat < 2 ^ 32 := by omega
  rw [i32Bits_of_nonneg h0 h32]
  omega

/-- **A coordinate word the code stores for a main position** is `-1` or its slot's row, and a
selected slot's word is its row. -/
theorem stored_main (hp : Pre P L m) {g pos : Nat} {x p len : BitVec 64}
    (hx : x = ixWdM P L g pos) (hpos : p = W pos) (hlen : len = W (P.topkLen (ctaidY L g)))
    (hlt : pos < 2 ^ 31) :
    StoredWordFull P (ctaidY L g) (ctaidX L g) false pos
      (ixCoord x (pw P.page) (ixDiv528 (pw P.blockStride)) (ixOk x p len)) := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  obtain ⟨-, -, -, hle, -⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hle
  have hl31 : P.topkLen (ctaidY L g) < 2 ^ 31 := by have := hp.topkAdd63Lt; omega
  subst hx hpos hlen
  by_cases hok : ixOk (ixWdM P L g pos) (W pos) (W (P.topkLen (ctaidY L g))) = true
  · obtain ⟨hne, hpl⟩ := ixOk_true (i32Bits_lt _) hlt hl31 hok
    have hv : slotValid P (ctaidY L g) (ctaidX L g) false pos := by
      refine ⟨hpl, fun h => hne ?_⟩
      have h' := h
      simp only [Bool.false_eq_true, ↓reduceIte] at h'
      rw [h']
      decide
    obtain ⟨h1, h2⟩ := ixCoord_main hp he hq hv
    have hw : wordInt (.bits 32 (ixCoord (ixWdM P L g pos) (pw P.page)
        (ixDiv528 (pw P.blockStride)) (ixOk (ixWdM P L g pos) (W pos)
          (W (P.topkLen (ctaidY L g)))))) =
          (slotRow P (ctaidY L g) (ctaidX L g) false pos : Int) := by
      rw [hok]
      simp only [ixWdM]
      rw [h1, wordInt_W h2]
      rfl
    exact ⟨.inr ⟨hv, hw⟩, fun _ => hw⟩
  · rw [Bool.not_eq_true] at hok
    refine ⟨.inl (by rw [hok, ixCoord_false]; exact wordInt_neg), fun hv => ?_⟩
    exact absurd (ixOk_of (i32Bits_lt _) hlt hl31 (valid_ne_main hp he hq hv) hv.1)
      (by rw [← ixWdM]; simp [hok])

/-- **The same for an extra position.** -/
theorem stored_extra (hp : Pre P L m) {g pos : Nat} {x p len : BitVec 64}
    (hx : x = ixWdX P L g pos) (hpos : p = W pos) (hlen : len = W (P.extraTopkLen (ctaidY L g)))
    (hlt : pos < 2 ^ 31) :
    StoredWordFull P (ctaidY L g) (ctaidX L g) true pos
      (ixCoord x (pw P.extraPage) (ixDiv528 (pw P.extraBlockStride)) (ixOk x p len)) := by
  obtain ⟨hq, he⟩ := ctaid_lt hp g
  obtain ⟨-, -, hr, -, hle⟩ := len_words hp (g / L.block)
  rw [rowOf_cta] at hle hr
  have hl31 : P.extraTopkLen (ctaidY L g) < 2 ^ 31 := by
    have := hp.paddedRange (ctaidY L g) he
    simp only [FlashMlaSparseDecodeH64.origPadded, FlashMlaSparseDecodeH64.ceilToMultiple,
      FlashMlaSparseDecodeH64.topkBlock] at this
    omega
  subst hx hpos hlen
  by_cases hok : ixOk (ixWdX P L g pos) (W pos) (W (P.extraTopkLen (ctaidY L g))) = true
  · obtain ⟨hne, hpl⟩ := ixOk_true (i32Bits_lt _) hlt hl31 hok
    have hv : slotValid P (ctaidY L g) (ctaidX L g) true pos := by
      refine ⟨hpl, fun h => hne ?_⟩
      have h' := h
      simp only [↓reduceIte] at h'
      rw [h']
      decide
    obtain ⟨h1, h2⟩ := ixCoord_extra hp (by omega) he hq hv
    have hw : wordInt (.bits 32 (ixCoord (ixWdX P L g pos) (pw P.extraPage)
        (ixDiv528 (pw P.extraBlockStride)) (ixOk (ixWdX P L g pos) (W pos)
          (W (P.extraTopkLen (ctaidY L g)))))) =
          (slotRow P (ctaidY L g) (ctaidX L g) true pos : Int) := by
      rw [hok]
      simp only [ixWdX]
      rw [h1, wordInt_W h2]
      rfl
    exact ⟨.inr ⟨hv, hw⟩, fun _ => hw⟩
  · rw [Bool.not_eq_true] at hok
    refine ⟨.inl (by rw [hok, ixCoord_false]; exact wordInt_neg), fun hv => ?_⟩
    have hv1 : pos < P.extraTopkLen (ctaidY L g) := by simpa using hv.1
    exact absurd (ixOk_of (i32Bits_lt _) hlt hl31 (valid_ne_extra hp (by omega) he hq hv) hv1)
      (by rw [← ixWdX]; simp [hok])

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
