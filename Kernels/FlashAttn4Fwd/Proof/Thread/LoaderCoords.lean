-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWorkPre
public import Kernels.FlashAttn4Fwd.Proof.Thread.Loader
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Lemmas.Flow.Bits

@[expose] public section

/-! # The loader's item coordinates, as the exact split of its work item

The registers the loader's copies take their batch, head and query block from are the code's
`FastDivmod` sequences on the item register (`batchW`, `headW`, `mblkW`). Under `Pre` they hold
the coordinates `coordsOf` of the item's work item `workOf`, exactly: each of the code's 32-bit
operations on words below `2 ^ 32` is the corresponding operation of `FastDivmod`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Work.Dm
open PTX PTX.Proof

noncomputable section

private theorem W_eq : FastDivmod.W = 2 ^ 32 := rfl

theorem addW_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    addW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (FastDivmod.add32 a b) := by
  simp only [addW, rd_ofNat ha, rd_ofNat hb, nf_add, nf_trunc, FastDivmod.add32, W_eq]
  congr 1
  omega

theorem subW_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    subW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (FastDivmod.sub32 a b) := by
  simp only [subW, rd_ofNat ha, rd_ofNat hb, nf_sub, nf_trunc, FastDivmod.sub32, W_eq]
  congr 1
  omega

theorem mulLoW_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    mulLoW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (FastDivmod.mulLo a b) := by
  simp only [mulLoW, rd_ofNat ha, rd_ofNat hb, nf_mul, nf_trunc, FastDivmod.mulLo, W_eq]
  congr 1
  generalize a * b = x
  omega

theorem mulHiW_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    mulHiW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (FastDivmod.mulHi a b) := by
  have hlt : a * b / 2 ^ 32 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (calc a * b ≤ a * 2 ^ 32 := Nat.mul_le_mul_left _ hb.le
      _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right ha (by positivity))
  have hm : FastDivmod.mulHi a b = a * b / 2 ^ 32 := by
    simp only [FastDivmod.mulHi, W_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hi : ((a : Int) * (b : Int)) / pow32 = ((a * b / 2 ^ 32 : Nat) : Int) := by
    simp only [pow32]
    push_cast
    rfl
  simp only [mulHiW, Bool.false_eq_true, ↓reduceIte, hm, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_lt_of_le ha (by decide : 2 ^ 32 ≤ 2 ^ 64)),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hb (by decide : 2 ^ 32 ≤ 2 ^ 64)), hi, BitVec.ofInt_natCast,
    rd_ofNat ha, rd_ofNat hb, nf_trunc]
  congr 1
  omega

theorem shrW_ofNat {a s : Nat} (ha : a < 2 ^ 32) (hs : s < 2 ^ 16) :
    shrW (BitVec.ofNat 64 a) (cvtW (BitVec.ofNat 64 s)) = BitVec.ofNat 64 (FastDivmod.shr32 a s) :=
  by
  have hc : cvtW (BitVec.ofNat 64 s) = BitVec.ofNat 64 s := by
    simp only [cvtW, nf_trunc]
    congr 1
    omega
  have hs' : (rd (BitVec.ofNat 64 s)).toNat = s := by
    rw [rd_ofNat (by omega), BitVec.toNat_ofNat]; omega
  simp only [shrW, hc, hs', rd_ofNat ha, FastDivmod.shr32, W_eq, Nat.mod_eq_of_lt ha]
  split_ifs with h
  · rw [Nat.div_eq_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) h))]
    rfl
  · rw [nf_shr]
    congr 2
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le ha (by decide : 2 ^ 32 ≤ 2 ^ 64))

theorem mulHi_lt {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    FastDivmod.mulHi a b < 2 ^ 32 := by
  simp only [FastDivmod.mulHi, W_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact Nat.div_lt_of_lt_mul (calc a * b ≤ a * 2 ^ 32 := Nat.mul_le_mul_left _ hb.le
    _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right ha (by positivity))

theorem sub32_lt (a b : Nat) : FastDivmod.sub32 a b < 2 ^ 32 := by
  simp only [FastDivmod.sub32, W_eq]; omega

theorem add32_lt (a b : Nat) : FastDivmod.add32 a b < 2 ^ 32 := by
  simp only [FastDivmod.add32, W_eq]; omega

theorem shr32_lt (a s : Nat) : FastDivmod.shr32 a s < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.div_le_self _ _)
    (by simp only [FastDivmod.W]; exact Nat.mod_lt _ (by positivity))

/-- The code's quotient of a 32-bit dividend is `FastDivmod.quot`. -/
theorem quotW_ofNat {x m s1 s2 : Nat} (hx : x < 2 ^ 32) (hm : m < 2 ^ 32) (h1 : s1 < 2 ^ 16)
    (h2 : s2 < 2 ^ 16) :
    quotW (BitVec.ofNat 64 x) (BitVec.ofNat 64 m) (cvtW (BitVec.ofNat 64 s1))
      (cvtW (BitVec.ofNat 64 s2)) = BitVec.ofNat 64 (FastDivmod.quot m s1 s2 x) := by
  simp only [quotW, mulHiW_ofNat hx hm]
  rw [subW_ofNat hx (mulHi_lt hx hm), shrW_ofNat (sub32_lt _ _) h1,
    addW_ofNat (shr32_lt _ _) (mulHi_lt hx hm), shrW_ofNat (add32_lt _ _) h2]
  rfl

/-- The code's remainder is `FastDivmod.rem`. -/
theorem remW_ofNat {x q d : Nat} (hx : x < 2 ^ 32) (hq : q < 2 ^ 32) (hd : d < 2 ^ 32) :
    remW (BitVec.ofNat 64 x) (BitVec.ofNat 64 q) (BitVec.ofNat 64 d) =
      BitVec.ofNat 64 (FastDivmod.rem d q x) := by
  have hl : FastDivmod.mulLo q d < 2 ^ 32 := by
    simp only [FastDivmod.mulLo, W_eq]; exact Nat.mod_lt _ (by positivity)
  simp only [remW, mulLoW_ofNat hq hd]
  rw [subW_ofNat hx hl]
  rfl

theorem quot_lt (m s1 s2 n : Nat) : FastDivmod.quot m s1 s2 n < 2 ^ 32 := shr32_lt _ _

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The divmod words the code reads fit their registers. -/
theorem divmod_bounds (hpre : Pre P L mem0) :
    divWord L "11" 1 < 2 ^ 32 ∧ divShift L "11" 0 < 2 ^ 16 ∧ divShift L "11" 1 < 2 ^ 16 ∧
      divWord L "11" 0 = P.blocks ∧ divWord L "12" 1 < 2 ^ 32 ∧ divShift L "12" 0 < 2 ^ 16 ∧
      divShift L "12" 1 < 2 ^ 16 ∧ divWord L "12" 0 = P.h := by
  have hb := Schedule.blocks_lt hpre
  have hh := Schedule.heads_lt hpre
  obtain ⟨b0, b1, b2, b3⟩ := Schedule.divmod_words (by omega) hpre.paramBlockDivmod
    hpre.blockDivmod
  obtain ⟨h0, h1, h2, h3⟩ := Schedule.divmod_words (by omega) hpre.paramHeadDivmod
    hpre.headDivmod
  obtain ⟨-, hm, hs1, hs2, -⟩ := hpre.blockDivmod
  obtain ⟨-, hm', hs1', hs2', -⟩ := hpre.headDivmod
  refine ⟨?_, ?_, ?_, b0, ?_, ?_, ?_, h0⟩ <;> omega

theorem qbW_eq (hpre : Pre P L mem0) {g i : Nat} (hw : workOf L g i < 2 ^ 32) :
    qbW L g i = BitVec.ofNat 64 (FastDivmod.quot (divWord L "11" 1) (divShift L "11" 0)
      (divShift L "11" 1) (workOf L g i)) := by
  obtain ⟨hm, hs1, hs2, -⟩ := divmod_bounds hpre
  simp only [qbW, nbS1W, nbS2W]
  rw [workW_eq (g := g) hpre i hw]
  exact quotW_ofNat hw hm hs1 hs2

theorem batchW_eq (hpre : Pre P L mem0) {g i : Nat} (hw : workOf L g i < 2 ^ 32) :
    batchW L g i = BitVec.ofNat 64 (coordsOf L (workOf L g i)).1 := by
  obtain ⟨-, -, -, -, hm, hs1, hs2, -⟩ := divmod_bounds hpre
  simp only [batchW, hS1W, hS2W, coordsOf]
  rw [qbW_eq hpre hw]
  exact quotW_ofNat (quot_lt _ _ _ _) hm hs1 hs2

theorem headW_eq (hpre : Pre P L mem0) {g i : Nat} (hw : workOf L g i < 2 ^ 32) :
    headW L g i = BitVec.ofNat 64 (coordsOf L (workOf L g i)).2.1 := by
  obtain ⟨-, -, -, -, hm, hs1, hs2, hd⟩ := divmod_bounds hpre
  have hh := Schedule.heads_lt hpre
  simp only [headW, coordsOf]
  rw [batchW_eq hpre hw, qbW_eq hpre hw]
  simp only [coordsOf]
  exact remW_ofNat (quot_lt _ _ _ _) (quot_lt _ _ _ _) (by show divWord L "12" 0 < 2 ^ 32; omega)

theorem mblkW_eq (hpre : Pre P L mem0) {g i : Nat} (hw : workOf L g i < 2 ^ 32) :
    mblkW L g i = BitVec.ofNat 64 (coordsOf L (workOf L g i)).2.2 := by
  obtain ⟨-, -, -, hd, -⟩ := divmod_bounds hpre
  have hb := Schedule.blocks_lt hpre
  simp only [mblkW, coordsOf]
  rw [qbW_eq hpre hw, workW_eq (g := g) hpre i hw]
  exact remW_ofNat hw (quot_lt _ _ _ _) (by show divWord L "11" 0 < 2 ^ 32; omega)

/-- The bounds of an existing item's coordinates: its work item and its batch and head fit a
positive 32-bit integer, and its query block's 512 rows lie within `seqlen_q`. -/
theorem item_bounds (hpre : Pre P L mem0) {g i : Nat} (hi : i < T L g) :
    workOf L g i < 2 ^ 31 ∧ (coordsOf L (workOf L g i)).1 < 2 ^ 31 ∧
      (coordsOf L (workOf L g i)).2.1 < 2 ^ 31 ∧
      512 * (coordsOf L (workOf L g i)).2.2 + 512 ≤ P.sq := by
  have hw : workOf L g i < P.items := (lt_T_iff (g := g) hpre).mp hi
  have hsr := hpre.scheduleRange
  have hbl : 0 < P.blocks := by
    have := hpre.sqPos
    unfold Params.blocks; omega
  have hcl := hpre.clustersPos
  have hc := Schedule.coords_eq hpre (show workOf L g i < 2 ^ 32 by omega)
  have hl := Schedule.coords_lt hpre hw
  have hb : P.b ≤ P.items :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hbl hpre.hPos)
  have hh : P.h ≤ P.items := by
    unfold Params.items
    calc P.h ≤ P.blocks * P.h := Nat.le_mul_of_pos_left _ hbl
      _ ≤ P.blocks * P.h * P.b := Nat.le_mul_of_pos_right _ hpre.bPos
  have hs := hpre.sqDiv512
  have hq : P.sq = 512 * P.blocks := by unfold Params.blocks; omega
  rw [hc]
  simp only at hl ⊢
  omega

/-- The query row of the CTA's half of an item, as the code computes it. -/
theorem qRowW_eq (hpre : Pre P L mem0) {g i : Nat} (hw : workOf L g i < 2 ^ 32)
    (hm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31) :
    Loader.qRowW L g i =
      BitVec.ofNat 64 (128 * rank L g + 512 * (coordsOf L (workOf L g i)).2.2) := by
  have hr : rank L g < 2 := Nat.mod_lt _ (by decide)
  rw [Loader.qRowW, mblkW_eq hpre hw]
  generalize (coordsOf L (workOf L g i)).2.2 = m at hm ⊢
  generalize rank L g = r at hr ⊢
  simp only [addW, shlW, rd, nf_trunc, nf_shl, nf_add, nf_toNat, nf_ofInt, nf_mod64_32,
    Nat.reducePow, Nat.reduceMod, Nat.reduceLeDiff, Int.reduceMod, Int.reduceToNat, ge_iff_le,
    ↓reduceIte]
  rw [nf_eq]
  omega

/-- The query row of the item's second stage (`256` rows further). -/
theorem qRowW_eq' (hpre : Pre P L mem0) {g i : Nat} (hw : workOf L g i < 2 ^ 32)
    (hm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31) :
    addW (Loader.qRowW L g i) (BitVec.ofInt 64 256) =
      BitVec.ofNat 64 (128 * rank L g + 512 * (coordsOf L (workOf L g i)).2.2 + 256) := by
  have hr : rank L g < 2 := Nat.mod_lt _ (by decide)
  rw [qRowW_eq hpre hw hm]
  generalize (coordsOf L (workOf L g i)).2.2 = m at hm ⊢
  generalize rank L g = r at hr ⊢
  simp only [addW, rd, nf_trunc, nf_add, nf_ofInt, nf_mod64_32,
    Nat.reducePow, Nat.reduceMod, Int.reduceMod, Int.reduceToNat]
  rw [nf_eq]
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Work.Dm
