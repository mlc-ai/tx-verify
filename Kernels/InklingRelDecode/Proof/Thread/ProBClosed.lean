-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAExit
public import Kernels.InklingRelDecode.Proof.Thread.ProBOps

@[expose] public section

/-! # Closed forms of the prologue's exit registers

The registers the prologue (pc 20 to 573) leaves for the later roles, as `Nat` expressions of its
inputs: the three loaded words `cu0 = cu_seqlens_q[req]`, `cu1 = cu_seqlens_q[req + 1]`,
`sk = seq_lens[req]` (`Dat.cu0`, `Dat.cu1`, `Dat.sk`), `num_splits` (`dt.pro.w71`), the split
index `ctaid.x` (`cta L g .x`) and the shared window base. Each theorem says that the value the
table (`ProATable`) gives the register is `BitVec.ofNat 64 e` for such an `e`; the table's terms
are the evaluator's own operations, so each is proved one operation at a time with the lemmas of
`ProBOps`, over `Nat` arithmetic, never by unfolding the whole chain.

| register | value | meaning |
| --- | --- | --- |
| `%r22` | `(past - 1023) / 128` | `n_bias` |
| `%r23` | `past / 128` | `fa_mask_right` |
| `%r24` | `⌈sk / 128⌉ * 128` | `rel_base + REL_PAD` |
| `%r176` | `num_splits - 1 - split + ⌈sk / 128⌉` | numerator of `num_iters` |
| `%r25`, `%r26` | `r176 / num_splits` | `num_iters` (`max(·, 0)` is the identity) |
| `%r217` | `num_splits - 1 - split + past / 128` | numerator of `num_old` |
| `%r32` | `min (min num_old num_iters) 3` | `num_pre` |
| `%r162`, `%r163` | `sharedBase + 213312`, `+ 213328` | barrier addresses |

The premises are `ArgsOk` (the thread's inherited registers) and `WordsOk` (the numeric
bounds of the loaded words, and that the two numerators are non-negative signed words);
`ProBSpec` derives the latter from `Pre`. The tables of the meanings in terms of `Spec` are
`ProBSpec`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The numeric bounds of `WordsOk` that the closed forms need. -/
abbrev Bnd (dt : Dat) : Prop :=
  dt.cu0 ≤ dt.cu1 ∧ dt.cu1 < 2 ^ 31 ∧ dt.cu1 - dt.cu0 ≤ dt.sk ∧ dt.sk + 255 < 2 ^ 31

def pastN (dt : Dat) : Nat := dt.sk - (dt.cu1 - dt.cu0)

theorem r20_val (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r20 L g dt = BitVec.ofNat 64 (dt.cu1 - dt.cu0) := by
  simp only [v_r20, v_r150, v_r149, wSub32_ofNat]
  congr 1
  omega

theorem r21_val (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r21 L g dt = BitVec.ofNat 64 (pastN dt) := by
  simp only [v_r21, v_r151, r20_val L g dt hb, wSub32_ofNat, pastN]
  congr 1
  omega

theorem r165_val (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r165 L g dt = BitVec.ofNat 64 (pastN dt - 1023) := by
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  have l1 : BitVec.ofInt 64 (-1023) = BitVec.ofNat 64 (2 ^ 64 - 1023) := by
    rw [nf_ofInt]; rfl
  have l0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := by
    rw [nf_ofInt]; rfl
  simp only [v_r165, v_r164, r21_val L g dt hb, l1, l0, wAdd32_ofNat, wMaxS32_eq,
    truncBits_ofNat _ _ (by omega : 32 ≤ 64), tos32, Nat.mod_mod, Nat.reducePow, Nat.reduceSub,
    Nat.zero_mod, Nat.cast_zero]
  split_ifs <;> first | (exfalso; omega) | (refine congrArg (BitVec.ofNat 64) ?_; omega)

theorem ofNat_congr {x y : Nat} (h : x = y) : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
  rw [h]

theorem r22_eq (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r22 L g dt = BitVec.ofNat 64 ((pastN dt - 1023) / 128) := by
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  have l7 : BitVec.ofInt 64 7 = BitVec.ofNat 64 7 := by
    rw [nf_ofInt]; rfl
  simp only [v_r22, r165_val L g dt hb, l7, wShrU32_ofNat _ _ (by omega : 7 < 32)]
  refine ofNat_congr ?_
  omega

theorem r168_val (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r168 L g dt = BitVec.ofNat 64 (pastN dt) := by
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  have l31 : BitVec.ofInt 64 31 = BitVec.ofNat 64 31 := by
    rw [nf_ofInt]; rfl
  have l25 : BitVec.ofInt 64 25 = BitVec.ofNat 64 25 := by
    rw [nf_ofInt]; rfl
  simp only [v_r168, v_r167, v_r166, r21_val L g dt hb, l31, l25,
    wShrS32_ofNat _ _ hp (by omega : 31 ≤ 32), wShrU32_ofNat _ _ (by omega : 25 < 32),
    wAdd32_ofNat]
  refine ofNat_congr ?_
  omega

theorem r23_eq (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r23 L g dt = BitVec.ofNat 64 (pastN dt / 128) := by
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  have l7 : BitVec.ofInt 64 7 = BitVec.ofNat 64 7 := by
    rw [nf_ofInt]; rfl
  simp only [v_r23, r168_val L g dt hb, l7, wShrS32_ofNat _ _ hp (by omega : 7 ≤ 32)]
  refine ofNat_congr ?_
  omega

theorem r172_val (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r172 L g dt = BitVec.ofNat 64 (dt.sk + 127) := by
  have hp : dt.sk + 127 < 2 ^ 31 := by omega
  have l31 : BitVec.ofInt 64 31 = BitVec.ofNat 64 31 := by
    rw [nf_ofInt]; rfl
  have l25 : BitVec.ofInt 64 25 = BitVec.ofNat 64 25 := by
    rw [nf_ofInt]; rfl
  have l127 : BitVec.ofInt 64 127 = BitVec.ofNat 64 127 := by
    rw [nf_ofInt]; rfl
  simp only [v_r172, v_r171, v_r170, v_r169, v_r151, l31, l25, l127, wAdd32_ofNat,
    wShrS32_ofNat _ _ (by omega : (dt.sk + 127) % 2 ^ 32 < 2 ^ 31) (by omega : 31 ≤ 32),
    wShrU32_ofNat _ _ (by omega : 25 < 32)]
  refine ofNat_congr ?_
  omega

theorem r173_val (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r173 L g dt = BitVec.ofNat 64 ((dt.sk + 127) / 128) := by
  have hp : dt.sk + 127 < 2 ^ 31 := by omega
  have l7 : BitVec.ofInt 64 7 = BitVec.ofNat 64 7 := by
    rw [nf_ofInt]; rfl
  simp only [v_r173, r172_val L g dt hb, l7, wShrS32_ofNat _ _ hp (by omega : 7 ≤ 32)]
  refine ofNat_congr ?_
  omega

theorem r24_eq (L : Launch) (g : Nat) (dt : Dat) (hb : Bnd dt) :
    v_r24 L g dt = BitVec.ofNat 64 ((dt.sk + 127) / 128 * 128) := by
  have l128 : BitVec.ofInt 64 (-128) = BitVec.ofNat 64 (2 ^ 64 - 128) := by
    rw [nf_ofInt]; rfl
  simp only [v_r24, r172_val L g dt hb, l128, wAnd32_ofNat]
  have h : (2 ^ 64 - 128) % 2 ^ 32 = 2 ^ 32 - 2 ^ 7 := by omega
  rw [h, CeilDiv.land_highMask _ 32 7 (by omega)]
  refine ofNat_congr ?_
  omega

theorem wCta_eq (L : Launch) (g : Nat) (d : Dim) :
    wCta L g d = BitVec.ofNat 64 (cta L g d % 2 ^ 32) := by
  simp only [wCta, cta, truncBits_ofNat _ _ (by omega : 32 ≤ 64)]

theorem r175_val (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro) :
    v_r175 L g dt = BitVec.ofNat 64 (dt.pro.w71 - 1 - cta L g .x) := by
  have h1 := ha.splitsRange
  have h2 := ha.splitIdx
  simp only [v_r175, v_r174, v_r17, v_r71, wCta_eq, wNot32_ofNat, wAdd32_ofNat]
  refine ofNat_congr ?_
  omega

theorem r176_eq (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro) (hb : Bnd dt) :
    v_r176 L g dt = BitVec.ofNat 64 (dt.pro.w71 - 1 - cta L g .x + (dt.sk + 127) / 128) := by
  have h1 := ha.splitsRange
  have h2 := ha.splitIdx
  simp only [v_r176, r175_val L g dt ha, r173_val L g dt hb, wAdd32_ofNat]
  refine ofNat_congr ?_
  omega

theorem r217_eq (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro) (hb : Bnd dt) :
    v_r217 L g dt = BitVec.ofNat 64 (dt.pro.w71 - 1 - cta L g .x + pastN dt / 128) := by
  have h1 := ha.splitsRange
  have h2 := ha.splitIdx
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  simp only [v_r217, r175_val L g dt ha, r23_eq L g dt hb, wAdd32_ofNat]
  refine ofNat_congr ?_
  omega

theorem nonneg_s32 (n : Nat) (h : n < 2 ^ 32) :
    0 ≤ intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 n)) ↔ n < 2 ^ 31 := by
  simp only [intOf, ↓reduceIte, truncBits_ofNat _ _ (by omega : 32 ≤ 64), tos32]
  split_ifs <;> omega

/-- The numerator of the first division is a non-negative signed word iff it is below `2 ^ 31`. -/
theorem num176_lt (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hw : WordsOk L g dt) :
    dt.pro.w71 - 1 - cta L g .x + (dt.sk + 127) / 128 < 2 ^ 31 := by
  have h1 := ha.splitsRange
  have h2 := ha.splitIdx
  have hb := hw.1
  have h := hw.2.1
  rw [r176_eq L g dt ha hb] at h
  refine (nonneg_s32 _ (by omega)).1 h

theorem num217_lt (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hw : WordsOk L g dt) :
    dt.pro.w71 - 1 - cta L g .x + pastN dt / 128 < 2 ^ 31 := by
  have h1 := ha.splitsRange
  have h2 := ha.splitIdx
  have hb := hw.1
  have hp : pastN dt < 2 ^ 31 := by unfold pastN; omega
  have h := hw.2.2
  rw [r217_eq L g dt ha hb] at h
  refine (nonneg_s32 _ (by omega)).1 h

/-- `num_iters` before the clamp, as a number: `(num_splits - 1 - split + ⌈seq_lens/128⌉) /
num_splits`. -/
def itersN (L : Launch) (g : Nat) (dt : Dat) : Nat :=
  (dt.pro.w71 - 1 - cta L g .x + (dt.sk + 127) / 128) / dt.pro.w71

/-- `num_old` before the clamp. -/
def oldN (L : Launch) (g : Nat) (dt : Dat) : Nat :=
  (dt.pro.w71 - 1 - cta L g .x + pastN dt / 128) / dt.pro.w71

section
variable (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
include L g dt ha

theorem itersN_lt (hw : WordsOk L g dt) : itersN L g dt < 2 ^ 31 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (num176_lt L g dt ha hw)

theorem oldN_lt (hw : WordsOk L g dt) : oldN L g dt < 2 ^ 31 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (num217_lt L g dt ha hw)

theorem r25_eq (hw : WordsOk L g dt) : v_r25 L g dt = BitVec.ofNat 64 (itersN L g dt) := by
  simp only [v_r25, r176_eq L g dt ha hw.1, v_r71, itersN,
    wDivS32_ofNat _ _ (num176_lt L g dt ha hw) ha.splitsRange]

theorem r26_eq (hw : WordsOk L g dt) : v_r26 L g dt = BitVec.ofNat 64 (itersN L g dt) := by
  have l0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := by
    rw [nf_ofInt]; rfl
  have := itersN_lt L g dt ha hw
  simp only [v_r26, r25_eq L g dt ha hw, l0, wMaxS32_pos _ _ this (by omega : 0 < 2 ^ 31)]
  refine ofNat_congr ?_
  omega

theorem v_r218_val (hw : WordsOk L g dt) : v_r218 L g dt = BitVec.ofNat 64 (oldN L g dt) := by
  simp only [v_r218, r217_eq L g dt ha hw.1, v_r71, oldN,
    wDivS32_ofNat _ _ (num217_lt L g dt ha hw) ha.splitsRange]

theorem v_r219_val (hw : WordsOk L g dt) : v_r219 L g dt = BitVec.ofNat 64 (oldN L g dt) := by
  have l0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := by
    rw [nf_ofInt]; rfl
  have := oldN_lt L g dt ha hw
  simp only [v_r219, v_r218_val L g dt ha hw, l0,
    wMaxS32_pos _ _ this (by omega : 0 < 2 ^ 31)]
  refine ofNat_congr ?_
  omega

theorem v_r31_val (hw : WordsOk L g dt) :
    v_r31 L g dt = BitVec.ofNat 64 (min (oldN L g dt) (itersN L g dt)) := by
  simp only [v_r31, v_r219_val L g dt ha hw, r26_eq L g dt ha hw,
    wMinS32_pos _ _ (oldN_lt L g dt ha hw) (itersN_lt L g dt ha hw)]

theorem r32_eq (hw : WordsOk L g dt) :
    v_r32 L g dt = BitVec.ofNat 64 (min (min (oldN L g dt) (itersN L g dt)) 3) := by
  have l3 : BitVec.ofInt 64 3 = BitVec.ofNat 64 3 := by
    rw [nf_ofInt]; rfl
  have h1 := oldN_lt L g dt ha hw
  have h2 := itersN_lt L g dt ha hw
  simp only [v_r32, v_r31_val L g dt ha hw, l3, wMinU32_ofNat]
  refine ofNat_congr ?_
  omega
end

theorem r162_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r162 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213312) % 2 ^ 32) := by
  have l : BitVec.ofInt 64 213312 = BitVec.ofNat 64 213312 := by
    rw [nf_ofInt]; rfl
  simp only [v_r162, v_r205, wSmem, l, truncBits_ofNat _ _ (by omega : 32 ≤ 64), wAdd32_ofNat]
  refine ofNat_congr ?_
  omega

theorem r163_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_r163 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213328) % 2 ^ 32) := by
  have l : BitVec.ofInt 64 213328 = BitVec.ofNat 64 213328 := by
    rw [nf_ofInt]; rfl
  simp only [v_r163, v_r205, wSmem, l, truncBits_ofNat _ _ (by omega : 32 ≤ 64), wAdd32_ofNat]
  refine ofNat_congr ?_
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
