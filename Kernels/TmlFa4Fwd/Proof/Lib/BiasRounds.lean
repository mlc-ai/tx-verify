-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.SWord
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasNum
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.SuPick
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's Bias groups are the softmax lanes' biased rounds

`bias_rounds`: for the picked tile, the Bias groups of stage `st` the loader takes (`biasTot` of its
setup) are one more than the biased rounds after the first that the stage's softmax lanes make
(`Softmax.nB`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option linter.unusedSimpArgs false

/-- Clearing the low seven bits. -/
theorem and_mask {a : Nat} (h : a < 2 ^ 32) : a &&& (2 ^ 32 - 128) = a / 128 * 128 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : i < 32
  · have hm : ∀ i : Fin 32, (2 ^ 32 - 2 ^ 7 : Nat).testBit i.val = decide (7 ≤ i.val) := by decide
    rw [hm ⟨i, hi⟩]
    by_cases h7 : 7 ≤ i
    · simp [h7]
    · simp [h7]
  · have h1 : a.testBit i = false := Nat.testBit_lt_two_pow
      (h.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1]
    by_cases h7 : 7 ≤ i
    · rw [show i - 7 + 7 = i by omega, h1]; simp
    · simp [h7]

/-- The signed value of a ceiling by 128. -/
theorem S_ceil_eq (x : BitVec 64) : S (Mma.ceil128 x) = (S x + 127) / 128 := by
  have hr := S_range x
  have hsg : S (shru (shrs x 31) 25) = if S x < 0 then 127 else 0 := by
    have h31 : (i32 31).toNat = 31 := by decide
    have h25 : (i32 25).toNat = 25 := by decide
    have he : shrs x 31 = truncBits 32 (BitVec.ofInt 64 (S x / 2 ^ 31)) := by
      simp only [shrs, h31]
      rfl
    rw [he]
    split
    · rw [show S x / 2 ^ 31 = -1 by omega]
      decide
    · rw [show S x / 2 ^ 31 = 0 by omega]
      decide
  unfold Mma.ceil128
  dsimp only
  have hs : S (add32 x (shru (shrs x 31) 25)) = S x + if S x < 0 then 127 else 0 := by
    rw [S_add (by rw [hsg]; split <;> omega) (by rw [hsg]; split <;> omega), hsg]
  have hcmp : (scmpi .gt .s x (-1) && scmp .ne .b x
      (andi (add32 x (shru (shrs x 31) 25)) (-128))) = decide (0 ≤ S x ∧ ¬ S x % 128 = 0) := by
    have hgt : scmpi .gt .s x (-1) = decide (-1 < S x) := by
      rw [Loader.scmpi_gt_s _ (by decide) (by decide), show Loader.sv x = S x from
        (Loader.sv_r32 x).symm]
    rw [hgt]
    by_cases h0 : 0 ≤ S x
    swap
    · simp [h0, show ¬ -1 < S x by omega]
    simp only [show -1 < S x by omega, decide_true, Bool.true_and, h0, true_and]
    have hz : shru (shrs x 31) 25 = 0 := by
      have h31 : (i32 31).toNat = 31 := by decide
      have he : shrs x 31 = truncBits 32 (BitVec.ofInt 64 (S x / 2 ^ 31)) := by
        simp only [shrs, h31]
        rfl
      rw [he, show S x / 2 ^ 31 = 0 by omega]
      decide
    rw [hz]
    have hx : S x = ((x.toNat % 2 ^ 32 : Nat) : Int) := by
      rw [S_def] at h0 ⊢
      split_ifs at h0 ⊢ <;> omega
    have ha : (andi (add32 x 0) (-128)).toNat = x.toNat % 2 ^ 32 / 128 * 128 := by
      have e1 : (r32 (add32 x 0)).toNat = x.toNat % 2 ^ 32 := by
        rw [r32, tr_toNat, add32_toNat']
        simp
      have e2 : (i32 (-128)).toNat = 2 ^ 32 - 128 := by decide
      rw [andi, BitVec.toNat_and, e1, e2, and_mask (Nat.mod_lt _ (by norm_num))]
    have hne : scmp .ne .b x (andi (add32 x 0) (-128)) =
        decide (x.toNat % 2 ^ 32 ≠ x.toNat % 2 ^ 32 / 128 * 128) := by
      have e3 : (r32 x).toNat = x.toNat % 2 ^ 32 := by rw [r32, tr_toNat]
      have e4 : (r32 (andi (add32 x 0) (-128))).toNat = x.toNat % 2 ^ 32 / 128 * 128 := by
        rw [r32, tr_toNat, ha]
        have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
        omega
      simp only [scmp, compare]
      rw [← e4, ← e3]
      by_cases hq : r32 x = r32 (andi (add32 x 0) (-128))
      · simp [hq]
      · have : (r32 x).toNat ≠ (r32 (andi (add32 x 0) (-128))).toNat := fun h =>
          hq (BitVec.eq_of_toNat_eq h)
        simp [hq, this]
    rw [hne, hx]
    congr 1
    apply propext
    omega
  rw [hcmp]
  have hc : ∀ c : Bool, S (sel c (i32 1) (i32 0)) = if c then 1 else 0 := by decide
  rw [S_add (by rw [S_shrs7, hs, hc]; split_ifs <;> omega)
    (by rw [S_shrs7, hs, hc]; split_ifs <;> omega), S_shrs7, hs, hc]
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem S_congr {x y : BitVec 64} (h : x.toNat % 2 ^ 32 = y.toNat % 2 ^ 32) : S x = S y := by
  rw [S_def, S_def, h]

/-- Ceilings of words 128 apart. -/
theorem ceil_step {x y : BitVec 64}
    (h : x.toNat % 2 ^ 32 = (y.toNat % 2 ^ 32 + 128) % 2 ^ 32) :
    S (Mma.ceil128 y) = S (Mma.ceil128 x) - 1 ∨ S (Mma.ceil128 x) < 0 := by
  rw [S_ceil_eq, S_ceil_eq, S_def, S_def]
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  have := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by norm_num)
  generalize x.toNat % 2 ^ 32 = a at *
  generalize y.toNat % 2 ^ 32 = b at *
  split_ifs <;> omega

/-- The arithmetic. -/
theorem rounds_arith {cu a0 a1 B M : Int} (hB : B = min cu a1) (hM : M = min cu a0)
    (h : a0 = a1 - 1 ∨ a1 < 0) :
    (1 + (B - 1 - max (B - min (B - M + 10) B) 0).toNat =
      1 + (if B < 2 then 0 else (min (max (B - 1) 0) 9).toNat) +
        if 10 < B ∧ M - B < 0 then 1 else 0) ∧
    1 + (B - 1 - max (B - min (B - B + 10) B) 0).toNat =
      1 + (if B < 2 then 0 else (min (max (B - 1) 0) 9).toNat) := by
  split_ifs <;> constructor <;> omega

/-- The loader's ceilings are the softmax warps'. -/
private theorem words {w u d : BitVec 64} :
    addi (add32 (add32 (shl (Softmax.or32 (shl w 1) (i32 1)) 7) u) d) 128 =
      addi (add32 (add32 (shl w 8) u) d) 256 ∧
    addi (add32 (add32 (shl (Softmax.or32 (shl w 1) (i32 0)) 7) u) d) 128 =
      addi (add32 (add32 (shl w 8) u) d) 128 := by
  have hsh : ∀ (x : BitVec 64) (n : Int), (i32 n).toNat < 32 →
      (shl x n).toNat = x.toNat % 2 ^ 32 * 2 ^ (i32 n).toNat % 2 ^ 32 := by
    intro x n h
    simp only [shl, show ¬ (i32 n).toNat ≥ 32 by omega, ↓reduceIte]
    rw [tr_toNat, BitVec.toNat_shiftLeft, r32, tr_toNat, Nat.shiftLeft_eq,
      Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
  have h1 : (i32 1).toNat = 1 := by decide
  have h7 : (i32 7).toNat = 7 := by decide
  have h8 : (i32 8).toNat = 8 := by decide
  have h0 : (i32 0).toNat = 0 := by decide
  have hor : ∀ b : Nat, b < 2 → ∀ y : BitVec 64, y.toNat = b →
      (Softmax.or32 (shl w 1) y).toNat = w.toNat % 2 ^ 32 * 2 % 2 ^ 32 + b := by
    intro b hb y hy
    rw [Softmax.or32, BitVec.toNat_or, r32, r32, tr_toNat, tr_toNat, hsh _ _ (by rw [h1]; omega),
      h1, hy, pow_one, Nat.mod_mod, Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega)]
    have := Nat.two_pow_add_eq_or_of_lt (i := 1) (b := b) (by omega)
      (w.toNat % 2 ^ 32 * 2 % 2 ^ 32 / 2)
    rw [pow_one, show 2 * (w.toNat % 2 ^ 32 * 2 % 2 ^ 32 / 2) = w.toNat % 2 ^ 32 * 2 % 2 ^ 32 by
      omega] at this
    exact this.symm
  have had : ∀ (x : BitVec 64) (n : Int), (addi x n).toNat =
      (x.toNat % 2 ^ 32 + (i32 n).toNat) % 2 ^ 32 := by
    intro x n
    show (truncBits 32 (r32 x + i32 n)).toNat = _
    rw [tr_toNat, BitVec.toNat_add, r32, tr_toNat,
      Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
  have h128 : (i32 128).toNat = 128 := by decide
  have h256 : (i32 256).toNat = 256 := by decide
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [had, add32_toNat', hsh _ _ (show (i32 7).toNat < 32 by rw [h7]; omega),
      hsh _ _ (show (i32 8).toNat < 32 by rw [h8]; omega), h7, h8, h128, h256]
  · rw [hor 1 (by omega) _ h1]
    generalize w.toNat % 2 ^ 32 = w
    generalize u.toNat % 2 ^ 32 = u
    generalize d.toNat % 2 ^ 32 = d
    omega
  · rw [hor 0 (by omega) _ h0]
    generalize w.toNat % 2 ^ 32 = w
    generalize u.toNat % 2 ^ 32 = u
    generalize d.toNat % 2 ^ 32 = d
    omega

/-- The biased rounds, as a function of the two block counts. -/
private theorem nB_eq {p : Params} {L : Launch} {g : Nat} (v : Softmax.V) (M : BitVec 64)
    (hM : M = min32 (Mma.ceil128 v.ukw) (Mma.ceil128 (addi (add32 (add32 (Softmax.r1808 p L g v)
      v.ukw) (sub32 v.sc.c0 v.sc.c1)) 128))) :
    Softmax.nB p L g v = S (Softmax.r166 p L g v) - 1 - max (S (Softmax.r166 p L g v) -
      min (S (Softmax.r166 p L g v) - S M + 10) (S (Softmax.r166 p L g v))) 0 := by
  have c1 := S_ceil v.ukw
  have c2 := S_ceil (Softmax.r165 p L g v)
  have hB : S (Softmax.r166 p L g v) =
      min (S (Mma.ceil128 v.ukw)) (S (Mma.ceil128 (Softmax.r165 p L g v))) := S_min _ _
  have hMS : -2 ^ 25 ≤ S M ∧ S M ≤ 2 ^ 25 := by
    rw [hM, S_min]
    have c3 := S_ceil (addi (add32 (add32 (Softmax.r1808 p L g v)
      v.ukw) (sub32 v.sc.c0 v.sc.c1)) 128)
    omega
  have h168 : S (Softmax.r168 p L g v) = S (Softmax.r166 p L g v) - S M + 10 := by
    unfold Softmax.r168
    rw [← hM]
    generalize Softmax.r166 p L g v = B at hB ⊢
    have hs := S_sub (x := B) (y := M) (by omega) (by omega)
    rw [S_addi (by decide) (by omega) (by omega), hs]
  have h299 : S (Softmax.r299 p L g v) = max (S (Softmax.r166 p L g v) -
      min (S (Softmax.r168 p L g v)) (S (Softmax.r166 p L g v))) 0 := by
    unfold Softmax.r299
    generalize Softmax.r168 p L g v = D at h168 ⊢
    generalize Softmax.r166 p L g v = B at hB h168 ⊢
    have h0 : S (i32 0) = 0 := by decide
    show S (Softmax.max32 (sub32 B (min32 D B)) (i32 0)) = _
    have hm := S_min D B
    rw [S_max, h0, S_sub (by rw [hm]; omega) (by rw [hm]; omega), hm]
  have h169 : S (Softmax.r169 p L g v) = S (Softmax.r166 p L g v) - 1 := by
    unfold Softmax.r169
    generalize Softmax.r166 p L g v = B at hB ⊢
    rw [S_addi (by decide) (by omega) (by omega)]
    omega
  rw [← h168, ← h299]
  show S (sub32 (Softmax.r169 p L g v) (Softmax.r299 p L g v)) = _
  generalize Softmax.r169 p L g v = E at h169 ⊢
  generalize Softmax.r299 p L g v = F at h299 ⊢
  rw [S_sub (by omega) (by omega), h169]

/-- **The Bias groups of the picked tile are one more than the biased rounds after the first.** -/
theorem bias_rounds {p : Params} {L : Launch} {y g : Nat} (hc : y / L.block = g / L.block)
    (R : Nat) (bal : BitVec 64) {v : Loader.V}
    (h28 : v.su.r28 = (Loader.setup p L y (Loader.refVL p L y R bal)).r28)
    (h29 : v.su.r29 = (Loader.setup p L y (Loader.refVL p L y R bal)).r29) :
    Loader.biasTot v (Softmax.stg L g) =
      1 + (Softmax.nB p L g (softRef p L g R bal)).toNat := by
  set V := softRef p L g R bal with hV
  have hrow : (Loader.coords p L y (Loader.refVL p L y R bal).sc).row =
      Softmax.rowOff p L g V.sc := by
    simp only [Loader.coords, Loader.refVL, Softmax.rowOff, Mma.coords, hV, softRef,
      Epilogue.ctaW, hc]
    rw [row_agree]
  have hu : (Loader.refVL p L y R bal).ukw = V.ukw := by
    simp only [Loader.refVL, hV, softRef, Mma.ukv, hc]
  have h0 : (Loader.refVL p L y R bal).sc.c0 = V.sc.c0 := by
    simp only [Loader.refVL, hV, softRef, hc]
  have h1 : (Loader.refVL p L y R bal).sc.c1 = V.sc.c1 := by
    simp only [Loader.refVL, hV, softRef, hc]
  have hB : v.su.r28 = Softmax.r166 p L g V := by
    rw [h28]
    simp only [Loader.setup, Softmax.r166, Softmax.r165, Mma.ceil128, Loader.cdivS, Loader.cdivP,
      ← hrow, ← hu, ← h0, ← h1]
    rfl
  have hR : v.su.r29 = sub32 (min32 (Mma.ceil128 V.ukw) (Mma.ceil128 (addi (add32 (add32
      (shl (Softmax.rowOff p L g V.sc) 8) V.ukw) (sub32 V.sc.c0 V.sc.c1)) 128)))
      (Softmax.r166 p L g V) := by
    rw [h29, ← hB, h28]
    simp only [Loader.setup, Mma.ceil128, Loader.cdivS, Loader.cdivP,
      ← hrow, ← hu, ← h0, ← h1]
    rfl
  clear_value V
  clear hV hrow hu h0 h1 h28 h29
  set u := V.ukw
  set w := Softmax.rowOff p L g V.sc with hw
  set dd := sub32 V.sc.c0 V.sc.c1 with hdd
  set y0 := addi (add32 (add32 (shl w 8) u) dd) 128 with hy0
  have h165 : Softmax.r165 p L g V = addi (add32 (add32 (shl w 8) u) dd) 256 := rfl
  have had : ∀ (x : BitVec 64) (n : Int), (addi x n).toNat =
      (x.toNat % 2 ^ 32 + (i32 n).toNat) % 2 ^ 32 := by
    intro x n
    show (truncBits 32 (r32 x + i32 n)).toNat = _
    rw [tr_toNat, BitVec.toNat_add, r32, tr_toNat,
      Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
  have hstep := ceil_step (x := Softmax.r165 p L g V) (y := y0) (by
    rw [h165, hy0, had, had, show (i32 128).toNat = 128 by decide,
      show (i32 256).toNat = 256 by decide]
    omega)
  have hBS : S (Softmax.r166 p L g V) =
      min (S (Mma.ceil128 u)) (S (Mma.ceil128 (Softmax.r165 p L g V))) := S_min _ _
  have hM0 := S_min (Mma.ceil128 u) (Mma.ceil128 y0)
  have c1 := S_ceil u
  have c2 := S_ceil (Softmax.r165 p L g V)
  have c3 := S_ceil y0
  have hsv : ∀ x, Loader.sv x = S x := fun x => (Loader.sv_r32 x).symm
  have hm1 : Loader.sv (addi (Softmax.r166 p L g V) (-1)) = S (Softmax.r166 p L g V) - 1 := by
    rw [hsv, S_addi (by decide) (by omega) (by omega)]
    omega
  have hlast : Loader.Last v ↔ 10 < S (Softmax.r166 p L g V) ∧
      S (min32 (Mma.ceil128 u) (Mma.ceil128 y0)) - S (Softmax.r166 p L g V) < 0 := by
    unfold Loader.Last
    rw [hB, hR, hsv, hsv, S_sub (by omega) (by omega)]
  obtain ⟨ar0, ar1⟩ := rounds_arith hBS hM0 hstep
  have hw0 : Loader.w0 v.su.r28 = if S (Softmax.r166 p L g V) < 2 then 0 else
      (min (max (S (Softmax.r166 p L g V) - 1) 0) 9).toNat := by
    rw [hB, Loader.w0, Loader.wRn, hm1, hsv]
  obtain ⟨w1, w2⟩ := words (w := w) (u := u) (d := dd)
  cases hst : Softmax.stg L g with
  | true =>
    rw [nB_eq V (Softmax.r166 p L g V) (by
      rw [Softmax.r1808, hst]
      simp only [sel, ↓reduceIte]
      rw [← hw, ← hdd, w1]
      rfl), ar1, Loader.biasTot, hw0]
    simp
  | false =>
    rw [nB_eq V (min32 (Mma.ceil128 u) (Mma.ceil128 y0)) (by
      rw [Softmax.r1808, hst]
      simp only [sel, Bool.false_eq_true, ↓reduceIte]
      rw [← hw, ← hdd, w2]), ar0, Loader.biasTot, hw0]
    simp only [hlast, true_and]

end
end PTX.Kernels.TmlFa4Fwd.Proof
