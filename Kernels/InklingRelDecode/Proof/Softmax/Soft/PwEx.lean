-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.MxInv
public import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinMax
public import Kernels.InklingRelDecode.Proof.Lib.LaneFold
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpInXw
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Score
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants

@[expose] public section

/-! # The words of the probability store are the exact probabilities

At the store of pc 1009 the exponent window's registers read exactly: the scores of the first
window (`w1_cols`) and the maxima of the round (`MEx`) give the window's inputs exactly
(`expInX_of`), so word `p` of the store is the pair of the probabilities of columns `2p` and
`2p + 1` of the lane's half. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

theorem colOfSrc_srcTab : ∀ i < 64, colOfSrc (srcTab i) = i := by decide +kernel

/-- The score of the register `r` of the first window's result, by the column it holds. -/
noncomputable def regX (Q : Params) (L : Launch) (g i r : Nat) : EReal :=
  Lib.colX Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
    (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) i (64 * (g % L.block / 16 % 2) + colOfSrc r)

/-- **The exponent window's inputs are exact** at the store of the probabilities. -/
theorem exp_in_x {m : Mem0} (hp : Pre Q L m) {y : Data.D} (E : EntSp Q L g ent)
    (hP : ent.prior = w32 ((Q.past ((L.ctaidOf (g / L.block)).get .z) : Nat) : ℤ))
    (ht : g % L.block < 256) (hn : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z))
    (hseq : Q.seqK ((L.ctaidOf (g / L.block)).get .z) + 511 < 2 ^ 31)
    (hs : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)))
    (hc : ∀ j < 64, BW (y.v.cur j) (Lib.laneBias Q L g y.c.i j))
    (hmp : Ev (m0 y) (Lib.laneSt Q L g y.c.i).m)
    (hmx : Ev y.v.mx (max (Lib.laneSt Q L g y.c.i).m
      (Lib.SoftFold.blockMax (Lib.laneBlk Q L g y.c.i)))) :
    ExpIn (xV ent L g y) ∧ ExpInX (xV ent L g y) (regX Q L g y.c.i) (Q.scale * log2eF32)
      (Lib.mUseOf (Q.scale * log2eF32) (Lib.laneBlk Q L g y.c.i) (Lib.laneSt Q L g y.c.i) *
        (-(Q.scale * log2eF32))) := by
  obtain ⟨W, hvf, hpe, q179, q180⟩ := w1_cols hp E hP ht hn hseq hs hc
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  have hV : ∀ r, (r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523) →
      xV ent L g y r = Lib.alphaVal (scaleW L) (m0 y) y.v.mx r := fun r h => by simp [xV, h]
  have hsx : ∀ r ∈ scoreRegs, Ev (xV ent L g y r) (regX Q L g y.c.i r) := by
    intro r hr
    obtain ⟨h1, h2⟩ := scoreRegs_cls r hr
    simp only [xV, h1, h2, ite_false]
    rw [congrFun hvf r]
    exact scores_ev hpe r hr
  have h499 : Ev (xV ent L g y 499) ((-(Q.scale * log2eF32) : ℝ) : EReal) := by
    have e499 : xV ent L g y 499 = derV ent L g 499 := by simp [xV]
    rw [e499, derV_499 (scaleVal_float hp)]
    exact ⟨(erealValue_coe .f32 _).symm, EReal.coe_ne_top _⟩
  have X := expInX_of (scaleW_ev hp) hpos hmp hmx hV h499 hsx
    (by simpa [xV] using q179) (by simpa [xV] using q180)
  refine ⟨xV_expIn_s hp (fun r hr => ev_ni (hsx r hr)) (ev_ni hmp) (ev_ni hmx), ?_⟩
  exact X

/-- The shifted score of a column is the exponent of the lane's probability word. -/
theorem pw2_col (Q : Params) (L : Launch) (g i c : Nat) (hpos : 0 < Q.scale * log2eF32) :
    pw2 (Lib.colX Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
      (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) i (64 * (g % L.block / 16 % 2) + c) *
        ((Q.scale * log2eF32 : ℝ) : EReal) +
      ((Lib.mUseOf (Q.scale * log2eF32) (Lib.laneBlk Q L g i) (Lib.laneSt Q L g i) *
        (-(Q.scale * log2eF32)) : ℝ) : EReal)) = Lib.lanePw Q L g i c := by
  have key : 128 * (Q.splits * i + (L.ctaidOf (g / L.block)).get .x) +
      (64 * (g % L.block / 16 % 2) + c) = Lib.laneKey Q L g i c := by
    unfold Lib.laneKey; omega
  unfold Lib.colX Lib.keyX Lib.lanePw
  rw [key]
  split_ifs
  · rw [← EReal.coe_mul, ← EReal.coe_add]
    simp only [pw2, EReal.coe_ne_bot, ite_false, EReal.toReal_coe, Lib.pExp]
    congr 1
    unfold Lib.laneBias Lib.laneScore
    ring
  · rw [EReal.bot_mul_coe_of_pos hpos, EReal.bot_add]
    simp [pw2]

theorem idx_pair (p : Nat) : (1288 + 4 * p - 1288) / 2 = 2 * p ∧
    (1290 + 4 * p - 1288) / 2 = 2 * p + 1 := by omega

/-- **The 32 words of the probability store are the exact probabilities** of the lane's half. -/
theorem pw_words {m : Mem0} (hp : Pre Q L m) {y : Data.D} (site : y.c.site = .tmemSt)
    (E : EntSp Q L g ent)
    (hP : ent.prior = w32 ((Q.past ((L.ctaidOf (g / L.block)).get .z) : Nat) : ℤ))
    (ht : g % L.block < 256) (hn : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z))
    (hseq : Q.seqK ((L.ctaidOf (g / L.block)).get .z) + 511 < 2 ^ 31)
    (hs : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)))
    (hc : ∀ j < 64, BW (y.v.cur j) (Lib.laneBias Q L g y.c.i j)) (M : MEx Q L g y) :
    ExpIn (xV ent L g y) ∧ ∀ p < 32, vP2 (vP1 (xE ent L g y)) (1677 + p) =
      .pair (.float .bf16 (Lib.lanePw Q L g y.c.i (2 * p)))
        (.float .bf16 (Lib.lanePw Q L g y.c.i (2 * p + 1))) := by
  have hm0 : m0 y = y.v.mp := by simp [m0, site]
  obtain ⟨hE, X⟩ := exp_in_x hp E hP ht hn hseq hs hc
    (hm0 ▸ M.mp (by rw [site]; rfl)) (M.mx (by rw [site]; rfl))
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  refine ⟨hE, fun p hp' => ?_⟩
  have h := (exp_exact X).1 p hp'
  change vP2 (vP1 (vE3 (xV ent L g y))) (1677 + p) = _
  rw [h]
  obtain ⟨i1, i2⟩ := idx_pair p
  have e1 : regX Q L g y.c.i (srcTab (2 * p)) = Lib.colX Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g)
      y.c.i (64 * (g % L.block / 16 % 2) + 2 * p) := by
    unfold regX; rw [colOfSrc_srcTab _ (by omega)]
  have e2 : regX Q L g y.c.i (srcTab (2 * p + 1)) = Lib.colX Q
      ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
      (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) y.c.i
      (64 * (g % L.block / 16 % 2) + (2 * p + 1)) := by
    unfold regX; rw [colOfSrc_srcTab _ (by omega)]
  unfold pWord shifted
  rw [i1, i2, e1, e2, pw2_col Q L g _ _ hpos, pw2_col Q L g _ _ hpos]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
