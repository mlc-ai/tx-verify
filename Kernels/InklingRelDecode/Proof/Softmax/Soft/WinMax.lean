-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinIn
public import Kernels.InklingRelDecode.Proof.Lib.WinHalf
public import Kernels.InklingRelDecode.Proof.Softmax.Data.IntWord
import Kernels.InklingRelDecode.Proof.Softmax.Data.PickIw
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Preds
import Kernels.InklingRelDecode.Proof.Softmax.Data.PredIn
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Fin
import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskFin
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Score
import Kernels.InklingRelDecode.Proof.Lib.Rows

@[expose] public section

/-! # The first window's maximum is the lane's half maximum

From the score and bias words of the value state, the sent word (register 1520 at the shuffle
of pc 1838) is the exact maximum of the lane's 64 columns over the visible keys. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

theorem canon_canon (d : Data.D) : canon (canon d) = canon d := by
  simp [canon, m0]

theorem w1V_canon (d : Data.D) : w1V ent L g (canon d) = w1V ent L g d := by
  simp [w1V, canon_canon]

/-- **The first window's pairs are the exact scores**, on the words of the scores, biases and
mask: register `2447 + j` holds columns `2 j` and `2 j + 1` of the lane's half. -/
theorem w1_cols {m : Mem0} (hp : Pre Q L m) {y : Data.D} (E : EntSp Q L g ent)
    (hP : ent.prior = w32 ((Q.past ((L.ctaidOf (g / L.block)).get .z) : Nat) : ℤ))
    (ht : g % L.block < 256) (hn : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z))
    (hseq : Q.seqK ((L.ctaidOf (g / L.block)).get .z) + 511 < 2 ^ 31)
    (hs : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)))
    (hc : ∀ j < 64, BW (y.v.cur j) (Lib.laneBias Q L g y.c.i j)) :
    ∃ W, vFin (w1V ent L g y) = runM.V' W ∧ PairsEv W (fun c => Lib.colX Q
      ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
      (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) y.c.i
      (64 * (g % L.block / 16 % 2) + c)) ∧
      (∃ q, vFin (w1V ent L g y) 179 = .pred q) ∧ ∃ q, vFin (w1V ent L g y) 180 = .pred q := by
  have bi := bias_in_w1 (e := ent) (g := g) hp hs hc
  obtain ⟨hsp, hsc⟩ : 0 < Q.splits ∧ 0 < Q.scale := ⟨hp.splitsPos, hp.scalePos⟩
  have hb1 := E.split
  have hb2 := E.splits
  have hb3 := E.nbias
  have tk : Control.token (g % L.block) = Lib.softRow (g % L.block) / 6 := by
    have : ∀ r < 64, r * 43 / 256 = r / 6 := by decide
    exact this (Control.row (g % L.block)) (by unfold Control.row; omega)
  have hnb : Q.nBias ((L.ctaidOf (g / L.block)).get .z) =
      (Q.past ((L.ctaidOf (g / L.block)).get .z) - 1023) / 128 := rfl
  have hbl : Q.blocks ((L.ctaidOf (g / L.block)).get .z) * 128 ≤
      Q.seqK ((L.ctaidOf (g / L.block)).get .z) + 127 := by
    unfold Params.blocks; omega
  have hpast : Q.past ((L.ctaidOf (g / L.block)).get .z) ≤
      Q.seqK ((L.ctaidOf (g / L.block)).get .z) := Nat.sub_le _ _
  have n1 : ent.split + y.c.i * ent.splits =
      Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x := by
    rw [hb1, hb2]; ring
  have hb : (ent.split + (canon y).c.i * ent.splits) * 128 + 127 < 2 ^ 31 := by
    change (ent.split + y.c.i * ent.splits) * 128 + 127 < 2 ^ 31
    omega
  have p96 := pick96_iff (e := ent) (L := L) (g := g) (d := canon y) rfl
    (by change ((ent.split + y.c.i * ent.splits : Nat) : ℤ) < 2 ^ 31; omega) (by omega)
  have p97 := pick97_iff (e := ent) (L := L) (g := g) (d := canon y) rfl hP hb (by omega)
    (by omega)
  have mi := maskIn_w1 (e := ent) (L := L) (g := g) (d := canon y) rfl hP ht (by omega)
  rw [w1V_canon] at p96 p97 mi
  obtain ⟨W, hvf, hpe⟩ := w1_pairs bi mi
  have heq : ∀ c < 64, w1Score (w1V ent L g y) (Lib.laneScore Q L g y.c.i)
      (Lib.laneBias Q L g y.c.i) (1 / Q.scale) ((g % L.block / 16 % 2 * 64 : Nat) : ℤ)
      (((ent.split + (canon y).c.i * ent.splits) * 128 : Nat) : ℤ)
      ((Q.past ((L.ctaidOf (g / L.block)).get .z) : ℤ) + (token (g % L.block) : Nat)) c =
      Lib.colX Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
        (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) y.c.i
        (64 * (g % L.block / 16 % 2) + c) := by
    intro c hc64
    have ci : (canon y).c.i = y.c.i := rfl
    rw [ci, n1] at p96 p97 mi ⊢
    have key : Lib.laneKey Q L g y.c.i c = 128 * (Q.splits * y.c.i +
        (L.ctaidOf (g / L.block)).get .x) + (64 * (g % L.block / 16 % 2) + c) := by
      unfold Lib.laneKey; omega
    unfold w1Score Lib.colX Lib.keyX
    rw [← key]
    change _ = if _ ≤ _ then ((Lib.laneBias Q L g y.c.i c * (1 / Q.scale) +
      Lib.laneScore Q L g y.c.i c : ℝ) : EReal) else ⊥
    have hc2 : g % L.block / 16 % 2 * 64 + c < 128 := by omega
    by_cases h96 : pick96 (w1V ent L g y) = true
    · have hlt : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
          Q.nBias ((L.ctaidOf (g / L.block)).get .z) := by
        have := of_decide_eq_true (p96.symm.trans h96)
        rw [hb3] at this
        omega
      have hz0 := laneBias_zero hlt c hc64
      have vis : Lib.laneKey Q L g y.c.i c ≤ Q.past ((L.ctaidOf (g / L.block)).get .z) +
          Lib.softRow (g % L.block) / 6 := by
        unfold Lib.laneKey; omega
      simp [h96, hz0, vis]
    have h96f : pick96 (w1V ent L g y) = false := by simpa using h96
    have tkn : token (g % L.block) < 11 := by rw [tk]; unfold Lib.softRow; omega
    by_cases h97 : pick97 (w1V ent L g y) = true
    · have hle := of_decide_eq_true (p97.symm.trans h97)
      have hle' : (Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x) * 128 + 127 ≤
          Q.past ((L.ctaidOf (g / L.block)).get .z) := by exact_mod_cast hle
      have vis : Lib.laneKey Q L g y.c.i c ≤ Q.past ((L.ctaidOf (g / L.block)).get .z) +
          Lib.softRow (g % L.block) / 6 := by
        unfold Lib.laneKey; omega
      simp [h96f, h97, vis, biased]
    · have h97f : pick97 (w1V ent L g y) = false := by simpa using h97
      have vi := vis_iff (cO := ((g % L.block / 16 % 2 * 64 : Nat) : ℤ))
        (b := (((Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x) * 128 : Nat) : ℤ))
        (P := (Q.past ((L.ctaidOf (g / L.block)).get .z) : ℤ) + (token (g % L.block) : Nat))
        (by omega) (by omega) (by push_cast; omega) (by omega) (by push_cast; omega) hc64
      have vk : vis ((g % L.block / 16 % 2 * 64 : Nat) : ℤ)
          (((Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x) * 128 : Nat) : ℤ)
          ((Q.past ((L.ctaidOf (g / L.block)).get .z) : ℤ) + (token (g % L.block) : Nat)) c =
          decide (Lib.laneKey Q L g y.c.i c ≤ Q.past ((L.ctaidOf (g / L.block)).get .z) +
            Lib.softRow (g % L.block) / 6) := by
        rw [vi]
        refine decide_eq_decide.mpr ?_
        rw [← tk]
        unfold Lib.laneKey
        push_cast
        omega
      simp only [h96f, h97f, Bool.false_eq_true, ite_false, vk, decide_eq_true_eq]
      by_cases hv : Lib.laneKey Q L g y.c.i c ≤ Q.past ((L.ctaidOf (g / L.block)).get .z) +
          Lib.softRow (g % L.block) / 6
      · simp [hv, biased]
      · simp [hv]

  have hq := fin_q (V := w1V ent L g y)
    (by rw [← w1V_canon, (w1V_12 (e := ent) (L := L) (g := g) (d := canon y) rfl).1]
        exact (derV_12 ht).1)
    (by rw [← w1V_canon, (w1V_12 (e := ent) (L := L) (g := g) (d := canon y) rfl).2]
        exact (derV_12 ht).2)
    (by obtain ⟨m1, -⟩ := mi; exact ⟨32, _, m1⟩)
    (by obtain ⟨-, m2, -⟩ := mi; exact ⟨32, _, m2⟩)
    (by
      have n484 : (484 : Nat) ∉ runA.outs := by decide +kernel
      have n484' : (484 : Nat) ∉ runP.outs := by decide +kernel
      rw [vA, V'_notin runA runA_ok _ n484, vP, V'_notin runP runP_ok _ n484',
        ← w1V_canon]
      exact w1V_484 (e := ent) (L := L) (g := g) (d := canon y) rfl)
  refine ⟨W, hvf, fun r h1 h2 => ?_, hq⟩
  obtain ⟨a, b, e, ha, hb⟩ := hpe r h1 h2
  exact ⟨a, b, e, by rwa [heq _ (by omega)] at ha, by rwa [heq _ (by omega)] at hb⟩

/-- **The first window's maximum is exact.** -/
theorem w1_half {m : Mem0} (hp : Pre Q L m) {y : Data.D} (E : EntSp Q L g ent)
    (hP : ent.prior = w32 ((Q.past ((L.ctaidOf (g / L.block)).get .z) : Nat) : ℤ))
    (ht : g % L.block < 256) (hn : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z))
    (hseq : Q.seqK ((L.ctaidOf (g / L.block)).get .z) + 511 < 2 ^ 31)
    (hs : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)))
    (hc : ∀ j < 64, BW (y.v.cur j) (Lib.laneBias Q L g y.c.i j)) :
    Ev (vFin (w1V ent L g y) 1520) (Lib.halfMax Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g)
      y.c.i (g % L.block / 16 % 2)) := by
  obtain ⟨W, hvf, hpe, -⟩ := w1_cols hp E hP ht hn hseq hs hc
  have mx := m_exact hpe
  rw [← congrFun hvf 1520] at mx
  exact mx

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
