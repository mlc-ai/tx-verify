-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftFold

@[expose] public section

/-!
# The kernel works in the unscaled domain

The kernel keeps its scores as `s' = S + bias / scale` and multiplies by `scale_log2 = scale * c`,
so its running maximum is the specification's divided by `scale`. `step` is the same function in
both domains: the step of the scaled state on the scaled blocks (constant `sl`) is the scaled step
of the kernel's state with constant `scale * sl` (`run_scale`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib.SoftFold

open Classical

/-- The state with the maximum multiplied by `c`. -/
noncomputable def scaleSt (c : ℝ) (st : St) : St := ⟨(c : EReal) * st.m, st.l, st.o⟩

/-- The blocks with every score multiplied by `c`. -/
def scaleBlk (c : ℝ) (blk : List (ℝ × ℝ)) : List (ℝ × ℝ) := blk.map fun q => (c * q.1, q.2)

theorem cmul_mono {c : ℝ} (hc : 0 < c) : Monotone (fun x : EReal => (c : EReal) * x) := by
  intro a b h
  induction a using EReal.rec <;> induction b using EReal.rec <;>
    simp [EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_top_of_pos hc] at h ⊢
  norm_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h hc.le

theorem cmul_max {c : ℝ} (hc : 0 < c) (a b : EReal) :
    (c : EReal) * max a b = max ((c : EReal) * a) ((c : EReal) * b) :=
  (cmul_mono hc).map_max

theorem cmul_bot {c : ℝ} (hc : 0 < c) : (c : EReal) * ⊥ = ⊥ := EReal.coe_mul_bot_of_pos hc

theorem cmul_eq_bot {c : ℝ} (hc : 0 < c) (x : EReal) : (c : EReal) * x = ⊥ ↔ x = ⊥ := by
  induction x using EReal.rec <;> simp [EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_top_of_pos hc,
    ← EReal.coe_mul]

theorem blockMax_scale {c : ℝ} (hc : 0 < c) (blk : List (ℝ × ℝ)) :
    blockMax (scaleBlk c blk) = (c : EReal) * blockMax blk := by
  induction blk with
  | nil => simp [scaleBlk, blockMax, cmul_bot hc]
  | cons q t ih =>
    have h : blockMax (scaleBlk c (q :: t)) =
        max ((c * q.1 : ℝ) : EReal) (blockMax (scaleBlk c t)) := rfl
    rw [h, ih]
    change _ = (c : EReal) * max (q.1 : EReal) (blockMax t)
    rw [cmul_max hc, EReal.coe_mul]

theorem mSafe_scale {c : ℝ} (hc : 0 < c) (x : EReal) :
    mSafe ((c : EReal) * x) = c * mSafe x := by
  by_cases h : x = ⊥
  · simp [h, cmul_bot hc, mSafe]
  · have h' : (c : EReal) * x ≠ ⊥ := fun e => h ((cmul_eq_bot hc x).mp e)
    simp only [mSafe, h, h', ite_false]
    induction x using EReal.rec with
    | bot => exact absurd rfl h
    | coe r => rw [← EReal.coe_mul, EReal.toReal_coe, EReal.toReal_coe]
    | top => simp [EReal.coe_mul_top_of_pos hc]

theorem alphaLog2_scale {c sl : ℝ} (hc : 0 < c) (hsl : 0 < sl) (m mn : EReal) :
    alphaLog2 sl ((c : EReal) * m) ((c : EReal) * mn) = alphaLog2 (c * sl) m mn := by
  unfold alphaLog2
  rw [mSafe_scale hc]
  induction m using EReal.rec with
  | bot =>
    rw [cmul_bot hc, EReal.bot_sub, EReal.bot_sub, EReal.bot_mul_coe_of_pos hsl,
      EReal.bot_mul_coe_of_pos (mul_pos hc hsl)]
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul]
    congr 1; ring
  | top =>
    rw [EReal.coe_mul_top_of_pos hc, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.top_mul_coe_of_pos hsl, EReal.top_mul_coe_of_pos (mul_pos hc hsl)]

theorem toReal_cmul {c : ℝ} (hc : 0 < c) (x : EReal) : ((c : EReal) * x).toReal = c * x.toReal := by
  induction x using EReal.rec with
  | bot => simp [cmul_bot hc]
  | coe r => rw [← EReal.coe_mul, EReal.toReal_coe, EReal.toReal_coe]
  | top => simp [EReal.coe_mul_top_of_pos hc]

theorem step_scale {c sl : ℝ} (hc : 0 < c) (hsl : 0 < sl) (blk : List (ℝ × ℝ)) (st : St) :
    step sl (scaleBlk c blk) (scaleSt c st) = scaleSt c (step (c * sl) blk st) := by
  have hm : max ((c : EReal) * st.m) (blockMax (scaleBlk c blk)) =
      (c : EReal) * max st.m (blockMax blk) := by rw [blockMax_scale hc, cmul_max hc]
  have hp : ∀ u : ℝ, (scaleBlk c blk).map (fun q => (2 : ℝ) ^ (sl * q.1 - c * u * sl)) =
      blk.map (fun q => (2 : ℝ) ^ (c * sl * q.1 - u * (c * sl))) := by
    intro u
    simp only [scaleBlk, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp]
    congr 1; ring
  have ho : ∀ u : ℝ, (scaleBlk c blk).map (fun q => (2 : ℝ) ^ (sl * q.1 - c * u * sl) * q.2) =
      blk.map (fun q => (2 : ℝ) ^ (c * sl * q.1 - u * (c * sl)) * q.2) := by
    intro u
    simp only [scaleBlk, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp]
    congr 2; ring
  simp only [step, scaleSt, hm, alphaLog2_scale hc hsl, mSafe_scale hc, toReal_cmul hc]
  split_ifs <;> simp [hp, ho]

theorem run_scale {c sl : ℝ} (hc : 0 < c) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ))) :
    run sl (bs.map (scaleBlk c)) = scaleSt c (run (c * sl) bs) := by
  have h0 : (⟨⊥, 0, 0⟩ : St) = scaleSt c ⟨⊥, 0, 0⟩ := by simp [scaleSt, cmul_bot hc]
  suffices ∀ st, List.foldl (fun st blk => step sl blk st) (scaleSt c st) (bs.map (scaleBlk c)) =
      scaleSt c (List.foldl (fun st blk => step (c * sl) blk st) st bs) by
    unfold run; have := this ⟨⊥, 0, 0⟩; rw [← h0] at this; exact this
  induction bs with
  | nil => intro st; rfl
  | cons b t ih => intro st; simp only [List.map_cons, List.foldl_cons]; rw [step_scale hc hsl, ih]

end PTX.Kernels.InklingRelDecode.Proof.Lib.SoftFold
