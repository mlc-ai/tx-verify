-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
The online softmax of the Inkling 2 relative-attention decode kernel computes the plain softmax.

The per-row update is `_verify_softmax` of vLLM `vllm/models/inkling2/ops/attention.py:790-799`.
The state `(m, l, o)` is the running maximum (an `EReal`, `-∞` before the first visible key), the
running denominator and one output dimension of the running numerator, all stored relative to `m`.
A block is the list of its visible keys `(score, value)`; masked keys have weight `0` and are
absent.  The rescale of the old state by `alpha` is skipped (lazy rescaling) while
`alpha_log2 ≥ -8`.

The theorems below show, by induction over the blocks, that after any list of blocks the state is
the plain softmax sums relative to some real `M`:
`l = Σ 2^(sl (s - M))` and `o = Σ 2^(sl (s - M)) v`, so the normalized output `o / l` and the
log2-sum-exp `m * sl + log2 l` equal the ones stated for the plain weights `2^(sl s)`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib.SoftFold

open Classical

/-- The running state of one row: `m` (row max, `-∞` initially), `l` (denominator), `o` (one
output dimension of the numerator). -/
structure St where
  m : EReal
  l : ℝ
  o : ℝ

/-- The maximum of the scores of a block, `-∞` for an empty block
(`m_new = max(m, tl.max(s, 1))`, source line 790). -/
noncomputable def blockMax (blk : List (ℝ × ℝ)) : EReal :=
  blk.foldr (fun p acc => max (p.1 : EReal) acc) ⊥

/-- `m_safe = tl.where(m_new == -inf, 0, m_new)` (source line 791). -/
noncomputable def mSafe (mNew : EReal) : ℝ := if mNew = ⊥ then 0 else mNew.toReal

/-- `alpha_log2 = (m - m_safe) * scale_log2` in `EReal` (source line 792); `m = -∞` gives `-∞`. -/
noncomputable def alphaLog2 (sl : ℝ) (m mNew : EReal) : EReal :=
  (m - (mSafe mNew : EReal)) * (sl : EReal)

/-- The lazy-rescale test `alpha_log2 >= -8` (source line 793). -/
def Keep (a : EReal) : Prop := ((-8 : ℝ) : EReal) ≤ a

/-- `2 ^ alpha_log2` with `2 ^ (-∞) = 0`, for `alpha_log2 < -8` (so never `+∞`). -/
noncomputable def pow2 (a : EReal) : ℝ := if a = ⊥ then 0 else (2 : ℝ) ^ a.toReal

/-- One block of the kernel's online softmax (source lines 790-799).

* `alpha = 1` if `keep` else `2 ^ alpha_log2` (line 794);
* `m_use = m` if `keep` else `m_safe` (line 795); when `keep`, `m` is finite, so `m.toReal` is `m`;
* `m' = m` if `keep` else `m_new` (line 796);
* `x_k = scale_log2 * s_k - m_use * scale_log2`, `p_k = 2 ^ x_k` (line 797);
* `l' = l * alpha + Σ p_k`, `o' = o * alpha + Σ p_k v_k` (lines 798-799). -/
noncomputable def step (sl : ℝ) (blk : List (ℝ × ℝ)) (st : St) : St :=
  let mNew : EReal := max st.m (blockMax blk)
  let a : EReal := alphaLog2 sl st.m mNew
  let alpha : ℝ := if Keep a then 1 else pow2 a
  let mUse : ℝ := if Keep a then st.m.toReal else mSafe mNew
  let p : (ℝ × ℝ) → ℝ := fun q => (2 : ℝ) ^ (sl * q.1 - mUse * sl)
  { m := if Keep a then st.m else mNew
    l := st.l * alpha + (blk.map p).sum
    o := st.o * alpha + (blk.map fun q => p q * q.2).sum }

/-- The state after a list of blocks. -/
noncomputable def run (sl : ℝ) (bs : List (List (ℝ × ℝ))) : St :=
  bs.foldl (fun st blk => step sl blk st) ⟨⊥, 0, 0⟩

/-- The plain softmax weight `2 ^ (scale_log2 * s)`. -/
noncomputable def W (sl s : ℝ) : ℝ := (2 : ℝ) ^ (sl * s)

/-- The denominator relative to `M`: `Σ 2^(sl (s - M))`. -/
noncomputable def lsum (sl M : ℝ) (A : List (ℝ × ℝ)) : ℝ :=
  (A.map fun q => (2 : ℝ) ^ (sl * (q.1 - M))).sum

/-- The numerator relative to `M`: `Σ 2^(sl (s - M)) v`. -/
noncomputable def osum (sl M : ℝ) (A : List (ℝ × ℝ)) : ℝ :=
  (A.map fun q => (2 : ℝ) ^ (sl * (q.1 - M)) * q.2).sum

/-- The invariant after the keys `A` have been processed. -/
def Inv (sl : ℝ) (A : List (ℝ × ℝ)) (st : St) : Prop :=
  (A = [] → st = ⟨⊥, 0, 0⟩) ∧
  (A ≠ [] → ∃ M : ℝ, st.m = (M : EReal) ∧ st.l = lsum sl M A ∧ st.o = osum sl M A ∧
    ∀ q ∈ A, q.1 ≤ M + 8 / sl)

theorem blockMax_nil : blockMax [] = ⊥ := rfl

theorem blockMax_real :
    ∀ blk : List (ℝ × ℝ), blk ≠ [] → ∃ b : ℝ, blockMax blk = (b : EReal) ∧ ∀ q ∈ blk, q.1 ≤ b
  | [], h => absurd rfl h
  | q :: t, _ => by
    rcases eq_or_ne t [] with rfl | ht
    · refine ⟨q.1, ?_, by simp⟩
      simp [blockMax]
    · obtain ⟨b, hb, hle⟩ := blockMax_real t ht
      refine ⟨max q.1 b, ?_, ?_⟩
      · have : blockMax (q :: t) = max (q.1 : EReal) (blockMax t) := rfl
        rw [this, hb]
        norm_cast
      · intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact le_max_left _ _
        · exact (hle r hr).trans (le_max_right _ _)


theorem mSafe_coe (x : ℝ) : mSafe (x : EReal) = x := by
  simp [mSafe]

theorem mSafe_bot : mSafe ⊥ = 0 := by
  simp [mSafe]

theorem not_keep_bot : ¬ Keep ⊥ := by
  simp [Keep]

theorem keep_coe_iff (x : ℝ) : Keep (x : EReal) ↔ -8 ≤ x := by
  simp only [Keep]
  exact EReal.coe_le_coe_iff

theorem step_nil_bot (sl : ℝ) (hsl : 0 < sl) : step sl [] ⟨⊥, 0, 0⟩ = ⟨⊥, 0, 0⟩ := by
  have ha : alphaLog2 sl ⊥ (max ⊥ (blockMax [])) = ⊥ := by
    simp [alphaLog2, blockMax_nil, mSafe_bot, EReal.bot_mul_coe_of_pos hsl]
  simp [step, blockMax_nil, mSafe_bot, pow2]

theorem step_nil_coe (sl : ℝ) (M l o : ℝ) :
    step sl [] ⟨(M : EReal), l, o⟩ = ⟨(M : EReal), l, o⟩ := by
  have hm : max (M : EReal) (blockMax []) = (M : EReal) := by
    simp [blockMax_nil]
  have ha : alphaLog2 sl (M : EReal) (max (M : EReal) (blockMax [])) = ((0 : ℝ) : EReal) := by
    simp [alphaLog2, hm, mSafe_coe]
  have hk : Keep (alphaLog2 sl (M : EReal) (max (M : EReal) (blockMax []))) := by
    rw [ha, keep_coe_iff]; norm_num
  simp [step, hk]


theorem alphaLog2_coe_coe (sl M M2 : ℝ) :
    alphaLog2 sl (M : EReal) (M2 : EReal) = (((M - M2) * sl : ℝ) : EReal) := by
  rw [alphaLog2, mSafe_coe]
  norm_cast

/-- The exponent of the rescale factor of a finite state against a block with maximum `b`. -/
theorem alphaLog2_coe (sl M b : ℝ) {blk : List (ℝ × ℝ)} (hb : blockMax blk = (b : EReal)) :
    alphaLog2 sl (M : EReal) (max (M : EReal) (blockMax blk)) =
      (((M - max M b) * sl : ℝ) : EReal) := by
  have hm : max (M : EReal) (blockMax blk) = ((max M b : ℝ) : EReal) := by
    rw [hb]; norm_cast
  rw [alphaLog2, hm, mSafe_coe]
  norm_cast

theorem pow2_coe (x : ℝ) : pow2 (x : EReal) = (2 : ℝ) ^ x := by
  simp [pow2]

theorem step_keep (sl M b l o : ℝ) {blk : List (ℝ × ℝ)} (hb : blockMax blk = (b : EReal))
    (hk : -8 ≤ (M - max M b) * sl) :
    step sl blk ⟨(M : EReal), l, o⟩ =
      ⟨(M : EReal), l + (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - M * sl)).sum,
        o + (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - M * sl) * q.2).sum⟩ := by
  have hk' : Keep (((M - max M b) * sl : ℝ) : EReal) := (keep_coe_iff _).2 hk
  simp only [step, alphaLog2_coe sl M b hb, hk', ite_true, EReal.toReal_coe, mul_one]

theorem step_nokeep (sl M b l o : ℝ) {blk : List (ℝ × ℝ)} (hb : blockMax blk = (b : EReal))
    (hk : ¬ -8 ≤ (M - max M b) * sl) :
    step sl blk ⟨(M : EReal), l, o⟩ =
      ⟨((max M b : ℝ) : EReal),
        l * (2 : ℝ) ^ ((M - max M b) * sl) +
          (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - max M b * sl)).sum,
        o * (2 : ℝ) ^ ((M - max M b) * sl) +
          (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - max M b * sl) * q.2).sum⟩ := by
  have hm : max (M : EReal) (blockMax blk) = ((max M b : ℝ) : EReal) := by
    rw [hb]; norm_cast
  have hk' : ¬ Keep (((M - max M b) * sl : ℝ) : EReal) := fun h => hk ((keep_coe_iff _).1 h)
  simp only [step, hm, alphaLog2_coe_coe, hk', ite_false, pow2_coe, mSafe_coe]

theorem step_bot (sl b l o : ℝ) (hsl : 0 < sl) {blk : List (ℝ × ℝ)}
    (hb : blockMax blk = (b : EReal)) :
    step sl blk ⟨⊥, l, o⟩ =
      ⟨(b : EReal), (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - b * sl)).sum,
        (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - b * sl) * q.2).sum⟩ := by
  have hm : max (⊥ : EReal) (blockMax blk) = (b : EReal) := by
    rw [hb]; exact max_eq_right bot_le
  have ha : alphaLog2 sl ⊥ (b : EReal) = ⊥ := by
    simp [alphaLog2, mSafe_coe, EReal.bot_mul_coe_of_pos hsl]
  simp only [step, hm, ha, not_keep_bot, ite_false, mSafe_coe, pow2, ite_true, mul_zero, zero_add]


theorem lsum_eq (sl M : ℝ) (blk : List (ℝ × ℝ)) :
    lsum sl M blk = (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - M * sl)).sum := by
  unfold lsum
  congr 1
  apply List.map_congr_left
  intro q _
  congr 1
  ring

theorem osum_eq (sl M : ℝ) (blk : List (ℝ × ℝ)) :
    osum sl M blk = (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - M * sl) * q.2).sum := by
  unfold osum
  congr 1
  apply List.map_congr_left
  intro q _
  congr 1
  congr 1
  ring

theorem lsum_append (sl M : ℝ) (A B : List (ℝ × ℝ)) :
    lsum sl M (A ++ B) = lsum sl M A + lsum sl M B := by
  simp [lsum, List.sum_append]

theorem osum_append (sl M : ℝ) (A B : List (ℝ × ℝ)) :
    osum sl M (A ++ B) = osum sl M A + osum sl M B := by
  simp [osum, List.sum_append]

theorem rpow_rescale (sl M M2 s : ℝ) :
    (2 : ℝ) ^ (sl * (s - M2)) = (2 : ℝ) ^ (sl * (s - M)) * (2 : ℝ) ^ ((M - M2) * sl) := by
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- Moving the reference point from `M` to `M2` multiplies the denominator by `2^((M-M2) sl)`. -/
theorem lsum_rescale (sl M M2 : ℝ) (A : List (ℝ × ℝ)) :
    lsum sl M2 A = lsum sl M A * (2 : ℝ) ^ ((M - M2) * sl) := by
  unfold lsum
  rw [← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro q _
  exact rpow_rescale ..

theorem osum_rescale (sl M M2 : ℝ) (A : List (ℝ × ℝ)) :
    osum sl M2 A = osum sl M A * (2 : ℝ) ^ ((M - M2) * sl) := by
  unfold osum
  rw [← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [rpow_rescale sl M M2 q.1]
  ring

theorem step_empty (sl : ℝ) (hsl : 0 < sl) {A : List (ℝ × ℝ)} {st : St} (h : Inv sl A st) :
    step sl [] st = st := by
  by_cases hA : A = []
  · rw [h.1 hA]
    exact step_nil_bot sl hsl
  · obtain ⟨M, hm, hl, ho, -⟩ := h.2 hA
    obtain ⟨m, l, o⟩ := st
    dsimp only at hm
    subst hm
    exact step_nil_coe sl M l o

theorem step_inv (sl : ℝ) (hsl : 0 < sl) {A : List (ℝ × ℝ)} {st : St} (h : Inv sl A st)
    (blk : List (ℝ × ℝ)) : Inv sl (A ++ blk) (step sl blk st) := by
  rcases eq_or_ne blk [] with rfl | hbl
  · rw [step_empty sl hsl h, List.append_nil]
    exact h
  obtain ⟨b, hb, hle⟩ := blockMax_real blk hbl
  have hpos : 0 < 8 / sl := by positivity
  by_cases hA : A = []
  · subst hA
    rw [h.1 rfl, step_bot sl b 0 0 hsl hb, List.nil_append]
    refine ⟨fun h => absurd h hbl, fun _ => ⟨b, rfl, (lsum_eq ..).symm, (osum_eq ..).symm, ?_⟩⟩
    intro q hq
    linarith [hle q hq]
  obtain ⟨M, hm, hl, ho, hbd⟩ := h.2 hA
  obtain ⟨m, l, o⟩ := st
  dsimp only at hm hl ho
  subst hm hl ho
  have hne : A ++ blk ≠ [] := by simp [hbl]
  by_cases hk : -8 ≤ (M - max M b) * sl
  · rw [step_keep sl M b _ _ hb hk]
    refine ⟨fun h => absurd h hne, fun _ => ⟨M, rfl, ?_, ?_, ?_⟩⟩
    · rw [lsum_append, lsum_eq sl M blk]
    · rw [osum_append, osum_eq sl M blk]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hbd q hq
      · have h1 : (max M b - M) * sl ≤ 8 := by nlinarith
        have h2 : max M b - M ≤ 8 / sl := (le_div_iff₀ hsl).2 h1
        linarith [hle q hq, le_max_right M b]
  · rw [step_nokeep sl M b _ _ hb hk]
    refine ⟨fun h => absurd h hne, fun _ => ⟨max M b, rfl, ?_, ?_, ?_⟩⟩
    · rw [lsum_append, lsum_rescale sl M (max M b), lsum_eq sl (max M b) blk]
    · rw [osum_append, osum_rescale sl M (max M b), osum_eq sl (max M b) blk]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · linarith [hbd q hq, le_max_left M b]
      · linarith [hle q hq, le_max_right M b]

/-- The invariant holds after every list of blocks. -/
theorem foldl_inv (sl : ℝ) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ))) :
    ∀ (A : List (ℝ × ℝ)) (st : St), Inv sl A st →
      Inv sl (A ++ bs.flatten) (bs.foldl (fun st blk => step sl blk st) st) := by
  induction bs with
  | nil => intro A st h; simpa using h
  | cons blk bs ih =>
    intro A st h
    have := ih (A ++ blk) _ (step_inv sl hsl h blk)
    simpa [List.append_assoc] using this

theorem run_inv (sl : ℝ) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ))) :
    Inv sl bs.flatten (run sl bs) := by
  have := foldl_inv sl hsl bs [] ⟨⊥, 0, 0⟩ ⟨fun _ => rfl, fun h => absurd rfl h⟩
  simpa [run] using this


/-- With no visible key the state is the initial one. -/
theorem fold_empty (sl : ℝ) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ))) (h : bs.flatten = []) :
    (run sl bs).l = 0 ∧ (run sl bs).o = 0 ∧ (run sl bs).m = ⊥ := by
  have := (run_inv sl hsl bs).1 h
  rw [this]
  exact ⟨rfl, rfl, rfl⟩

/-- After the blocks `bs` the state is the plain softmax sums relative to a finite `M`, which is
within `8 / sl` of the largest score (lazy rescaling). -/
theorem fold_invariant (sl : ℝ) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ)))
    (h : bs.flatten ≠ []) :
    ∃ M : ℝ, (run sl bs).m = (M : EReal) ∧
      (run sl bs).l = (bs.flatten.map fun q => (2 : ℝ) ^ (sl * (q.1 - M))).sum ∧
      (run sl bs).o = (bs.flatten.map fun q => (2 : ℝ) ^ (sl * (q.1 - M)) * q.2).sum ∧
      ∀ q ∈ bs.flatten, q.1 ≤ M + 8 / sl :=
  (run_inv sl hsl bs).2 h

theorem lsum_eq_div (sl M : ℝ) (A : List (ℝ × ℝ)) :
    lsum sl M A = (A.map fun q => W sl q.1).sum / (2 : ℝ) ^ (sl * M) := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  unfold lsum
  congr 1
  apply List.map_congr_left
  intro q _
  rw [W, mul_sub, Real.rpow_sub (by norm_num), div_eq_mul_inv]

theorem osum_eq_div (sl M : ℝ) (A : List (ℝ × ℝ)) :
    osum sl M A = (A.map fun q => W sl q.1 * q.2).sum / (2 : ℝ) ^ (sl * M) := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  unfold osum
  congr 1
  apply List.map_congr_left
  intro q _
  rw [W, mul_sub, Real.rpow_sub (by norm_num), div_eq_mul_inv]
  ring

theorem sumW_pos (sl : ℝ) {A : List (ℝ × ℝ)} (h : A ≠ []) :
    0 < (A.map fun q => W sl q.1).sum := by
  apply List.sum_pos
  · intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
    exact Real.rpow_pos_of_pos (by norm_num) _
  · simpa using h

/-- The normalized output `o / l` is the plain softmax-weighted average, and `l > 0`. -/
theorem fold_normalized (sl : ℝ) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ)))
    (h : bs.flatten ≠ []) :
    (run sl bs).o / (run sl bs).l =
        (bs.flatten.map fun q => W sl q.1 * q.2).sum / (bs.flatten.map fun q => W sl q.1).sum ∧
      0 < (run sl bs).l := by
  obtain ⟨M, -, hl, ho, -⟩ := fold_invariant sl hsl bs h
  have hl' : (run sl bs).l = lsum sl M bs.flatten := hl
  have ho' : (run sl bs).o = osum sl M bs.flatten := ho
  have hc : 0 < (2 : ℝ) ^ (sl * M) := Real.rpow_pos_of_pos (by norm_num) _
  have hS := sumW_pos sl h
  refine ⟨?_, ?_⟩
  · rw [hl', ho', lsum_eq_div, osum_eq_div]
    exact div_div_div_cancel_right₀ hc.ne' _ _
  · rw [hl', lsum_eq_div]
    exact div_pos hS hc

/-- The log2-sum-exp `m * sl + log2 l` is the one of the plain weights. -/
theorem fold_lse (sl : ℝ) (hsl : 0 < sl) (bs : List (List (ℝ × ℝ))) (h : bs.flatten ≠ []) :
    ((run sl bs).m).toReal * sl + Real.logb 2 (run sl bs).l =
      Real.logb 2 (bs.flatten.map fun q => W sl q.1).sum := by
  obtain ⟨M, hm, hl, -, -⟩ := fold_invariant sl hsl bs h
  have hl' : (run sl bs).l = lsum sl M bs.flatten := hl
  have hc : 0 < (2 : ℝ) ^ (sl * M) := Real.rpow_pos_of_pos (by norm_num) _
  have hS := sumW_pos sl h
  rw [hm, hl', lsum_eq_div, Real.logb_div hS.ne' hc.ne', Real.logb_rpow (by norm_num)
    (by norm_num), EReal.toReal_coe]
  ring

end PTX.Kernels.InklingRelDecode.Proof.Lib.SoftFold
