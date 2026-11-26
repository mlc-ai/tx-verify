-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Carry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Epi
public import Lemmas.Flow.SetpReads
public import Lemmas.Flow.Recip
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts

@[expose] public section

/-! # The epilogue's row-sum stages against the extended reals

The runs `e1` (the masked maximum and sum: the true maximum `r` is `-inf` where the row has no kept
column), `e3` (the final sum `l + p` with the peer's word `p`), `e5` and `e6`/`e7` (the factor:
zero for a zero sum, else `1 / (sum + 2^(sink - maximum))`), as "reads as" statements on the words
the runs leave in their registers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

theorem w0e_pred_bot {V : Nat → Value} {r : EReal} (hr : Rd (V 2885) r) :
    predOf (e1_v1147 V) = decide (r = ⊥) := by
  unfold e1_v1147
  rw [setpE_reads (.inl rfl) (rd_read hr) readEReal_negInf]
  rfl

theorem w0e_e1 (V : Nat → Value) {r : EReal} {m l : ℝ} (hr : Rd (V 2885) r)
    (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) :
    Rd (lookupD (e1_facts1 V) 481) (w0EMax r m) ∧
      Rd (lookupD (e1_facts1 V) 1727) ((w0ESum r l : ℝ) : EReal) := by
  have hp := w0e_pred_bot hr
  constructor
  · change Rd (e1_v1151 V) _
    unfold e1_v1151 w0EMax
    rw [hp]
    by_cases h : r = ⊥
    · simp only [h, decide_true, ↓reduceIte]
      exact rd_negInf
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hm
  · change Rd (e1_v1150 V) _
    unfold e1_v1150 w0ESum
    rw [hp]
    by_cases h : r = ⊥
    · simp only [h, decide_true, ↓reduceIte]
      exact w0_rd_lI
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hl

/-- **The final sum** (`e3`): the masked sum plus the peer's word. -/
theorem w0e_e3 (V : Nat → Value) {a p : ℝ} (ha : Rd (V 1727) a) (hp : Rd (V 1728) p) :
    Rd (lookupD (e3_facts1 V) 482) ((a + p : ℝ) : EReal) := by
  change Rd (e3_v1158 V) _
  unfold e3_v1158
  rw [addE_reads (rd_read ha) (rd_read hp) (addEReal_coe a p), erealValue_coe]
  exact rd_float _

theorem w0e_pred_zero (W : Nat → Value) {s : ℝ} (hs : Rd (W 482) s) :
    predOf (e5_v1189 W) = decide (s = 0) := by
  unfold e5_v1189
  rw [setpE_reads (.inl rfl) (rd_read hs) (readEReal_of_valFloat valFloat_zero)]
  simp [erealCompare]
  rfl

theorem w0e_fac_core (W : Nat → Value) {s e : ℝ} (hs : Rd (W 482) s)
    (hv : e6_v1193 W = .float .f32 e) (hs0 : 0 ≤ s) (hne : s ≠ 0) (he : 0 ≤ e) :
    Rd (e6_v1196 W) ((1 / (s + e) : ℝ) : EReal) := by
  have h2 : e6_v1194 W = .float .f32 (s + e) := by
    unfold e6_v1194
    rw [hv, addE_reads (rd_read hs) (readEReal_float e) (addEReal_coe s e), erealValue_coe]
    rfl
  have hpos : s + e ≠ 0 := by
    have : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hne)
    positivity
  have e1 : fF (approxE (divI true)) [.reg 1744, .reg 1743] [e6_v1195 W, e6_v1194 W] =
      approxE (divI true) [e6_v1195 W, e6_v1194 W] := by
    simp [fF, fOpnd, lk, regsOf, regOf, List.lookup]
  have hd : approxE (divI true) [e6_v1195 W, e6_v1194 W] = .ok (.float .f32 (1 / (s + e))) :=
    approxE_div_fin valFloat_one (by rw [h2]; simp [valFloat, pure, Except.pure]) hpos
  unfold e6_v1196
  rw [e1, hd]
  exact rd_float _

theorem w0e_e6_ex2 (W : Nat → Value) {m : ℝ} {sk : EReal} (hm : Rd (W 481) m)
    (hk : Rd (W 2880) sk) : e6_v1193 W = .float .f32 (w0Sk2 sk m) := by
  unfold e6_v1193 e6_v1192
  rcases rd_lane hk with ⟨k, rfl⟩ | rfl
  · rw [subE_reads (z := ((k + -m : ℝ) : EReal)) (rd_read hk) (rd_read hm)
      (by rw [← EReal.coe_neg]; exact addEReal_coe k (-m))]
    simp only [okVal, erealValue_coe]
    rw [ex2E_real (readEReal_float _)]
    simp [w0Sk2, sub_eq_add_neg]
  · rw [subE_reads (z := ⊥) (rd_read hk) (rd_read hm) (by simp [addEReal])]
    simp only [okVal, erealValue_bot]
    rw [ex2E_negInf]
    simp [w0Sk2]

theorem w0e_e6 (W : Nat → Value) {s m : ℝ} {sk : EReal} (hs : Rd (W 482) s) (hm : Rd (W 481) m)
    (hk : Rd (W 2880) sk) (hs0 : 0 ≤ s) (hne : s ≠ 0) :
    Rd (e6_v1196 W) (((1 / (s + w0Sk2 sk m) : ℝ)) : EReal) :=
  w0e_fac_core W hs (w0e_e6_ex2 W hm hk) hs0 hne (by
    unfold w0Sk2; split_ifs <;> positivity)

/-- **The zero-sum test and the factor** (`e5`, `e6`): zero for a zero sum, else the quotient. -/
theorem w0e_zj (W : Nat → Value) {s m : ℝ} {sk : EReal} (hs : Rd (W 482) s)
    (hm : s ≠ 0 → Rd (W 481) m) (hk : Rd (W 2880) sk) (hs0 : 0 ≤ s) :
    Rd (if predOf (e5_v1189 W) then e5_v1190 W else e6_v1196 W) ((w0Fac s sk m : ℝ) : EReal) := by
  rw [w0e_pred_zero W hs]
  by_cases h : s = 0
  · have h0 : e5_v1190 W = lI := rfl
    simp only [h, decide_true, ↓reduceIte, w0Fac]
    exact w0_rd_lI
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, w0Fac]
    exact w0e_e6 W hs (hm h) hk hs0 h

/-- **The factor pair** (`e7`): the pair register `%rd588` holds the factor twice. -/
theorem w0e_e7 (V : Nat → Value) {f : ℝ} (hf : Rd (V 2956) f) :
    pairRead (lookupD (e7_facts1 V) 3577) = some (.ok ((f : EReal), (f : EReal))) :=
  pairRead_join hf hf

/-- **The factor pair of the epilogue** from the loop's end values (`e1`, `e3`, `e5`-`e7`): with
the maximum `r`, the carried statistics `m`, `l`, the sink word `sk` and the peer's word `p`, the
pair register holds `w0Fac (w0ESum r l + p) sk m` twice. A row without a kept column has no peer
sum (`r = -inf` needs `p = 0`). -/
theorem w0e_fac (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ} {sk : EReal}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hk : Rd (V 2880) sk)
    (hp : Rd pe p) (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) (hrp : r = ⊥ → p = 0) :
    pairRead (lookupD (f_fac V pe) 3577) =
      some (.ok ((w0Fac (w0ESum r l + p) sk m : ℝ), (w0Fac (w0ESum r l + p) sk m : ℝ))) := by
  obtain ⟨h481, h1727⟩ := w0e_e1 V hr hm hl
  have h0 : 0 ≤ w0ESum r l := by unfold w0ESum; split_ifs <;> first | exact le_rfl | exact hl0
  have h482 : Rd (lookupD (f_ew V pe) 482) ((w0ESum r l + p : ℝ) : EReal) :=
    w0e_e3 (f_ex1 V pe) (a := w0ESum r l) h1727 hp
  have hz : Rd (lookupD (f_ew V pe) 2880) sk := hk
  have hzj : Rd (f_zj V pe) ((w0Fac (w0ESum r l + p) sk m : ℝ) : EReal) := by
    refine w0e_zj (lookupD (f_ew V pe)) h482 (fun hne => ?_) hz (by positivity)
    have hr' : r ≠ ⊥ := fun h => hne (by simp [w0ESum, h, hrp h])
    have h481' : Rd (lookupD (f_ew V pe) 481) (w0EMax r m) := h481
    simpa [w0EMax, hr'] using h481'
  exact w0e_e7 _ (f := w0Fac (w0ESum r l + p) sk m) hzj

theorem f32Value_ln2 : f32Value 1060205080 = some (1453635 / 2097152) := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  norm_num

theorem valFloat_ln2 :
    valFloat .f32 (.bits 32 (BitVec.ofNat 64 1060205080)) = .ok lseLog2Factor := by
  have := valFloat_b32 (b := 1060205080) (by norm_num) f32Value_ln2
  simpa [b32, lseLog2Factor] using this

theorem w0e_v1163 (W : Nat → Value) {s : ℝ} (hs : W 482 = .float .f32 s) (h0 : 0 < s) :
    e4_v1163 W = .float .f32 (Real.log s / Real.log 2 * lseLog2Factor) := by
  have h1 : e4_v1162 W = .float .f32 (Real.log s / Real.log 2) := by
    unfold e4_v1162
    simp [lg2E, hs, valFloat, pure, Except.pure, Except.toOption, h0, okVal]
  have e1 : fF (mulL true) [.reg 1730, .f32imm 1060205080] [e4_v1162 W] =
      mulE true (e4_v1162 W) (.bits 32 (BitVec.ofNat 64 1060205080)) := by
    simp [fF, fOpnd, lk, regsOf, regOf, mulL]
  unfold e4_v1163
  rw [e1, h1, mulE_reads (readEReal_float _) (readEReal_of_valFloat valFloat_ln2)
    (mulEReal_coe _ _), erealValue_coe]
  rfl

theorem w0e_v1164 (W : Nat → Value) {s : ℝ} {M : EReal} (hs : W 482 = .float .f32 s)
    (hM : Rd (W 481) M) (h0 : 0 < s) :
    e4_v1164 W = erealValue .f32 (M * (lseLog2Factor : EReal) +
      ((Real.log s / Real.log 2 * lseLog2Factor : ℝ) : EReal)) := by
  have hc := readEReal_of_valFloat valFloat_ln2
  have e1 : fF (floatE (fmaI .rn true)) [.reg 481, .f32imm 1060205080, .reg 1731]
      [W 481, e4_v1163 W] =
      floatE (fmaI .rn true) [W 481, .bits 32 (BitVec.ofNat 64 1060205080), e4_v1163 W] := by
    simp [fF, fOpnd, lk, regsOf, regOf, List.lookup]
  have hpos : (0 : ℝ) < lseLog2Factor := by unfold lseLog2Factor; norm_num
  unfold e4_v1164
  rw [e1, w0e_v1163 W hs h0]
  have hw : (mulEReal M (lseLog2Factor : EReal)).bind (addEReal · ((Real.log s / Real.log 2 *
      lseLog2Factor : ℝ) : EReal)) = some (M * (lseLog2Factor : EReal) +
      ((Real.log s / Real.log 2 * lseLog2Factor : ℝ) : EReal)) := by
    rcases rd_lane hM with ⟨m, rfl⟩ | rfl
    · rw [mulEReal_coe]; simp only [Option.bind_some]
      rw [addEReal_coe]; rfl
    · rw [mulEReal_bot_pos hpos, Option.bind_some, addEReal_bot_coe,
        EReal.bot_mul_of_pos (by exact_mod_cast hpos), EReal.bot_add]
  rw [fmaE_reads (rd_read hM) hc (readEReal_float _) hw]
  rfl

theorem w0e_e4_pos (W : Nat → Value) {s : ℝ} {M : EReal} (hs : W 482 = .float .f32 s)
    (hM : Rd (W 481) M) (hp : 0 < s) : e4_v1166 W = w0LseV s M := by
  have h4 := w0e_v1164 W hs hM hp
  have hpos : (0 : ℝ) < lseLog2Factor := by unfold lseLog2Factor; norm_num
  have hs0 : ¬ s = 0 := hp.ne'
  unfold e4_v1166 e4_v1165
  rw [h4]
  rcases rd_lane hM with ⟨m, rfl⟩ | rfl
  · have hz : (m : EReal) * (lseLog2Factor : EReal) + ((Real.log s / Real.log 2 *
        lseLog2Factor : ℝ) : EReal) = ((m * lseLog2Factor + Real.log s / Real.log 2 *
        lseLog2Factor : ℝ) : EReal) := by push_cast; rfl
    have hcmp : erealCompare .eq ((m * lseLog2Factor + Real.log s / Real.log 2 *
        lseLog2Factor : ℝ) : EReal) ⊥ = false := decide_eq_false (EReal.coe_ne_bot _)
    rw [hz, erealValue_coe, setpE_reads (.inl rfl) (readEReal_float _) readEReal_negInf, hcmp]
    simp only [okPred, predOf, Bool.false_eq_true, ↓reduceIte]
    simp [w0LseV, hs0]
  · rw [EReal.bot_mul_of_pos (by exact_mod_cast hpos), EReal.bot_add, erealValue_bot,
      setpE_reads (.inl rfl) readEReal_negInf readEReal_negInf]
    simp [w0LseV, erealCompare, okPred, predOf, opndVal]

theorem w0e_lg2_zero : lg2E [.float .f32 0] = .ok negInf32 := by
  have hv : (valFloat .f32 (.float .f32 0)).toOption = some 0 := by
    simp [valFloat, pure, Except.pure, Except.toOption]
  unfold lg2E
  simp only [hv, lt_self_iff_false, ite_false]
  exact coreFloat_lg2_zero true

/-- The zero sum's chain (`e4`): `lg2` of zero, its scaling and the maximum's fma are `-inf`. -/
theorem w0e_zero_v1162 (W : Nat → Value) (hs : W 482 = .float .f32 0) :
    e4_v1162 W = negInf32 := by
  unfold e4_v1162
  rw [hs, w0e_lg2_zero]
  rfl

theorem w0e_zero_v1163 (W : Nat → Value) (hs : W 482 = .float .f32 0) :
    e4_v1163 W = negInf32 := by
  have hpos : (0 : ℝ) < lseLog2Factor := by unfold lseLog2Factor; norm_num
  have e1 : fF (mulL true) [.reg 1730, .f32imm 1060205080] [e4_v1162 W] =
      mulE true (e4_v1162 W) (.bits 32 (BitVec.ofNat 64 1060205080)) := by
    simp [fF, fOpnd, lk, regsOf, regOf, mulL]
  unfold e4_v1163
  rw [e1, w0e_zero_v1162 W hs, mulE_reads (z := ⊥) readEReal_negInf
    (readEReal_of_valFloat valFloat_ln2) (mulEReal_bot_pos hpos)]
  rfl

theorem w0e_zero_v1164 (W : Nat → Value) {M : EReal} (hs : W 482 = .float .f32 0)
    (hM : Rd (W 481) M) : e4_v1164 W = negInf32 := by
  have hpos : (0 : ℝ) < lseLog2Factor := by unfold lseLog2Factor; norm_num
  have e2 : fF (floatE (fmaI .rn true)) [.reg 481, .f32imm 1060205080, .reg 1731]
      [W 481, e4_v1163 W] =
      floatE (fmaI .rn true) [W 481, .bits 32 (BitVec.ofNat 64 1060205080), e4_v1163 W] := by
    simp [fF, fOpnd, lk, regsOf, regOf, List.lookup]
  unfold e4_v1164
  rw [e2, w0e_zero_v1163 W hs, fmaE_reads (z := ⊥) (rd_read hM)
    (readEReal_of_valFloat valFloat_ln2) readEReal_negInf (w := ⊥) ?_]
  · rw [erealValue_bot]; rfl
  · rcases rd_lane hM with ⟨m, rfl⟩ | rfl
    · rw [mulEReal_coe, Option.bind_some]
      unfold addEReal
      split_ifs with h
      · rcases h with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (EReal.coe_ne_top _)
        · exact absurd h (by simp)
      · simp
    · rw [mulEReal_bot_pos hpos]; simp [addEReal]

theorem w0e_e4_zero (W : Nat → Value) {M : EReal} (hs : W 482 = .float .f32 0)
    (hM : Rd (W 481) M) : e4_v1166 W = w0LseV 0 M := by
  have h4 := w0e_zero_v1164 W hs hM
  unfold e4_v1166 e4_v1165
  rw [h4, setpE_reads (.inl rfl) readEReal_negInf readEReal_negInf]
  simp [w0LseV, erealCompare, okPred, predOf, opndVal]

theorem w0e_e4 (W : Nat → Value) {s : ℝ} {M : EReal} (hs : W 482 = .float .f32 s)
    (hM : Rd (W 481) M) (h0 : 0 ≤ s) : lookupD (e4_facts1 W) 1733 = w0LseV s M := by
  rcases h0.lt_or_eq with hp | hz
  · exact w0e_e4_pos W hs hM hp
  · subst hz; exact w0e_e4_zero W hs hM

theorem w0e_e3_eq (V : Nat → Value) {a p : ℝ} (ha : Rd (V 1727) a) (hp : Rd (V 1728) p) :
    lookupD (e3_facts1 V) 482 = .float .f32 (a + p) := by
  change e3_v1158 V = _
  unfold e3_v1158
  rw [addE_reads (rd_read ha) (rd_read hp) (addEReal_coe a p), erealValue_coe]
  rfl

/-- **The LSE word of the epilogue** from the loop's end values (`e1`, `e3`, `e4`). -/
theorem w0e_lse (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hp : Rd pe p)
    (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) :
    lookupD (f_lse V pe) 1733 = w0LseV (w0ESum r l + p) (w0EMax r m) := by
  obtain ⟨h481, h1727⟩ := w0e_e1 V hr hm hl
  have h0 : 0 ≤ w0ESum r l := by unfold w0ESum; split_ifs <;> first | exact le_rfl | exact hl0
  have h482 : lookupD (f_ew V pe) 482 = .float .f32 (w0ESum r l + p) :=
    w0e_e3_eq (f_ex1 V pe) (a := w0ESum r l) h1727 hp
  have h481' : Rd (lookupD (f_ew V pe) 481) (w0EMax r m) := h481
  exact w0e_e4 (lookupD (f_ew V pe)) h482 h481' (by positivity)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
