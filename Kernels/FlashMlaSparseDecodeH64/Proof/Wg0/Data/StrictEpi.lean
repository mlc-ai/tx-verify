-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumEpi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictLib2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Rescale0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Sink
public import Lemmas.Flow.Mul2NVal

@[expose] public section

/-! # Conditions of the epilogue's small runs

The conditions of the runs `e1`, `e3`, `e5`, `e7` (statistics, sums, the factor pair), the
rescale factor `alpha` and the sink word `sk`: no item's outcome is a fault when the words they
read are numbers (`Rd`), the integer words have their widths, and the sum is a real. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

/-- A move of an immediate to a 32-bit register is no fault. -/
theorem c_movImm {op : Op} {d k : Nat}
    (hop : op = .move ⟨.scalar, .int .b 32, [some d], [.imm k]⟩) :
    ∃ v, coreF op [] [] = .ok v := by
  subst hop
  exact ⟨Value.bits 32 (truncBits 32 (BitVec.ofNat 64 k)), by
    simp [coreF, coreW, oVal, oBits, DType.width, Value.bytes]; rfl⟩

theorem e1_cvt {y : Nat} {x : Value} (hx : x = .bits 16 (BitVec.ofNat 64 y)) :
    coreF e1_op1148 [452] [x] = .ok (.bits 32 (BitVec.ofNat 64 (y % 65536 % 4294967296))) := by
  subst hx
  simp [e1_op1148, coreF, coreW, lk, cvtW, oVal, oBits, truncBits, DType.width, pure,
    Except.pure, bind, Except.bind]

theorem c_selpF {W : Nat → Value} {p k r : Nat} (hv : (W r).bytes = 4) :
    (if predOf (W p) then opndVal W (.f32imm k) else opndVal W (.reg r)).bytes = 4 := by
  split <;> simp [opndVal, hv, Value.bytes]

theorem e1_cond_of_reads (V : Nat → Value) {r : EReal} {y : Nat}
    (h452 : V 452 = .bits 16 (BitVec.ofNat 64 y)) (hr : Rd (V 2885) r)
    (hm : (V 2950).bytes = 4) (hl : (V 2955).bytes = 4) :
    xCond (lookupD (e1_facts0 V)) e1_items0 := by
  have ec := e1_cvt h452
  simp only [e1_items0, xCond]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨_, setpE_reads (.inl rfl) (rd_read hr) readEReal_negInf⟩
  · exact ⟨_, ec⟩
  · show ∃ v, coreF e1_op1149 [1724] [okVal (.bits 32 0) (coreF e1_op1148 [452] [V 452])] = .ok v
    rw [ec]
    simp only [w0m_okVal]
    exact ⟨_, w0m_and_imm (k := 255) (kn := 255) rfl (by simp) (by omega) (by norm_num)⟩
  · exact c_selpF hl
  · exact c_selpF hm
  · exact c_movImm rfl
  · exact c_movImm rfl

theorem e3_cond_of_reads (V : Nat → Value) {a p : ℝ} (ha : Rd (V 1727) a) (hp : Rd (V 1728) p) :
    xCond (lookupD (e3_facts0 V)) e3_items0 :=
  ⟨⟨_, addE_reads (rd_read ha) (rd_read hp) (addEReal_coe a p)⟩, trivial⟩

theorem e5_cond_of_reads (V : Nat → Value) {s : ℝ} (hs : Rd (V 482) s) :
    xCond (lookupD (e5_facts0 V)) e5_items0 :=
  ⟨⟨_, setpE_reads (.inl rfl) (rd_read hs) (readEReal_of_valFloat valFloat_zero)⟩,
    c_movImm rfl, trivial⟩

theorem e7_cond_of_reads (V : Nat → Value) (hf : (V 2956).bytes = 4) :
    xCond (lookupD (e7_facts0 V)) e7_items0 :=
  ⟨And.intro hf hf, c_movImm rfl, trivial⟩

theorem alpha_cond_of_reads (V : Nat → Value) {A : Value} {s : ℝ} (hA : OkF A s)
    (hf : (∃ y, A = .bits 32 y) ∨ ∃ r, A = .float .f32 r)
    (hV : V 3565 = joinValue A (.bits 32 0)) : alpha_cond V := by
  have hz : Clean (.bits 32 0) := ⟨rfl, fun _ _ _ h => (by cases h), fun _ _ h => by
    simp only [Value.bits.injEq] at h; obtain ⟨-, rfl⟩ := h; simp⟩
  have hj := split_join_clean hA.1 hz
  have hb8 : (joinValue A (.bits 32 0)).bytes = 8 := by
    rcases hf with ⟨y, rfl⟩ | ⟨r, rfl⟩
    · simp [joinValue, Value.bytes]
    · simp [joinValue, Value.bytes]; rfl
  have hA4 := hA.1.1
  have hl : lk [3565] [V 3565] 3565 = joinValue A (.bits 32 0) := by
    rw [hV]; simp [lk]
  have e : sinkW 64 true 3565 (lk [3565] [V 3565]) = .ok A := by
    simp only [hl, sinkW, hb8, hj, hA4]
    simp [Value.bytes]
  have e' : alpha_v713 V = A := by
    unfold alpha_v713
    simp only [e]; rfl
  show xCond (lookupD (alpha_facts0 V)) alpha_items0
  simp only [alpha_items0, xCond]
  exact ⟨⟨A, e⟩,
    by show (alpha_v713 V).bytes = 4 ∧ (alpha_v713 V).bytes = 4; rw [e']; exact ⟨hA4, hA4⟩,
    c_movImm rfl, trivial⟩

theorem f32Value_log2e : f32Value 1069066811 = some (12102203 / 8388608) := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  norm_num

theorem valFloat_log2e :
    valFloat .f32 (.bits 32 (BitVec.ofNat 64 1069066811)) = .ok (12102203 / 8388608) := by
  have := valFloat_b32 (b := 1069066811) (by norm_num) f32Value_log2e
  simpa [b32] using this

/-- The sink word's scaling is no fault when the loaded word reads as a number. -/
theorem sk_cond_of_reads (V : Nat → Value) {x : EReal} (hx : Rd (V 932) x) : sk_cond V := by
  have e : fF (mulL true) [.reg 932, .f32imm 1069066811] [V 932] =
      mulE true (V 932) (.bits 32 (BitVec.ofNat 64 1069066811)) := by
    simp [fF, fOpnd, lk, regsOf, regOf, mulL]
  obtain ⟨hz, -⟩ := w0r_mulpos (M := x) (rd_lane hx) (sc := 12102203 / 8388608) (by norm_num)
  refine ⟨⟨erealValue .f32 (x * (((12102203 / 8388608 : ℝ)) : EReal)), ?_⟩, trivial⟩
  show fF (mulL true) [.reg 932, .f32imm 1069066811] [V 932] = _
  rw [e, mulE_reads (rd_read hx) (readEReal_of_valFloat valFloat_log2e) hz]

theorem e6_cond_of_reads (W : Nat → Value) {s m : ℝ} {sk : EReal} (hs : Rd (W 482) s)
    (hm : Rd (W 481) m) (hk : Rd (W 2880) sk) (hs0 : 0 ≤ s) (hne : s ≠ 0) :
    xCond (lookupD (e6_facts0 W)) e6_items0 := by
  have hv := w0e_e6_ex2 W hm hk
  have hsub : ∃ v, subE true (W 2880) (W 481) = .ok v := by
    rcases rd_lane hk with ⟨k, rfl⟩ | rfl
    · exact ⟨_, subE_reads (z := ((k + -m : ℝ) : EReal)) (rd_read hk) (rd_read hm)
        (by rw [← EReal.coe_neg]; exact addEReal_coe k (-m))⟩
    · exact ⟨_, subE_reads (z := ⊥) (rd_read hk) (rd_read hm) (by simp [addEReal])⟩
  have hex : ∃ v, ex2E true (e6_v1192 W) = .ok v := by
    unfold e6_v1192
    rcases rd_lane hk with ⟨k, rfl⟩ | rfl
    · rw [subE_reads (z := ((k + -m : ℝ) : EReal)) (rd_read hk) (rd_read hm)
        (by rw [← EReal.coe_neg]; exact addEReal_coe k (-m))]
      simp only [okVal, erealValue_coe]
      exact ⟨_, ex2E_real (readEReal_float _)⟩
    · rw [subE_reads (z := ⊥) (rd_read hk) (rd_read hm) (by simp [addEReal])]
      simp only [okVal, erealValue_bot]
      exact ⟨_, ex2E_negInf true⟩
  have h2 : e6_v1194 W = .float .f32 (s + w0Sk2 sk m) := by
    unfold e6_v1194
    rw [hv, addE_reads (rd_read hs) (readEReal_float _) (addEReal_coe s _), erealValue_coe]
    rfl
  have hadd : ∃ v, floatE (addI true) [W 482, e6_v1193 W] = .ok v := by
    rw [hv]; exact ⟨_, addE_reads (rd_read hs) (readEReal_float _) (addEReal_coe s _)⟩
  have hpos : s + w0Sk2 sk m ≠ 0 := by
    have : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hne)
    have : 0 ≤ w0Sk2 sk m := by unfold w0Sk2; split_ifs <;> positivity
    positivity
  have e1 : fF (approxE (divI true)) [.reg 1744, .reg 1743] [e6_v1195 W, e6_v1194 W] =
      approxE (divI true) [e6_v1195 W, e6_v1194 W] := by
    simp [fF, fOpnd, lk, regsOf, regOf, List.lookup]
  have hd : approxE (divI true) [e6_v1195 W, e6_v1194 W] =
      .ok (.float .f32 (1 / (s + w0Sk2 sk m))) :=
    approxE_div_fin valFloat_one (by rw [h2]; simp [valFloat, pure, Except.pure]) hpos
  simp only [e6_items0, xCond]
  exact ⟨hsub, hex, hadd, trivial, ⟨_, e1.trans hd⟩, trivial⟩

theorem erealValue_ne_sentinel (x : EReal) : erealValue .f32 x ≠ .bits 32 0 := by
  unfold erealValue
  split_ifs <;> first | decide | simp

theorem e4_cond_of_reads (W : Nat → Value) {s : ℝ} {M : EReal} (hs : W 482 = .float .f32 s)
    (hM : Rd (W 481) M) (h0 : 0 ≤ s) : xCond (lookupD (e4_facts0 W)) e4_items0 := by
  rcases h0.lt_or_eq with hp | hz
  · have h1 : e4_v1162 W = .float .f32 (Real.log s / Real.log 2) := by
      unfold e4_v1162
      simp [lg2E, hs, valFloat, pure, Except.pure, Except.toOption, hp, okVal]
    have h2 := w0e_v1163 W hs hp
    have h3 := w0e_v1164 W hs hM hp
    have hpos : (0 : ℝ) < lseLog2Factor := by unfold lseLog2Factor; norm_num
    have hl : SK.ni.Lane (M * (lseLog2Factor : EReal) +
        ((Real.log s / Real.log 2 * lseLog2Factor : ℝ) : EReal)) := by
      rcases rd_lane hM with ⟨m, rfl⟩ | rfl
      · exact .inl ⟨m * lseLog2Factor + Real.log s / Real.log 2 * lseLog2Factor, by push_cast; rfl⟩
      · exact .inr (by rw [EReal.bot_mul_of_pos (by exact_mod_cast hpos), EReal.bot_add])
    have hR : Rd (e4_v1164 W) (M * (lseLog2Factor : EReal) +
        ((Real.log s / Real.log 2 * lseLog2Factor : ℝ) : EReal)) := by
      rw [h3]; exact rd_erealValue hl
    simp only [e4_items0, xCond]
    exact ⟨cond_of_okVal h1 (by simp), cond_of_okVal h2 (by simp),
      cond_of_okVal h3 (erealValue_ne_sentinel _),
      ⟨_, setpE_reads (.inl rfl) (rd_read hR) readEReal_negInf⟩,
      c_selpF (r := 1732) hR.1.1, trivial⟩
  · subst hz
    have h1 := w0e_zero_v1162 W hs
    have h2 := w0e_zero_v1163 W hs
    have h4 := w0e_zero_v1164 W hs hM
    have hR4 : readEReal .f32 (e4_v1164 W) = some (.ok ⊥) := by rw [h4]; exact readEReal_negInf
    simp only [e4_items0, xCond]
    exact ⟨cond_of_okVal h1 (by decide), cond_of_okVal h2 (by decide),
      cond_of_okVal h4 (by decide),
      ⟨_, setpE_reads (.inl rfl) hR4 readEReal_negInf⟩,
      c_selpF (r := 1732) (show (e4_v1164 W).bytes = 4 by rw [h4]; rfl), trivial⟩


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
