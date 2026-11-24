-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.FiniteTolerance
import Kernels.FlashKdaFwd.Audit.OneToken

/-! Sharp attainable error bounds over all bfloat16 output words, on two legal
single-token calls. The results quantify over every possible implementation output. -/
namespace FlashKda.OutputFormat
open PTX Chunk Sequence Algorithm OneToken FiniteInputs
noncomputable section

def least : ℚ := 1/2^133
def greatest : ℚ := 255*2^120

/-- Every finite word is zero or has magnitude at least the minimum subnormal, and its
magnitude is at most the largest normal. Both endpoints are actual format values. -/
theorem finite_range {w : Nat} {x : ℚ}
    (read : (FloatFmt.bf16.layout.decode w).bind FVal.num = some x) :
    (x = 0 ∨ least ≤ |x|) ∧ |x| ≤ greatest := by
  obtain ⟨v,hv,hn⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨eq,top⟩ := FloatFmt.decode_number .bf16 hv (by simp [hn])
  rw [eq,FVal.num_fieldVal] at hn
  let f := w % 32768
  change f ≤ 0x7f7f at top
  have mag : |x| = Layout.magnitude 8 7 f := by
    change some (if w / 32768 % 2 == 1 then -Layout.magnitude 8 7 f
      else Layout.magnitude 8 7 f) = some x at hn
    rw [← Option.some.inj hn]
    split <;> simp [abs_of_nonneg (Layout.magnitude_nonneg 8 7 f)]
  rw [mag]
  constructor
  · by_cases zero : f = 0
    · left
      apply abs_eq_zero.mp
      rw [mag,zero,Layout.magnitude_zero]
    · right
      exact (Layout.magnitude_strictMono 8 7).monotone (by omega : 1 ≤ f)
  · exact (Layout.magnitude_strictMono 8 7).monotone top

theorem endpoint_words :
    (FloatFmt.bf16.layout.decode 0).bind FVal.num = some 0 ∧
    (FloatFmt.bf16.layout.decode 0x7f7f).bind FVal.num = some greatest := by decide +kernel

/-- Given a nonnegative exact target at or below half the smallest positive output,
zero attains the least absolute error. No numerical or nonnumerical word does better. -/
theorem near_zero {target : ℝ} (pos : 0 ≤ target) (tiny : 2*target ≤ (least:ℝ))
    (absolute relative : ℝ) :
    (∃ w : Fin 65536, within .bf16 w.val target absolute relative) ↔
      target ≤ absolute + relative * |target| := by
  constructor
  · rintro ⟨_,x,read,close⟩
    obtain ⟨zero|lower,_⟩ := finite_range read
    · simpa [zero,abs_of_nonneg pos] using close
    · have lb : (least:ℝ) ≤ |(x:ℝ)| := by exact_mod_cast lower
      have tri := abs_add_le ((x:ℝ)-target) target
      rw [sub_add_cancel,abs_of_nonneg pos] at tri
      linarith
  · intro enough
    refine ⟨0,0,endpoint_words.1,?_⟩
    simpa [abs_of_nonneg pos] using enough

/-- Above the positive representable range, saturation to the largest finite word attains
the least absolute error among all words that satisfy a numerical comparison. -/
theorem above_range {target : ℝ} (large : (greatest:ℝ) ≤ target) (absolute relative : ℝ) :
    (∃ w : Fin 65536, within .bf16 w.val target absolute relative) ↔
      target - greatest ≤ absolute + relative * |target| := by
  constructor
  · rintro ⟨_,x,read,close⟩
    have upper : (x:ℝ) ≤ (greatest:ℝ) := by
      exact_mod_cast (le_abs_self x).trans (finite_range read).2
    rw [abs_of_nonpos (by linarith : (x:ℝ)-target ≤ 0)] at close
    linarith
  · intro enough
    refine ⟨0x7f7f,greatest,endpoint_words.2,?_⟩
    rw [abs_of_nonpos (by linarith : (greatest:ℝ)-target ≤ 0)]
    linarith

/-- All nonzero raw query/key components in the small call are normal bfloat16 values. -/
def small : ℝ := 1/2^67

def raw (q k : Row 128) (v : ℝ) :=
  activate (fun _ => q) (fun _ => k) (fun _ _ => 0) (fun _ => v) (fun _ => 0) (-1) 0
    (fun _ => 0)

def smallResult : ℝ :=
  output (raw (four 1 0 small 0) (four 0 1 small 0) 1) (fun _ => 0) 1 1 0
def largeResult : ℝ :=
  output (raw (four 1 0 0 0) (four 1 0 0 0) (2^127)) (fun _ => 0) 1 8 0

theorem public_words :
    FloatFmt.bf16.layout.decode 0x3f80 = some (.fin 1) ∧
    FloatFmt.bf16.layout.decode 0x1e00 = some (.fin (1/2^67)) ∧
    FloatFmt.bf16.layout.decode 0x7f00 = some (.fin (2^127)) ∧
    FloatFmt.bf16.layout.decode 0 = some (.zero false) ∧
    FloatFmt.f32.layout.decode 0x41000000 = some (.fin 8) ∧
    FloatFmt.f32.layout.decode 0xbf800000 = some (.fin (-1)) := by decide +kernel

private theorem small_dots :
    let q := four 1 0 small 0
    let k := four 0 1 small 0
    dot k q = small^2 ∧ dot q q = 1 + small^2 ∧ dot k k = 1 + small^2 := by
  simp only [dot_four]
  norm_num [four,pow_two]

theorem small_exact : smallResult = small^2/(2*(1 + small^2 + 1/1000000)) := by
  rw [smallResult,single]
  simp only [raw,activate,sigmoid,neg_zero,Real.exp_zero,normalize_dot,
    small_dots.1,small_dots.2.1,small_dots.2.2]
  rw [← sq,Real.sq_sqrt (by positivity)]
  norm_num [small]

theorem large_exact : largeResult = (2:ℝ)^129*1000000/1000001 := by
  rw [largeResult,single]
  simp only [raw,activate,sigmoid,neg_zero,Real.exp_zero,normalize_dot,dot_four]
  norm_num [four,← sq,div_pow,Real.sq_sqrt (show 0 ≤ (1000001:ℝ) by norm_num)]

/-- Correct IEEE rounding gives positive zero at the small end and positive infinity at
the large end. The numerical acceptance criteria below compare against the exact real. -/
theorem correctly_rounded :
    FloatFmt.bf16.layout.round .rn .inf smallResult false = some (.zero false) ∧
    FloatFmt.bf16.layout.round .rn .inf largeResult false = some (.inf false) := by
  change (Layout.binary 8 7 true .ieee).round .rn .inf _ _ = _ ∧
    (Layout.binary 8 7 true .ieee).round .rn .inf _ _ = _
  constructor
  · rw [small_exact,Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
      (by norm_num [small,Layout.magnitude,Layout.bias])
      (by norm_num [small,Layout.magnitude,Layout.bias]) (by simp)]
    norm_num [small,Layout.magnitude,Layout.bias,RoundMode.away,Layout.fieldVal]
  · rw [large_exact,Layout.round_inf_ieee (m := .rn) (by trivial)
      (by norm_num [Layout.maxNorm_binary,Layout.topField,Layout.magnitude,Layout.bias])]
    norm_num [Layout.topField,Layout.magnitude,Layout.bias]

/-- These relative tolerances are feasible exactly at and above the two stated limits.
The optimizing words are given by the corresponding endpoint theorems. -/
theorem optimal_relative (relative : ℝ) :
    ((∃ w : Fin 65536, within .bf16 w.val smallResult 0 relative) ↔ 1 ≤ relative) ∧
    ((∃ w : Fin 65536, within .bf16 w.val largeResult 0 relative) ↔
      51399949/102400000 ≤ relative) := by
  have pos : 0 < smallResult := by rw [small_exact]; norm_num [small]
  have tiny : 2*smallResult ≤ least := by rw [small_exact]; norm_num [small,least]
  have big : (greatest:ℝ) ≤ largeResult := by rw [large_exact]; norm_num [greatest]
  constructor
  · rw [near_zero pos.le tiny,abs_of_pos pos,zero_add]
    simpa only [one_mul] using (show 1*smallResult ≤ relative*smallResult ↔ 1 ≤ relative
      from mul_le_mul_iff_left₀ pos)
  · rw [above_range big,large_exact]
    norm_num [greatest]
    constructor <;> intro h <;> linarith

/-- Even one unit of absolute tolerance plus 50 percent of the exact result is impossible
for the large call, including if a kernel saturates to its maximum finite output. -/
theorem large_impossible (w : Fin 65536) : ¬within .bf16 w.val largeResult 1 (1/2) := by
  have big : (greatest:ℝ) ≤ largeResult := by rw [large_exact]; norm_num [greatest]
  intro close
  have h := (above_range big 1 (1/2)).mp ⟨w,close⟩
  rw [large_exact] at h
  norm_num [greatest] at h

/-- In the large call all 128 output channels have the same exact target. The usual RMS
comparison divides by the reference RMS plus 10⁻⁸. Every tensor of finite output words
still has a ratio above one half, computed here in the reals. -/
theorem large_rms (words : Fin 128 → Fin 65536) (values : Fin 128 → ℚ)
    (numeric : ∀ i, (FloatFmt.bf16.layout.decode (words i).val).bind FVal.num = some (values i)) :
    1/2 < Real.sqrt ((∑ i, ((values i : ℝ)-largeResult)^2)/128) /
      (largeResult + 1/100000000) := by
  have gap : 0 ≤ largeResult - greatest := by rw [large_exact]; norm_num [greatest]
  have each (i : Fin 128) : (largeResult-(greatest:ℝ))^2 ≤ ((values i:ℝ)-largeResult)^2 := by
    have h : (values i : ℝ) ≤ greatest := by
      exact_mod_cast (le_abs_self _).trans (finite_range (numeric i)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr h) gap, sq_nonneg ((greatest:ℝ)-values i)]
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_ofNat] at summed
  have rms := Real.le_sqrt_of_sq_le (by linarith only [summed] :
    (largeResult-(greatest:ℝ))^2 ≤ (∑ i, ((values i:ℝ)-largeResult)^2)/128)
  apply (lt_div_iff₀ (by rw [large_exact]; positivity)).mpr
  exact lt_of_lt_of_le (by rw [large_exact]; norm_num [greatest]) rms

/-- The input scaling parameter in the dense public capture crosses an IEEE
binary64-to-binary32 boundary in the Python-to-C++ binding. -/
theorem captured_scale :
    let passed : ℚ := 6369051672525773/72057594037927936
    let received : ℚ := 11863283/134217728
    (Layout.binary 11 52 true .ieee).decode 0x3fb6a09e667f3bcd = some (.fin passed) ∧
    FloatFmt.f32.layout.decode 0x3db504f3 = some (.fin received) ∧
    FloatFmt.f32.layout.round .rn .inf (passed:ℝ) false = some (.fin received) := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  change (Layout.binary 8 23 true .ieee).round .rn .inf _ false = _
  rw [Layout.round_between (m := .rn) (F := 0x3db504f3) (by trivial) (by decide)
    (by norm_num [Layout.magnitude,Layout.bias]) (by norm_num [Layout.magnitude,Layout.bias])
    (by simp)]
  norm_num [Layout.magnitude,Layout.bias,Layout.fieldVal,RoundMode.away]

end
end FlashKda.OutputFormat
