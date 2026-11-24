-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.NormRange
public import Kernels.FlashKdaFwd.Proof.Seed
import Mathlib.Tactic

/-! The exponential and reciprocal-exponential factors in a causal query-key product.
The two-ulp envelope is measured from the correctly rounded binary32 exponential. -/
@[expose] public section
namespace FlashKda.GatePair
open PTX RootContract
noncomputable section

abbrev low : Nat := 7*2^23
abbrev high : Nat := 247*2^23
abbrev unitError : ℝ := 1/2097152

private theorem endpoints :
    magnitude low = (1:ℚ)/2^120 ∧ magnitude high = (2:ℚ)^120 := by decide +kernel

private theorem gap (f : Nat) (normalField : 8388608 ≤ f) :
    (magnitude (f+1) : ℝ) - magnitude f ≤ (magnitude f : ℝ)/8388608 := by
  exact_mod_cast OperandRound.normal_spacing 8 23 f normalField

/-- Locate the exact nearest-even result for either sign in this interval of normal fields. -/
theorem signed_anchor {x : ℝ} (lower : (1:ℝ)/2^120 ≤ |x|) (upper : |x| ≤ 2^120) :
    ∃ r, low ≤ r ∧ r ≤ high ∧
      format.round .rn .inf x false = some (.fin (OperandRound.signed x (magnitude r))) ∧
      |((OperandRound.signed x (magnitude r) : ℚ):ℝ)-x| ≤ |x|/16777216 := by
  have lo : (magnitude low : ℝ) ≤ |x| := by simpa only [endpoints.1, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using lower
  have hi : |x| ≤ (magnitude high : ℝ) := by rw [endpoints.2]; exact_mod_cast upper
  obtain ⟨f,lf,ft,fx,eq|⟨ht,lt,next⟩⟩ := NormRange.locate (by decide : low ≤ high) lo hi
  · refine ⟨f,lf,ft,?_,?_⟩
    · change (Layout.binary 8 23 true .ieee).round .rn .inf x false = _
      rw [Layout.round_exact (m := .rn) (F := f) (by trivial) (by dsimp [low] at lf; omega)
        (ft.trans (by decide)) eq.symm (by simp)]
      simp [Layout.fieldVal,OperandRound.signed,show f ≠ 0 by dsimp [low] at lf; omega]
    · rw [OperandRound.signed_error,eq,sub_self,abs_zero]; positivity
  · have step := Layout.round_between (m := .rn) (ov := .inf) (zneg := false)
      (eb := 8) (mb := 23) (signed := true) (sp := .ieee) (x := x) (F := f)
      (by trivial) (lt_of_lt_of_le ht (by decide : high ≤ format.topField)) lt next (by simp)
    obtain ⟨b,rounded,dist⟩ := OperandRound.nearest |x| (magnitude f) (magnitude (f+1))
      (decide (x<0)) (f%2==0) fx next.le
    have dx := gap f (by dsimp [low] at lf; omega)
    cases b
    · refine ⟨f,lf,ft,?_,?_⟩
      · change (Layout.binary 8 23 true .ieee).round .rn .inf x false = _
        rw [step]
        simp [rounded,Layout.fieldVal,OperandRound.signed,show f ≠ 0 by dsimp [low] at lf; omega]
      · rw [OperandRound.signed_error]; simp only [Bool.false_eq_true,ite_false] at dist; linarith
    · refine ⟨f+1,by omega,by omega,?_,?_⟩
      · change (Layout.binary 8 23 true .ieee).round .rn .inf x false = _
        rw [step]; simp [rounded,Layout.fieldVal,OperandRound.signed]
      · rw [OperandRound.signed_error]; simp only [ite_true] at dist; linarith

/-- The anchor for measuring ulps is the actual nearest-even result, including at binade
boundaries where the upward and downward gaps can differ. -/
theorem anchor {x : ℝ} (lower : (1:ℝ)/2^120 ≤ x) (upper : x ≤ 2^120) :
    ∃ r, low ≤ r ∧ r ≤ high ∧ format.round .rn .inf x false = some (.fin (magnitude r)) ∧
      |(magnitude r : ℝ)-x| ≤ x/16777216 := by
  have pos : 0 < x := lt_of_lt_of_le (by norm_num) lower
  simpa only [OperandRound.signed,not_lt.mpr pos.le,ite_false,abs_of_pos pos] using
    (signed_anchor (lower.trans_eq (abs_of_pos pos).symm) ((abs_of_pos pos).trans_le upper))

/-- A numerical envelope for PTX ex2.approx, allowing two upward ulps at the nearest word.
The operand is the effective binary32 value after the instruction's input flush. -/
def allowed (z a : ℝ) : Prop :=
  ∃ r, low ≤ r ∧ r ≤ high ∧
    format.round .rn .inf ((2:ℝ)^z) false = some (.fin (magnitude r)) ∧
    |a-(magnitude r : ℝ)| ≤ 2*((magnitude (r+1) : ℝ)-magnitude r)

private theorem range {z : ℝ} (hz : |z| ≤ 120) :
    (1:ℝ)/2^120 ≤ (2:ℝ)^z ∧ (2:ℝ)^z ≤ 2^120 := by
  obtain ⟨lo,hi⟩ := abs_le.mp hz
  have a := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) lo
  have b := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hi
  constructor <;> norm_num at * <;> assumption

/-- For every input in the stated range the envelope contains an actual binary32 word. -/
theorem attainable {z : ℝ} (hz : |z| ≤ 120) :
    ∃ r, low ≤ r ∧ r ≤ high ∧ allowed z (magnitude r : ℝ) := by
  obtain ⟨r,lo,hi,word,_⟩ := anchor (range hz).1 (range hz).2
  refine ⟨r,lo,hi,r,lo,hi,word,?_⟩
  have monotone : (magnitude r : ℝ) ≤ (magnitude (r+1) : ℝ) := by
    exact_mod_cast (Layout.magnitude_strictMono 8 23).monotone (Nat.le_succ r)
  simp only [sub_self,abs_zero]
  linarith

theorem relative {z a : ℝ} (hz : |z| ≤ 120) (ok : allowed z a) :
    |a-(2:ℝ)^z| ≤ unitError * (2:ℝ)^z := by
  obtain ⟨r,lo,_,word,err⟩ := ok
  obtain ⟨j,_,_,near,delta⟩ := anchor (range hz).1 (range hz).2
  have same : magnitude r = magnitude j := FVal.fin.inj (Option.some.inj (word.symm.trans near))
  rw [← same] at delta
  have spacing := gap r (by dsimp [low] at lo; omega)
  have hi := (abs_le.mp delta).2
  have total := abs_sub_le a (magnitude r : ℝ) ((2:ℝ)^z)
  dsimp [unitError]
  linarith [Real.rpow_pos_of_pos (by norm_num : 0 < (2:ℝ)) z]

/-- Two independent exponential approximations track their exact product even when they
use different prefix values from an earlier key and a later query. -/
theorem product {z w a b : ℝ} (hz : |z| ≤ 120) (hw : |w| ≤ 120)
    (ha : allowed z a) (hb : allowed (-w) b) :
    |a*b-(2:ℝ)^(z-w)| ≤ (1/1000000)*(2:ℝ)^(z-w) := by
  let x := (2:ℝ)^z
  let y := (2:ℝ)^(-w)
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hy : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  have prod : x*y = (2:ℝ)^(z-w)  := by
    dsimp [x,y]; rw [← Real.rpow_add (by norm_num),sub_eq_add_neg]
  have da : |a-x| ≤ unitError*x := relative hz ha
  have db : |b-y| ≤ unitError*y := relative (by simpa using hw) hb
  have err := mul_le_mul da db (abs_nonneg _) (by positivity : 0 ≤ unitError*x)
  have left := mul_le_mul_of_nonneg_right da hy.le
  have right := mul_le_mul_of_nonneg_left db hx.le
  rw [← prod,show a*b-x*y = (a-x)*(b-y) + (a-x)*y + x*(b-y) by ring]
  calc
    _ ≤ |(a-x)*(b-y)| + |(a-x)*y| + |x*(b-y)| :=
      (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul,abs_of_pos hx,abs_of_pos hy]
      dsimp [unitError] at *
      nlinarith only [err,left,right,mul_pos hx hy]

theorem pair {z a b : ℝ} (hz : |z| ≤ 120) (ha : allowed z a) (hb : allowed (-z) b) :
    |a*b-1| ≤ 1/1000000 := by simpa using product hz hz ha hb

/-- Exact coefficient at the supplied query and key prefixes, with the relative decay
between their positions applied coordinatewise. -/
def ideal {d : ℕ} (q k z w : Chunk.Row d) := ∑ i, (q i*k i)*(2:ℝ)^(z i-w i)

theorem same_token {d : ℕ} (q k z : Chunk.Row d) : ideal q k z z = Chunk.dot q k := by
  simp [ideal,Chunk.dot]

/-- For causal positions the exact relative decay lies between zero and one.
Rounded matrix operands contribute a second term to the absolute coefficient error. -/
theorem causal {d : ℕ} (q k z w a b qa kb : Chunk.Row d) {u : ℝ} (hu : 0 ≤ u)
    (hz : ∀ i, |z i| ≤ 120) (hw : ∀ i, |w i| ≤ 120) (ordered : ∀ i, z i ≤ w i)
    (ha : ∀ i, allowed (z i) (a i)) (hb : ∀ i, allowed (-w i) (b i))
    (hq : ∀ i, |qa i-q i*a i| ≤ u*|q i*a i|)
    (hk : ∀ i, |kb i-k i*b i| ≤ u*|k i*b i|) :
    |Chunk.dot qa kb - ideal q k z w| ≤
      ((2*u+u^2)*(1+1/1000000)+1/1000000) * ∑ i, |q i*k i| := by
  let p : Chunk.Row d := fun i => q i*a i
  let r : Chunk.Row d := fun i => k i*b i
  let t i := (2:ℝ)^(z i-w i)
  have tp i : 0 < t i := Real.rpow_pos_of_pos (by norm_num) _
  have top i : t i ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (sub_nonpos.mpr (ordered i))
    simpa [t] using h
  have each i : |a i*b i-t i| ≤ 1/1000000 :=
    (product (hz i) (hw i) (ha i) (hb i)).trans (by linarith [top i])
  have term i : |p i*r i - q i*k i*t i| ≤ (1/1000000)*|q i*k i| := by
    have eq : p i*r i-q i*k i*t i = (a i*b i-t i)*(q i*k i) := by dsimp [p,r]; ring
    rw [eq,abs_mul]
    exact mul_le_mul_of_nonneg_right (each i) (abs_nonneg _)
  have shifted : (∑ i, |p i*r i|) ≤ (1+1/1000000)*∑ i, |q i*k i| := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
    have tri := abs_add_le (p i*r i-q i*k i*t i) (q i*k i*t i)
    rw [sub_add_cancel,abs_mul (q i*k i),abs_of_pos (tp i)] at tri
    linarith [term i,mul_le_mul_of_nonneg_left (top i) (abs_nonneg (q i*k i))]
  have bias : |Chunk.dot p r - ideal q k z w| ≤ (1/1000000)*∑ i, |q i*k i| := by
    simp only [Chunk.dot,ideal,← Finset.sum_sub_distrib,Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _ => term i)
  have base := Seed.dot_round p r qa kb hu hq hk
  have nonneg : 0 ≤ 2*u+u^2 := by positivity
  calc
    _ ≤ |Chunk.dot qa kb - Chunk.dot p r| + |Chunk.dot p r - ideal q k z w| := abs_sub_le ..
    _ ≤ (2*u+u^2)*((1+1/1000000)*∑ i, |q i*k i|) + (1/1000000)*∑ i, |q i*k i| :=
      add_le_add (base.trans (mul_le_mul_of_nonneg_left shifted nonneg)) bias
    _ = _ := by ring

end
end FlashKda.GatePair
