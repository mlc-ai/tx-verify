-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.GatedOperands
import Mathlib.Tactic

/-! Absolute forward error of a causal coefficient after a finite-precision dot reduction. -/
@[expose] public section
namespace FlashKda.GateAccumulation
open GatedOperands
noncomputable section

abbrev unit : ℝ := 1/8388608

/-- Up to one binary32 ulp of relative error for an individual operation on normal values.
This relation also requires an exact zero when the mathematical result is zero. -/
def Rounded (x y : ℝ) := |y-x| ≤ unit*|x|

theorem of_single {x : ℝ} {y : ℚ} (h : Single x y) : Rounded x y := by
  exact (single_err h).trans (mul_le_mul_of_nonneg_right (by norm_num [unit]) (abs_nonneg _))

/-- A reduction of height at most h with ideal sum x, sum of absolute terms mass, and
computed result y. Shorter branches may be padded without introducing extra rounding. -/
inductive Reduction : Nat → ℝ → ℝ → ℝ → Prop
  | leaf (v : ℝ) : Reduction 0 v |v| v
  | round {h x mass y z} : Reduction h x mass y → Rounded y z → Reduction (h+1) x mass z
  | add {h x₁ x₂ m₁ m₂ y₁ y₂ z} : Reduction h x₁ m₁ y₁ → Reduction h x₂ m₂ y₂ →
      |z-(y₁+y₂)| ≤ unit*(|y₁|+|y₂|) → Reduction (h+1) (x₁+x₂) (m₁+m₂) z

theorem addition {x y z : ℝ} (rnd : Rounded (x+y) z) :
    |z-(x+y)| ≤ unit*(|x|+|y|) :=
  rnd.trans (mul_le_mul_of_nonneg_left (abs_add_le x y) (by norm_num [unit]))

private theorem step {h : Nat} {x mass y z : ℝ}
    (size : |y| ≤ (1+unit)^h*mass) (error : |y-x| ≤ ((1+unit)^h-1)*mass)
    (v : |z-y| ≤ unit*((1+unit)^h*mass)) :
    |z| ≤ (1+unit)^(h+1)*mass ∧ |z-x| ≤ ((1+unit)^(h+1)-1)*mass := by
  have triangle := abs_add_le (z-y) y
  rw [sub_add_cancel] at triangle
  have e := abs_sub_le z y x
  rw [pow_succ]
  constructor <;> nlinarith only [triangle,v,size,e,error]

theorem error {h x mass y} (r : Reduction h x mass y) :
    |y| ≤ (1+unit)^h*mass ∧ |y-x| ≤ ((1+unit)^h-1)*mass := by
  induction r with
  | leaf w => simp
  | round prev rnd ih =>
    exact step ih.1 ih.2 (rnd.trans (mul_le_mul_of_nonneg_left ih.1 (by norm_num [unit])))
  | @add h a b ma mb ya yb z _ _ rnd ia ib =>
    apply step
    · rw [mul_add]
      exact (abs_add_le ya yb).trans (add_le_add ia.1 ib.1)
    · rw [show ya+yb-(a+b) = (ya-a)+(yb-b) by ring,mul_add]
      exact (abs_add_le _ _).trans (add_le_add ia.2 ib.2)
    · exact rnd.trans (mul_le_mul_of_nonneg_left
        (by rw [mul_add]; exact add_le_add ia.1 ib.1) (by norm_num [unit]))

private theorem factor {h : Nat} (depth : h ≤ 129) : (1+unit)^h-1 ≤ 16/1000000 := by
  have h1 : (1+unit)^h ≤ (1+unit)^129 :=
    pow_le_pow_right₀ (by norm_num [unit]) depth
  have h2 : ((1:ℚ)+1/8388608)^129-1 ≤ 16/1000000 := by decide +kernel
  have cast := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at cast
  exact (sub_le_sub_right h1 1).trans cast

/-- Combine the individual prepared operand errors and all rounding in a dot tree.
The depth counts both leaf products and additions, so 129 also covers 128 serial
multiply/add steps with a separate multiplication and one extra addition of zero. -/
theorem coefficient {d h : Nat} (terms target weight : Fin d → ℝ)
    (nonneg : ∀ i, 0 ≤ weight i) (bound : ∀ i, |target i| ≤ weight i)
    (formed : ∀ i, |terms i-target i| ≤ (783/100000)*weight i) {result : ℝ}
    (reduced : Reduction h (∑ i, terms i) (∑ i, |terms i|) result) (depth : h ≤ 129) :
    |result - ∑ i, target i| ≤ (785/100000) * ∑ i, weight i := by
  have w : 0 ≤ ∑ i, weight i := Finset.sum_nonneg fun i _ => nonneg i
  have formation : |(∑ i, terms i) - ∑ i, target i| ≤ (783/100000)*∑ i, weight i := by
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _ => formed i)
  have mass : (∑ i, |terms i|) ≤ (1+783/100000)*∑ i, weight i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have t := abs_add_le (terms i-target i) (target i)
    rw [sub_add_cancel] at t
    linarith [formed i,bound i]
  have e := (error reduced).2.trans
    (mul_le_mul_of_nonneg_right (factor depth) (Finset.sum_nonneg fun i _ => abs_nonneg _))
  have capped := e.trans (mul_le_mul_of_nonneg_left mass (by norm_num))
  linarith [abs_sub_le result (∑ i, terms i) (∑ i, target i)]

/-- Final bfloat16 store of the coefficient after binary32 accumulation. -/
theorem narrowing {result target mass : ℝ} {stored : ℚ} (size : |target| ≤ mass)
    (error : |result-target| ≤ (785/100000)*mass) (conversion : Brain result stored) :
    |(stored:ℝ)-target| ≤ (1179/100000)*mass := by
  obtain ⟨v,rounded,close⟩ := OperandRound.value _ conversion.1
  obtain rfl := Option.some.inj (rounded.symm.trans conversion.2)
  have r := abs_add_le (result-target) target
  rw [sub_add_cancel] at r
  linarith [abs_sub_le (v:ℝ) result target,abs_nonneg target]

/-- The reference uses the computed gate prefixes of the two positions. Both input
preparation and reduction are included, with operands and prefixes at the compiled sites. -/
theorem from_prefixes {d h : Nat} (q k a b : Chunk.Row d) (s : Nat → Fin d → ℚ)
    {gateScale : ℚ} (lo : -29/4 ≤ gateScale) (hi : gateScale ≤ 0)
    {j t : Nat} (previous : j ≤ t) (fit : t ≤ 16) (start : ∀ i, s 0 i = 0)
    (steps : ∀ n < t, ∀ i, GateRange.Update gateScale (s n i) (s (n+1) i))
    (scale : ℝ) (qd qs ki aq bk : Fin d → ℚ)
    (decay : ∀ i, GatePair.allowed (s t i:ℝ) (a i))
    (restore : ∀ i, GatePair.allowed (-(s j i:ℝ)) (b i))
    (query : ∀ i, Single (q i*a i) (qd i)) (scaled : ∀ i, Single ((qd i:ℝ)*scale) (qs i))
    (key : ∀ i, Single (k i*b i) (ki i))
    (queryBf : ∀ i, Brain (qs i:ℝ) (aq i)) (keyBf : ∀ i, Brain (ki i:ℝ) (bk i))
    {result : ℝ} (reduced : Reduction h (∑ i, (aq i:ℝ)*bk i) (∑ i, |(aq i:ℝ)*bk i|) result)
    (depth : h ≤ 129) :
    |result-scale*GatePair.ideal q k (fun i => (s t i:ℝ)) (fun i => (s j i:ℝ))| ≤
      (785/100000)*|scale| * ∑ i, |q i*k i| ∧
    ∀ v : ℚ, Brain result v →
      |(v:ℝ)-scale*GatePair.ideal q k (fun i => (s t i:ℝ)) (fun i => (s j i:ℝ))| ≤
        (1179/100000)*|scale| * ∑ i, |q i*k i| := by
  let weight (i : Fin d) := |scale| * |q i*k i|
  let target (i : Fin d) : ℝ := scale*((q i*k i)*(2:ℝ)^((s t i:ℝ)-(s j i:ℝ)))
  have per i : |(aq i:ℝ)*bk i-target i| ≤ (783/100000)*weight i := by
    have one := GatedOperands.from_prefixes (d := 1) (fun _ => q i) (fun _ => k i)
      (fun _ => a i) (fun _ => b i) (fun n _ => s n i) lo hi previous fit
      (fun _ => start i) (fun n hn _ => steps n hn i) scale
      (fun _ => qd i) (fun _ => qs i) (fun _ => ki i) (fun _ => aq i) (fun _ => bk i)
      (fun _ => decay i) (fun _ => restore i) (fun _ => query i) (fun _ => scaled i)
      (fun _ => key i) (fun _ => queryBf i) (fun _ => keyBf i)
    simpa [target,weight,Chunk.dot,GatePair.ideal,mul_assoc] using one
  have size i : |target i| ≤ weight i := by
    have order := GateRange.ordered lo hi (fun n => s n i) (start i) t fit
      (fun n hn => steps n hn i) previous le_rfl
    have neg : (s t i:ℝ)-(s j i:ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast order)
    have damp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) neg
    rw [Real.rpow_zero] at damp
    simp only [target,weight,abs_mul,abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) damp) (abs_nonneg _)
  have all := coefficient _ target weight (fun i => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    size per reduced depth
  constructor
  · simpa [target,weight,GatePair.ideal,Finset.mul_sum,mul_assoc] using all
  intro v conversion
  have cap := (Finset.abs_sum_le_sum_abs target Finset.univ).trans
    (Finset.sum_le_sum fun i _ => size i)
  simpa [target,weight,GatePair.ideal,Finset.mul_sum,mul_assoc] using
    narrowing cap all conversion

end
end FlashKda.GateAccumulation
