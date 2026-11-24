-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.OneTokenNormalize
import Mathlib.Tactic

/-! The sign reversal follows from normalized bfloat16 operands and the two subsequent
roundings in an arithmetic model of the measured one-token path. -/
@[expose] public section
namespace FlashKda.OneToken
open PTX
noncomputable section

/-- Extract a finite nonzero rational after a round-to-nearest-even bfloat16 conversion. -/
def roundedCoordinate (x : ℝ) : Option ℚ := do
  let .fin y ← brainFloat.round .rn .inf x false | none
  return y

/-- Query and key each have four nonzero coordinates. The one-token dot is stored in
bfloat16, then scaled by one half and stored as the public output. -/
def firstCoordinate (q₀ q₁ q₂ q₃ k₀ k₁ k₂ k₃ : ℝ) : Option FVal := do
  let a ← roundedCoordinate q₀
  let b ← roundedCoordinate q₁
  let c ← roundedCoordinate q₂
  let d ← roundedCoordinate q₃
  let w ← roundedCoordinate k₀
  let x ← roundedCoordinate k₁
  let y ← roundedCoordinate k₂
  let z ← roundedCoordinate k₃
  let product ← roundedCoordinate ((a*w + b*x + c*y + d*z : ℚ) : ℝ)
  brainFloat.round .rn .inf (product/2) false

private theorem coordinate_of_cell {center x : ℝ} {value : ℚ} (h : conversionCell center value)
    (e : |x-center| ≤ 1/4194304) : roundedCoordinate x = some value := by
  unfold roundedCoordinate
  rw [h x e]
  rfl

/-- All permitted reciprocal square roots and independently perturbed products give a positive
arithmetic result for an input whose real output is strictly negative. -/
theorem positive_rounded_forward {q k q₀ q₁ q₂ q₃ k₀ k₁ k₂ k₃ : ℝ}
    (hq : admissibleRoot (3146753/1048576) q) (hk : admissibleRoot (14696465/16777216) k)
    (eq₀ : |q₀-q| ≤ 1/4194304) (eq₁ : |q₁-q| ≤ 1/4194304)
    (eq₂ : |q₂-(-q)| ≤ 1/4194304) (eq₃ : |q₃-(-q/32)| ≤ 1/4194304)
    (ek₀ : |k₀-k/4| ≤ 1/4194304) (ek₁ : |k₁-k/2| ≤ 1/4194304)
    (ek₂ : |k₂-3*k/4| ≤ 1/4194304) (ek₃ : |k₃-k/32| ≤ 1/4194304) :
    firstCoordinate q₀ q₁ q₂ q₃ k₀ k₁ k₂ k₃ = some (.fin (69/262144)) ∧
      answer (1/32) 1 < 0 := by
  obtain ⟨a,b,c,d,e,f,g⟩ := normalized_values hq hk
  refine ⟨?_, measured_sign_flip.1⟩
  simp only [firstCoordinate, coordinate_of_cell a eq₀, coordinate_of_cell a eq₁,
    coordinate_of_cell b eq₂, coordinate_of_cell c eq₃, coordinate_of_cell d ek₀,
    coordinate_of_cell e ek₁, coordinate_of_cell f ek₂, coordinate_of_cell g ek₃,
    bind, Option.bind]
  have dotValue : (((37/64*(137/512) + 37/64*(137/256) + (-37/64)*(205/256) +
      (-37/2048)*(137/4096) : ℚ)) : ℝ) = 4403/8388608 := by norm_num
  rw [dotValue]
  unfold roundedCoordinate
  rw [rounded_dot]
  change brainFloat.round .rn .inf (((69/131072 : ℚ) : ℝ)/2) false = _
  push_cast
  exact rounded_output

end
end FlashKda.OneToken
