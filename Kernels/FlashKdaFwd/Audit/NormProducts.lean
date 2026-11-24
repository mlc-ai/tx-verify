-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormRoots

/-! Discharge the product-rounding hypotheses on every allowed binary32 reciprocal square root. -/
namespace FlashKda.Binary
open PTX Normalize OneToken
noncomputable section

/-- A normalized coordinate before its bfloat16 store, using a binary32 product with flushing. -/
def singleProduct (x : ℚ) : Option ℚ := do
  let .fin y ← binary32.roundVal .rn true (.fin x) | none
  return y

theorem product_of_round {x y : ℚ} (hx : binary32.minNormal ≤ |x|)
    (hy : binary32.flush (.fin y) = .fin y)
    (hr : binary32.round .rn .inf (x : ℝ) false = some (.fin y)) :
    singleProduct x = some y := by
  have positive : ¬ |(x : ℝ)| < (binary32.minNormal : ℚ) := by exact_mod_cast not_lt.mpr hx
  unfold singleProduct
  simp [Layout.roundVal, Layout.roundFtz, hr, hy, positive]

def exactProductField (x : ℚ) (w : Nat) : Prop :=
  0 < w ∧ w ≤ binary32.topField ∧ |x| = mag w ∧ binary32.minNormal ≤ |x|

instance (x : ℚ) (w : Nat) : Decidable (exactProductField x w) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem product_exact {x : ℚ} {w : Nat} (h : exactProductField x w) : singleProduct x = some x := by
  obtain ⟨hw,ht,heq,hm⟩ := h
  apply product_of_round hm
  · simp [Layout.flush, Layout.subnormal, not_lt.mpr hm]
  · have habs : |(x:ℝ)| = (mag w : ℚ) := by exact_mod_cast heq
    rw [Layout.round_exact (m := .rn) (F := w) (by trivial) hw ht habs (by simp)]
    by_cases hn : x < 0
    · have hn' : (x:ℝ) < 0 := by exact_mod_cast hn
      rw [abs_of_neg hn] at heq
      simp [Layout.fieldVal, Nat.ne_of_gt hw, hn', ← heq]
    · have hn' : ¬ (x:ℝ) < 0 := by exact_mod_cast hn
      rw [abs_of_nonneg (le_of_not_gt hn)] at heq
      simp [Layout.fieldVal, Nat.ne_of_gt hw, hn', ← heq]

def allowed (key : Bool) (i : Fin 4) : ℚ := mag (firstRootWord key + i.val)

theorem query_products (i : Fin 4) :
    let q := allowed false i
    singleProduct q = some q ∧ singleProduct (-q) = some (-q) ∧
    singleProduct (-q/32) = some (-q/32) := by
  have check : ∀ j : Fin 4,
      let w := firstRootWord false + j.val
      let q := allowed false j
      exactProductField q w ∧ exactProductField (-q) w ∧
        exactProductField (-q/32) (w-5*0x800000) := by decide +kernel
  exact ⟨product_exact (check i).1, product_exact (check i).2.1, product_exact (check i).2.2⟩

theorem key_products (i : Fin 4) :
    let k := allowed true i
    singleProduct (k/4) = some (k/4) ∧ singleProduct (k/2) = some (k/2) ∧
    singleProduct (k/32) = some (k/32) := by
  have check : ∀ j : Fin 4,
      let w := firstRootWord true + j.val
      let k := allowed true j
      exactProductField (k/4) (w-2*0x800000) ∧ exactProductField (k/2) (w-0x800000) ∧
        exactProductField (k/32) (w-5*0x800000) := by decide +kernel
  exact ⟨product_exact (check i).1, product_exact (check i).2.1, product_exact (check i).2.2⟩

def third (i : Fin 4) := mag ([0x3f4d245c,0x3f4d245e,0x3f4d245f,0x3f4d2460][i.val]!)

local macro "product_values" : tactic => `(tactic|
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, RoundMode.away, allowed, firstRootWord,
    third, mag, List.getElem!_eq_getElem?_getD])

theorem third_product (i : Fin 4) : singleProduct (3*allowed true i/4) = some (third i) ∧
    |third i - 3*allowed true i/4| ≤ 1/33554432 := by
  have error : ∀ j : Fin 4, |third j - 3*allowed true j/4| ≤ 1/33554432 := by decide +kernel
  refine ⟨?_, error i⟩
  apply product_of_round
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  fin_cases i
  · rw [Layout.round_exact (m := .rn) (F := 0x3f4d245c) (by trivial) (by decide)
      (by decide) (by product_values) (by simp)]
    product_values
  · rw [Layout.round_between (m := .rn) (F := 0x3f4d245d) (by trivial) (by decide)
      (by product_values) (by product_values) (by simp)]
    product_values
  · rw [Layout.round_exact (m := .rn) (F := 0x3f4d245f) (by trivial) (by decide)
      (by decide) (by product_values) (by simp)]
    product_values
  · rw [Layout.round_between (m := .rn) (F := 0x3f4d2460) (by trivial) (by decide)
      (by product_values) (by product_values) (by simp)]
    product_values

def outputUsingRoots (q k : ℚ) : Option FVal := do
  let a ← singleProduct q
  let b ← singleProduct (-q)
  let c ← singleProduct (-q/32)
  let w ← singleProduct (k/4)
  let x ← singleProduct (k/2)
  let y ← singleProduct (3*k/4)
  let z ← singleProduct (k/32)
  firstCoordinate a a b c w x y z

/-- Any positive single-precision reciprocal square roots permitted by the bound give this
same positive output under the scalar product and dot-product semantics of the witness. -/
theorem all_rounded_outputs (qw kw : Nat)
    (hq : admissibleRoot (inputValue false) (mag qw))
    (hk : admissibleRoot (inputValue true) (mag kw)) :
    outputUsingRoots (mag qw) (mag kw) = some (.fin (69/262144)) ∧ answer (1/32) 1 < 0 := by
  obtain ⟨i,rfl⟩ := (all_root_words false _).mp hq
  obtain ⟨j,rfl⟩ := (all_root_words true _).mp hk
  obtain ⟨qa,qb,qc⟩ := query_products i
  obtain ⟨ka,kb,kd⟩ := key_products j
  have kc := (third_product j).1
  change outputUsingRoots (allowed false i) (allowed true j) = _ ∧ _
  simp only [outputUsingRoots, qa, qb, qc, ka, kb, kc, kd, bind, Option.bind]
  push_cast
  have hq' : admissibleRoot (3146753/1048576) (allowed false i) := by
    simpa [inputValue, allowed] using hq
  have hk' : admissibleRoot (14696465/16777216) (allowed true j) := by
    simpa [inputValue, allowed] using hk
  have e : |(third j : ℝ) - 3*(allowed true j : ℝ)/4| ≤ 1/4194304 := by
    fin_cases j <;> product_values
  exact positive_rounded_forward hq' hk' (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) e (by simp)

end
end FlashKda.Binary
