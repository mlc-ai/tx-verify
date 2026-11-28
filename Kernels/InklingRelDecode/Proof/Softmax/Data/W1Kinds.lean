-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Seq
public import Kernels.InklingRelDecode.Proof.Softmax.Data.NumLib

@[expose] public section

/-! # The first window sends a number or `-inf`

Whatever the path (no bias, bias, bias and mask), register 1520 at pc 1838 is a word that reads as a
real number or `-inf`, when the 32 bias packs (`1916 + m`) have `bf16` halves, the 32 score pairs
(`2447 + m`) are pairs of numbers and `1960` is the pair of `1/scale` (`W1In`). The proof types the
generated values (`Gen.w1*_v*`) of the end facts of each run by `NumLib`'s closure lemmas. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- **What the first window reads as numbers**: the bias packs, the pairs of scores and the pair of
`1 / scale`. -/
structure W1In (V : Nat → Value) : Prop where
  bias : ∀ r, 1916 ≤ r → r < 1948 → Bf16Pair (V r)
  score : ∀ r, 2447 ≤ r → r < 2479 → (Kd.pr .fl).Has (V r)
  step : (Kd.pr .fl).Has (V 1960)

/-- A run's value at a register that its facts type is typed when the start value is. -/
theorem V'_has (r : RunData) {W : Nat → Value} {x : Nat} {K : Kd}
    (h : ∀ p ∈ r.fs1 W, p.1 = x → K.Has p.2) (hx : K.Has (W x)) : K.Has (r.V' W x) := by
  unfold RunData.V' valueEx
  cases hl : (r.fs1 W).lookup x with
  | none => exact hx
  | some v => exact h _ (mem_of_lookupK hl) rfl

/-- A run leaves the registers it does not write. -/
theorem V'_pass (r : RunData) (ok : r.Ok) {lo hi : Nat}
    (hout : r.outs.all (fun k => decide (k < lo ∨ hi ≤ k)) = true) (W : Nat → Value) {x : Nat}
    (h1 : lo ≤ x) (h2 : x < hi) : r.V' W x = W x := by
  unfold RunData.V' valueEx
  have : (r.fs1 W).lookup x = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    have hk : p.1 ∈ r.outs := by rw [← ok.h1 W]; exact List.mem_map_of_mem hp
    have := List.all_eq_true.mp hout _ hk
    simp only [decide_eq_true_eq] at this
    have hne : x ≠ p.1 := by omega
    simpa using hne
  rw [this]
  rfl

/-- The pairs the bias run writes are pairs of numbers. -/
theorem a_has (V : Nat → Value) (h : W1In V) :
    ∀ p ∈ Gen.w1a_facts6 V, 2447 ≤ p.1 → p.1 < 2479 → (Kd.pr .fl).Has p.2 := by
  intro p hp
  simp only [Gen.w1a_facts6, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals first
    | (intro h1 h2; dsimp only at h1 h2; exfalso; omega)
    | (intro _ _; dsimp only; repeat' first
        | (apply h.score <;> omega)
        | exact h.step
        | (apply (h.bias _ _ _).1 <;> omega)
        | (apply (h.bias _ _ _).2 <;> omega)
        | apply fma2_has | apply join_fl_has | apply widen_has)

/-- The pairs the mask run writes are pairs of numbers or `-inf`. -/
theorem c_has (V : Nat → Value) (hs : ∀ r, 2447 ≤ r → r < 2479 → (Kd.pr .fl).Has (V r)) :
    ∀ p ∈ Gen.w1c_facts5 V, 2447 ≤ p.1 → p.1 < 2479 → (Kd.pr .ni).Has p.2 := by
  intro p hp
  simp only [Gen.w1c_facts5, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals
    intro _ _
    dsimp only
    repeat' first
      | apply join_ni_has | apply sel_has | apply split1_has | apply split2_has
      | (apply hs <;> omega)

/-- The maximum run of pairs of numbers or `-inf` gives a number or `-inf`. -/
theorem m_has (W : Nat → Value) (h : ∀ r, 2447 ≤ r → r < 2479 → (Kd.pr .ni).Has (W r)) :
    (Kd.s .ni).Has (runM.V' W 1520) := by
  show (Kd.s .ni).Has (Gen.w1m_v1837 W)
  repeat' first
    | (apply h <;> omega)
    | apply split1_has | apply split2_has | apply max3_has | apply max2_has

theorem a_range (V : Nat → Value) (h : W1In V) :
    ∀ x, 2447 ≤ x → x < 2479 → (Kd.pr .fl).Has (runA.V' V x) := fun x h1 h2 =>
  V'_has runA (fun p hp hx => a_has V h p hp (hx ▸ h1) (hx ▸ h2)) (h.score x h1 h2)

theorem c_range (V : Nat → Value) (hs : ∀ r, 2447 ≤ r → r < 2479 → (Kd.pr .fl).Has (V r)) :
    ∀ x, 2447 ≤ x → x < 2479 → (Kd.pr .ni).Has (runC.V' V x) := fun x h1 h2 =>
  V'_has runC (fun p hp hx => c_has V hs p hp (hx ▸ h1) (hx ▸ h2)) (pr_mono (hs x h1 h2))

/-- **The registers the last run starts from are pairs of numbers or `-inf`**, on every path. -/
theorem w1_file (V : Nat → Value) (h : W1In V) :
    ∃ W, (∀ r, 2447 ≤ r → r < 2479 → (Kd.pr .ni).Has (W r)) ∧ vFin V = runM.V' W := by
  have oP1 : runP.outs.all (fun k => decide (k < 1916 ∨ 1948 ≤ k)) = true := by decide +kernel
  have oP2 : runP.outs.all (fun k => decide (k < 1960 ∨ 1961 ≤ k)) = true := by decide +kernel
  have oP3 : runP.outs.all (fun k => decide (k < 2447 ∨ 2479 ≤ k)) = true := by decide +kernel
  have oB : runB.outs.all (fun k => decide (k < 2447 ∨ 2479 ≤ k)) = true := by decide +kernel
  have oT : runT.outs.all (fun k => decide (k < 2447 ∨ 2479 ≤ k)) = true := by decide +kernel
  have hP : W1In (vP V) :=
    { bias := fun x h1 h2 => by
        unfold vP; rw [V'_pass runP runP_ok oP1 V h1 h2]; exact h.bias x h1 h2
      score := fun x h1 h2 => by
        unfold vP; rw [V'_pass runP runP_ok oP3 V h1 h2]; exact h.score x h1 h2
      step := by
        unfold vP; rw [V'_pass runP runP_ok oP2 V (x := 1960) (by omega) (by omega)]
        exact h.step }
  have hA := a_range (vP V) hP
  by_cases h96 : pick96 V = true
  · exact ⟨vP V, fun x h1 h2 => pr_mono (hP.score x h1 h2), by funext r; simp [vFin, h96, vS]⟩
  by_cases h97 : pick97 V = true
  · refine ⟨runT.V' (vA V), fun x h1 h2 => pr_mono ?_, by funext r; simp [vFin, h96, h97, vU]⟩
    rw [V'_pass runT runT_ok oT _ h1 h2]; exact hA x h1 h2
  · refine ⟨runT.V' (runC.V' (runB.V' (vA V))), fun x h1 h2 => ?_,
      by funext r; simp [vFin, h96, h97, vM]⟩
    rw [V'_pass runT runT_ok oT _ h1 h2]
    exact c_range _ (fun y g1 g2 => by
      rw [V'_pass runB runB_ok oB _ g1 g2]; exact hA y g1 g2) x h1 h2

/-- **The word the first window sends is a number or `-inf`**, on every path. -/
theorem w1_ni (V : Nat → Value) (h : W1In V) : (Kd.s .ni).Has (vFin V 1520) := by
  obtain ⟨W, hW, e⟩ := w1_file V h
  rw [e]
  exact m_has W hW

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
