-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskFin
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6

@[expose] public section

/-! # The scores the first window leaves, exactly

Whatever path the first window takes, the 64 score registers it leaves (`scoreRegs`) hold the exact
word of the score of their column: the raw score without a bias (`pick96`), the biased score
(`pick97`) or the biased score of the visible columns and `-inf` of the others. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- The column a score register holds. -/
def colOfSrc (r : Nat) : Nat := ((List.range 64).map srcTab).idxOf r

/-- The exact score of a column on the path the predicates choose. -/
def w1Score (V : Nat → Value) (S β : Nat → ℝ) (isc : ℝ) (cO b P : ℤ) (c : Nat) : EReal :=
  if pick96 V = true then ((S c : ℝ) : EReal)
  else if pick97 V = true then ((biased S β isc c : ℝ) : EReal)
  else if vis cO b P c then ((biased S β isc c : ℝ) : EReal) else ⊥

theorem scores_ev {W : Nat → Value} {xs : Nat → EReal} (h : PairsEv W xs) :
    ∀ r ∈ scoreRegs, Ev (runM.V' W r) (xs (colOfSrc r)) := by
  intro r hr
  refine V'_out runM runM_ok (P := fun r v => r ∈ scoreRegs → Ev v (xs (colOfSrc r)))
    (fun p hp => ?_) (scoreRegs_runM r hr) hr
  change p ∈ Gen.w1m_facts3 W at hp
  simp only [Gen.w1m_facts3, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals first
    | (intro h1; dsimp only at h1; exfalso; revert h1; decide +kernel)
    | (intro _
       first
         | exact pe_lo (h _ (by norm_num) (by norm_num))
         | exact pe_hi (h _ (by norm_num) (by norm_num)))

/-- **The first window's registers are those of the exact scores**, on every path. -/
theorem w1_pairs {V : Nat → Value} {S β : Nat → ℝ} {isc : ℝ} {cO b P : ℤ}
    (h : BiasIn V S β isc) (m : MaskIn (vA V) cO b P) :
    ∃ W, vFin V = runM.V' W ∧ PairsEv W (w1Score V S β isc cO b P) := by
  by_cases h96 : pick96 V = true
  · refine ⟨vP V, by funext r; simp [vFin, h96, vS], fun r h1 h2 => ?_⟩
    simp only [w1Score, h96, ↓reduceIte]
    rw [vP_score h1 h2]
    exact h.score r h1 h2
  by_cases h97 : pick97 V = true
  · have hA := a_exact (biasIn_vP h)
    refine ⟨runT.V' (vA V), by funext r; simp [vFin, h96, h97, vU], fun r h1 h2 => ?_⟩
    simp only [w1Score, h96, h97, ↓reduceIte]
    rw [vT_score h1 h2]
    exact hA r h1 h2
  · have hB : PairsEv (runB.V' (vA V)) (fun c => ((biased S β isc c : ℝ) : EReal)) :=
      fun r h1 h2 => by rw [vB_score h1 h2]; exact a_exact (biasIn_vP h) r h1 h2
    have hC := mask_c (V := runB.V' (vA V)) (cO := cO) (b := b) (P := P)
      (fun r hr => (mask_b m (isSub_out hr)).2.1 hr)
      ((mask_b m (r := 1139) (by decide +kernel)).2.2 rfl)
      (fun r h1 h2 => (mask_b m (pred_out h1 h2)).1 h1 h2) hB
    have hk : w1Score V S β isc cO b P = fun c =>
        if vis cO b P c then ((biased S β isc c : ℝ) : EReal) else ⊥ := by
      funext c
      simp [w1Score, h96, h97]
    refine ⟨runT.V' (runC.V' (runB.V' (vA V))), by funext r; simp [vFin, h96, h97, vM],
      fun r h1 h2 => ?_⟩
    rw [hk, vT_score h1 h2]
    exact hC r h1 h2

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
