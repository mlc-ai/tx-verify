-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskB

@[expose] public section

/-! # The select run of the mask

The run of pcs 1600 to 1755 replaces the score of each column by `-inf` unless its test passed. On
exact scores `xs` and the differences and predicates the previous run left, the pairs are exact
pairs of the scores of the columns that pass (`vis`) and `-inf`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- **The select run on exact scores.** -/
theorem mask_c {V : Nat → Value} {cO b P : ℤ} {xs : Nat → EReal}
    (hs : ∀ r, IsSub r → IW (V r) (zc cO b P (colOfSub r))) (h1139 : IW (V 1139) (zc cO b P 1))
    (hp : ∀ r, 98 ≤ r → r < 134 → V r = .pred (vis cO b P (colOfPred r)))
    (hx : PairsEv V xs) : PairsEv (runC.V' V) (fun c => if vis cO b P c then xs c else ⊥) := by
  intro r h1 h2
  have hm : r ∈ runC.outs := by
    have : ∀ r, 2447 ≤ r → r < 2479 → r ∈ runC.outs := by decide +kernel
    exact this r h1 h2
  refine V'_out runC runC_ok (P := fun r v => 2447 ≤ r → r < 2479 →
    PE v ((fun c => if vis cO b P c then xs c else ⊥) (2 * (r - 2447)))
      ((fun c => if vis cO b P c then xs c else ⊥) (2 * (r - 2447) + 1))) ?_ hm h1 h2
  intro p hq
  change p ∈ Gen.w1c_facts5 V at hq
  simp only [Gen.w1c_facts5, List.mem_cons, List.not_mem_nil, or_false] at hq
  repeat' (rcases hq with rfl | hq)
  all_goals
    intro _ _
    dsimp only
    refine pe_join ?_ ?_ <;> apply selp_ev' (by decide)
    all_goals first
      | exact pe_lo (hx _ (by norm_num) (by norm_num))
      | exact pe_hi (hx _ (by norm_num) (by norm_num))
      | exact hp _ (by norm_num) (by norm_num)
      | (apply gt_p
         · exact hs _ (by decide)
         · simp only [vis, zc, colOfSub]
           norm_num)
      | (apply lt_p
         · exact h1139
         · rfl)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
