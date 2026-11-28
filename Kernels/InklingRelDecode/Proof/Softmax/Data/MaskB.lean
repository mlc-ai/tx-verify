-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskExact

@[expose] public section

/-! # The differences run of the mask

The run of pcs 1467 to 1599 writes, for each of the 64 columns of the thread, either the predicate
of the column's test (columns 28 to 63) or the signed difference the next run tests (the others). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- **What the run writes**: the predicates and the differences. -/
def BOut (cO b P : ℤ) (r : Nat) (v : Value) : Prop :=
  (98 ≤ r → r < 134 → v = .pred (vis cO b P (colOfPred r))) ∧
  (IsSub r → IW v (zc cO b P (colOfSub r))) ∧ (r = 1139 → IW v (zc cO b P 1))

theorem iw_of {v : Value} {z z' : ℤ} (h : IW v z) (e : z = z') : IW v z' := e ▸ h

theorem mask_b {W : Nat → Value} {cO b P : ℤ} (m : MaskIn W cO b P) {r : Nat}
    (hr : r ∈ runB.outs) : BOut cO b P r (runB.V' W r) := by
  refine V'_out runB runB_ok (P := BOut cO b P) (fun p hp => ?_) hr
  change p ∈ Gen.w1b_facts5 W at hp
  simp only [Gen.w1b_facts5, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals refine ⟨fun h1 h2 => ?_, fun h1 => ?_, fun h => ?_⟩
  all_goals dsimp only at *
  all_goals try (exfalso; first | omega | (simp only [IsSub] at *; omega))
  all_goals first
    | (apply gt_p
       · repeat' first
           | apply sub_iw | apply add_iw | exact m.col | exact m.base
           | apply lo_iw m | apply hi_iw m | decide
       · simp only [vis, zc, colOfPred]
         first | (norm_num; done) | (norm_num; ring_nf))
    | (apply iw_of
       · repeat' first
           | apply sub_iw | apply add_iw | exact m.col | exact m.base
           | apply lo_iw m | apply hi_iw m | decide
       · simp only [zc, colOfSub]
         first | (norm_num; done) | (norm_num; omega))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
