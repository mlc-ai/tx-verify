-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Places

@[expose] public section

/-! # The MMA warp's K/V ring counts

At every place of the pipeline, the MMA warp's commits to the empty barrier of K/V slot `j`
(on the lane that commits) are at most its successful polls of the full barrier of slot `j`
(`commit_le_acq`): each of the ring's release points follows its acquisition point
(`ringRel_le_ringAcq`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma

noncomputable section

theorem pq_mono {x y : Nat} (q r : Nat) (hxy : x ≤ y)
    (hin : (20 ≤ x ∧ x < 60) ↔ (20 ≤ y ∧ y < 60)) : pq y q r ≤ pq x q r := by
  unfold pq
  by_cases hx : 20 ≤ x ∧ x < 60
  · have hy := hin.mp hx
    simp only [hx, hy, and_self, ite_true]
    split_ifs <;> omega
  · have hy : ¬ (20 ≤ y ∧ y < 60) := fun h => hx (hin.mpr h)
    simp only [hx, hy, ite_false]
    split_ifs <;> omega

theorem ringRel_le_ringAcq (q r : Nat) : ringRel q r ≤ ringAcq q r := by
  have h1 := pq_mono q r (show 2 ≤ 16 by omega) (by omega)
  have h2 := pq_mono q r (show 20 ≤ 43 by omega) (by omega)
  have h3 := pq_mono q r (show 29 ≤ 49 by omega) (by omega)
  have h4 := pq_mono q r (show 64 ≤ 81 by omega) (by omega)
  simp only [ringRel, ringAcq]
  omega

theorem ringCount_mono {n n' : Nat} (h : n ≤ n') (s : Nat) : ringCount n s ≤ ringCount n' s := by
  simp only [ringCount]
  omega

/-- **The commits to an empty slot are at most the successful polls of its full slot.** -/
theorem commit_le_acq (q r j : Nat) (hj : j < 3) :
    commitAt q r (56 + 8 * j) ≤ acqAt q r (32 + 8 * j) := by
  have h := ringCount_mono (ringRel_le_ringAcq q r) j
  have e1 : (56 + 8 * j - 56) / 8 = j := by omega
  have e2 : (32 + 8 * j - 32) / 8 = j := by omega
  simp only [commitAt, acqAt]
  interval_cases j <;> simp_all

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
