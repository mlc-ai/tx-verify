-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Round
public import Lemmas.Real.OnlineFold

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
noncomputable section

/-- The code's two-lane reduction adds its seed and each of the 128 columns exactly once. -/
theorem rowSumT_eq (seed : ℝ) (w : Nat → ℝ) :
    rowSumT seed w = seed + ∑ k ∈ Finset.range 128, w k := by
  have sumList (n : Nat) : ∑ k ∈ Finset.range n, w k = ((List.range n).map w).sum := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ]; simp
  rw [sumList]
  unfold rowSumT
  conv_rhs => dsimp only [List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  abel

/-- The protocol's fold from the machine's per-round reference maxima and accumulator recurrence.
A zero rescale is allowed when every previous score was masked. -/
theorem fold_of_rounds (p : Params) (n : Nat) (hn : 0 < n) (M : Nat → EReal)
    (x : Nat → Nat → EReal) (f s : Nat → ℝ)
    (h0 : s 0 = rowSumT 0 (probability p (M 0) ∘ x 0))
    (hs : ∀ u, u+1 < n → s (u+1) = rowSumT (s u * f (u+1)) (probability p (M (u+1)) ∘ x (u+1)))
    (hf : ∀ u, u+1 < n → f (u+1) = scale p (M (u+1)) / scale p (M u) ∨
      ∀ v ≤ u, ∀ k < 128, x v k = ⊥)
    (hle : ∀ u < n, f u ≤ 1) :
    PTX.Numeric.OnlineFold.Fold n (fun u k => weight p (x u k))
      (fun u k => probability p (M u) (x u k)) (scale p ∘ M) f (s (n-1)) := by
  have pos (u : Nat) : 0 < scale p (M u) := Real.rpow_pos_of_pos (by norm_num) _
  have mass (u : Nat) : ∑ k ∈ Finset.range 128, (probability p (M u) ∘ x u) k =
      scale p (M u) * ∑ k ∈ Finset.range 128, weight p (x u k) := by
    simp only [Function.comp_apply, probability_eq, Finset.mul_sum]
  have vanishes (u : Nat) (hm : ∀ v ≤ u, ∀ k < 128, x v k = ⊥) :
      ∑ v ∈ Finset.range (u+1), ∑ k ∈ Finset.range 128, weight p (x v k) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro k hk
    simp [weight, hm v (Nat.le_of_lt_succ (Finset.mem_range.mp hv)) k (Finset.mem_range.mp hk)]
  have sums (u : Nat) (hu : u < n) : s u = scale p (M u) *
      ∑ v ∈ Finset.range (u+1), ∑ k ∈ Finset.range 128, weight p (x v k) := by
    induction u with
    | zero => rw [h0, rowSumT_eq, mass, zero_add, Finset.sum_range_one]
    | succ u ih =>
      rw [hs u hu, rowSumT_eq, mass, ih (by omega), Finset.sum_range_succ _ (u+1), mul_add]
      congr 1
      rcases hf u hu with h | h
      · rw [h]
        field_simp [(pos u).ne']
      · rw [vanishes u h]; ring
  refine ⟨fun u _ => pos u, fun u _ k _ => probability_eq p _ _, ?_, hle, ?_⟩
  · intro u hu
    exact (hf u hu).imp_right fun h v hv k hk => by simp [weight, h v hv k hk]
  · simpa [Nat.sub_add_cancel hn] using sums (n-1) (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
