-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.LaterSums
import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstSum
import Kernels.TmlFa4Fwd.Proof.Softmax.RefSucc

@[expose] public section

/-! # The row sum of a softmax data state is nonnegative

A step keeps the row sum, or ends a round with the round's sum (`succ_rs`); a round's sum of
nonnegative weights on a nonnegative sum is nonnegative (`sumAfter_nonneg`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem weights_nonneg (p L g v r i) : 0 ≤ P p L g v r i := by
  unfold P probability
  split
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (by norm_num) _).le

theorem factor_nonneg (p v r) : 0 ≤ factor p v r := by
  have carry (keep : Bool) (x : ℝ) : 0 ≤ carry p v keep x := by
    unfold carry
    cases v.mf
    · exact le_rfl
    · cases keep
      · exact (Real.rpow_pos_of_pos (by norm_num) _).le
      · exact zero_le_one
  cases r with
  | first => exact zero_le_one
  | bias => exact carry _ _
  | plain => exact carry _ _

theorem sumAfter_nonneg {p L m} (hp : Pre p L m) (g : Nat) {v : V} (h : 0 ≤ v.rs) (r : Rd) :
    0 ≤ sumAfter p L g v r := by
  have hs (q : Rd) : 0 ≤ ∑ i ∈ Finset.range 128, P p L g v q i :=
    Finset.sum_nonneg fun i _ => weights_nonneg p L g v q i
  cases r with
  | first =>
    rw [sumAfter, first_sum hp g v]
    exact hs .first
  | bias =>
    rw [sumAfter, bias_sum hp g v, rowSumT_eq]
    exact add_nonneg (mul_nonneg h (factor_nonneg p v _)) (hs _)
  | plain =>
    rw [sumAfter, plain_sum hp g v, rowSumT_eq]
    exact add_nonneg (mul_nonneg h (factor_nonneg p v _)) (hs _)

set_option maxHeartbeats 4000000 in
/-- **A step keeps the row sum, or ends a round.** -/
theorem succ_rs {p L g} {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    d'.v.rs = d.v.rs ∨ ∃ r, d'.v.rs = sumAfter p L g d.v r := by
  obtain ⟨s, v, k, acc⟩ := d
  by_cases hr : ∃ r, s = .pwend r
  · obtain ⟨r, rfl⟩ := hr
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · obtain ⟨-, -, hs⟩ := afterRound_stats p L g ⟨.pwend r, v, k, acc⟩ r
        exact .inr ⟨r, hs⟩
      · exact .inl rfl
    · cases h
  · left
    cases s with
    | pwend r => exact absurd ⟨r, rfl⟩ hr
    | sld r c => cases r <;> sc_split <;> rfl
    | pst r q =>
      have hv : d'.v = v := by
        cases r <;> (match q with | 0 | 1 | 2 | 3 => ?_) <;> simp only [succ] at h <;>
          first | (cases h; rfl) | (split at h <;> cases h <;> rfl)
      rw [hv]
    | fin j =>
      fin_cases j <;> simp only [succ] at h <;> cases h <;> rfl
    | up s j => fin_cases j <;> sc_split <;> rfl
    | total s => cases s <;> sc_split <;> rfl
    | wend l => cases l <;> sc_split <;> rfl
    | barEnd l => cases l <;> sc_split <;> rfl
    | vote l => cases l <;> sc_split <;> rfl
    | pre l => cases l <;> sc_split <;> rfl
    | tiles l => cases l <;> sc_split <;> rfl
    | _ => sc_split <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
