-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Masked
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.LaterSums
import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstSum
import Kernels.TmlFa4Fwd.Proof.Softmax.RefSucc

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A round whose maximum is minus infinity leaves a zero running sum. -/
theorem sumAfter_of_bot {p L m} (hp : Pre p L m) (g : Nat) (v : V) (r : Rd)
    (h : maximum p L g v r = ⊥) : sumAfter p L g v r = 0 := by
  have zero (q : Rd) (hm : ∀ i < 128, score p L g v q i = ⊥) :
      ∑ i ∈ Finset.range 128, P p L g v q i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [P, probability, hm i (Finset.mem_range.mp hi), ite_true]
  cases r with
  | first =>
    rw [sumAfter, first_sum hp]
    exact zero _ fun _ hi => first_masked p L g v h hi
  | bias =>
    obtain ⟨hf, hm⟩ := bias_masked p L g v h
    rw [sumAfter, bias_sum hp, rowSumT_eq, zero _ hm]
    simp only [factor, carry, hf, Bool.cond_false, mul_zero, add_zero]
  | plain => exact (EReal.coe_ne_bot _ h).elim

/-- A continuing step either carries all running statistics or replaces all three together. -/
theorem succ_stats {p L g} {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    (d'.v.mf = d.v.mf ∧ d'.v.mr = d.v.mr ∧ d'.v.rs = d.v.rs) ∨
      ∃ r, d.site = .pwend r ∧ d'.v.mf = finE (maximum p L g d.v r) ∧
        d'.v.mr = (maximum p L g d.v r).toReal ∧ d'.v.rs = sumAfter p L g d.v r := by
  obtain ⟨s, v, k, acc⟩ := d
  by_cases hr : ∃ r, s = .pwend r
  · obtain ⟨r, rfl⟩ := hr
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · exact .inr ⟨r, rfl, afterRound_stats p L g _ r⟩
      · exact .inl ⟨rfl,rfl,rfl⟩
    · cases h
  · left
    cases s with
    | pwend r => exact absurd ⟨r, rfl⟩ hr
    | sld r c => cases r <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | pst r q =>
      have hv : d'.v = v := by
        cases r <;> (match q with | 0 | 1 | 2 | 3 => ?_) <;> simp only [succ] at h <;>
          first | (cases h; rfl) | (split at h <;> cases h <;> rfl)
      rw [hv]; exact ⟨rfl,rfl,rfl⟩
    | fin j => fin_cases j <;> simp only [succ] at h <;> cases h <;> exact ⟨rfl,rfl,rfl⟩
    | up s j => fin_cases j <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | total s => cases s <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | wend l => cases l <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | barEnd l => cases l <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | vote l => cases l <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | pre l => cases l <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | tiles l => cases l <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
    | _ => sc_split <;> exact ⟨rfl,rfl,rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
