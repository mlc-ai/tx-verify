-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataChunk

@[expose] public section

/-! # `Counts`: the ballot of a running rescale

A site of a rescale (one with warp-collective `tcgen05` events still to come) follows a vote
with a nonzero ballot (`pre_rsNz`), and its steps make no ballot event (`rs_not_vote`): the last
ballot event before such a site is nonzero (`step_rsNz`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 8000000 in
theorem pre_rsNz {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) (h : 0 < tcLack d') :
    (∃ st, d.site = .vote st ∧ ∃ m a b, e.kind = .vote m a b ∧ b ≠ 0) ∨ 0 < tcLack d := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  corr_cases hn
  all_goals (try (simp [tcLack] at h; done))
  all_goals (try (right; simp [tcLack]; omega))
  all_goals simp_all

theorem rs_not_vote {L : Launch} {g : Nat} {d : D} {e : Event} (h : 0 < tcLack d)
    (hev : Ev L g d e) : isVote e = false := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨pc, k⟩ := e
  obtain ⟨site, i, t, aw, a, o⟩ := d
  cases site <;> simp only [tcLack, Nat.lt_irrefl] at h <;> simp only at hk
  all_goals first
    | (obtain ⟨_, hk⟩ := hk; subst hk; rfl)
    | (subst hk; rfl)

theorem step_rsNz {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}
    (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (h : 0 < tcLack d → ∃ v < es.length, ∃ pc m a b, es[v]? = some ⟨pc, .vote m a b⟩ ∧ b ≠ 0 ∧
      (es.take v).countP isVote + 1 = es.countP isVote) :
    0 < tcLack d' → ∃ v < (es ++ [e]).length, ∃ pc m a b,
      (es ++ [e])[v]? = some ⟨pc, .vote m a b⟩ ∧ b ≠ 0 ∧
      ((es ++ [e]).take v).countP isVote + 1 = (es ++ [e]).countP isVote := by
  intro h'
  rcases pre_rsNz hn h' with ⟨st, -, m, a, b, hk, hb⟩ | hl
  · refine ⟨es.length, by simp, e.pc, m, a, b, ?_, hb, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk]
    · rw [snoc_take le_rfl, List.take_length, List.countP_append]
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp [isVote]
  · obtain ⟨v, hv, pc, m, a, b, hg, hb, hc⟩ := h hl
    refine ⟨v, by simp; omega, pc, m, a, b, by rw [snoc_get hv, hg], hb, ?_⟩
    rw [snoc_take hv.le, List.countP_append, hc]
    simp [rs_not_vote hl hev]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
