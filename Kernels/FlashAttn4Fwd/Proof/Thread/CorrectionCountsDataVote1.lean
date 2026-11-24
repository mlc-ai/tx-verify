-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataChunk

@[expose] public section

/-! # `Counts`: the data of a trip's rescale, stage 1

A rescale's store of chunk `j` is done before the sites after its step (`pre_rsStored1`); the
sites after the vote follow the vote (to the first chunk's load when the ballot is not zero, to
the O-free arrival otherwise) or each other, the O-free arrival after the rescale's wait
(`pre_rsAfterVote1`); every such step keeps the item, the trip, the word and its reading. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 8000000 in
theorem pre_rsStored1 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (hst : st = 1) {j : Fin 8}
    (h : rsStored d' st j) :
    (d.site = .rst st j ∨ rsStored d st j) ∧ d'.i = d.i ∧ d'.t = d.t := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold rsStored at h ⊢
  subst hst
  corr_cases hn
  all_goals (try (simp at h; done))
  all_goals simp only [Fin.ext_iff, Site.rst.injEq, and_true] at h ⊢
  all_goals omega

set_option maxHeartbeats 8000000 in
theorem pre_rsAfterVote1 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (hst : st = 1) (h : rsAfterVote d' st) :
    ((d.site = .vote st ∧ ∃ m a b, e.kind = .vote m a b ∧
        ((d'.site = .rld st 0 ∧ b ≠ 0) ∨ (d'.site = .oFree st false ∧ b = 0))) ∨
      (rsAfterVote d st ∧ (d'.site = .oFree st false → d.site = .rwait st))) ∧
      d'.i = d.i ∧ d'.t = d.t ∧ d'.aw = d.aw ∧ d'.a = d.a := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold rsAfterVote at h ⊢
  subst hst
  corr_cases hn
  all_goals (try (simp at h; done))
  all_goals simp_all

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
