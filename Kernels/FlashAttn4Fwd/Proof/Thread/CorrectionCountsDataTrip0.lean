-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataChunk

@[expose] public section

/-! # `Counts`: the data of a trip, stage 0

A rescale chunk's wait follows its load (which sets the chunk's values) and its store the wait
(`pre_rsChunk0`); the vote follows the load of `α` (which sets the word) and the rescale's sites
follow the vote or each other (`pre_rsSite0`); every such step keeps the item and the trip. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 8000000 in
theorem pre_rsChunk0 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (hst : st = 0) {j : Fin 8}
    (h : rsChunk d' st j) :
    ((d.site = .rld st j ∧ ∃ a, e.kind = .tc (.ld a d'.o .s32x32b)) ∨
      (rsChunk d st j ∧ d'.o = d.o)) ∧
      d'.i = d.i ∧ d'.t = d.t := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold rsChunk at h ⊢
  subst hst
  corr_cases hn
  all_goals (try (simp at h; done))
  all_goals simp_all

set_option maxHeartbeats 8000000 in
theorem pre_rsSite0 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (hst : st = 0) (h : rsSite d' st) :
    ((d.site = .ldA st ∧ ∃ ac bs, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok d'.aw) ∨
      (rsSite d st ∧ d'.aw = d.aw)) ∧ d'.i = d.i ∧ d'.t = d.t := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold rsSite rsChunk at h ⊢
  subst hst
  corr_cases hn
  all_goals (try (simp at h; done))
  all_goals simp_all

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
