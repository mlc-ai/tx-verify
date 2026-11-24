-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataChunk

@[expose] public section

/-! # `Counts`: the data of the final part, stage 1, the statistics word

The credit of the load of `l` follows that load (which sets the word); the sites after it follow
the credit (which sets `1 / l'`) or each other; every other step keeps the word, its reading and
the item (`pre_finStat`; the reading: `CorrectionCountsDataRecip`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 8000000 in
theorem pre_finStat1 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (hst : st = 1) (h : finStat d' st) :
    ((d.site = .ldL st ∧ ∃ ac bs, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok d'.aw) ∨
      (finStat d st ∧ d'.aw = d.aw)) ∧ d'.i = d.i := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold finStat finRecip finChunk at h ⊢
  subst hst
  corr_cases hn
  all_goals (try (simp at h; done))
  all_goals simp_all


end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
