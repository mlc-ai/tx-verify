-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataChunk

@[expose] public section

/-! # `Counts`: the data of the final part, the staging stores

A staging store is done before the sites after its step, and every step into such a site keeps
the item (`pre_wDone`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxHeartbeats 8000000 in
theorem pre_wDone {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} {j : Fin 8} {h : Fin 2} {el : Fin 4}
    (hw : wDone d' st j h el) :
    (d.site = .fst st j h el ∨ wDone d st j h el) ∧ d'.i = d.i := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold wDone at hw ⊢
  corr_cases hn
  all_goals (try (simp at hw; done))
  all_goals simp only [Fin.ext_iff, Site.fst.injEq, and_true] at hw ⊢
  all_goals omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
