-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataRecip0
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataRecip1

@[expose] public section

/-! # `Counts`: the data of the final part, the reading of the statistics word

The credit of the load of `l` follows that load (which sets the word); the sites after it follow
the credit (which sets `1 / l'`) or each other; every other step keeps the word, its reading and
the item (`pre_finRecip`).
-/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem pre_finRecip {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (h : finRecip d' st) :
    ((((st.val = 0 ∧ d.site = .credit 4) ∨ (st.val = 1 ∧ d.site = .credit 5)) ∧
      ∃ r, recipE d.aw = .ok r ∧ d'.a = rd32 r) ∨
      (finRecip d st ∧ d'.a = d.a)) ∧ d'.aw = d.aw := by
  rcases (show st = 0 ∨ st = 1 by omega) with hst | hst
  · exact pre_finRecip0 hn hst h
  · exact pre_finRecip1 hn hst h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
