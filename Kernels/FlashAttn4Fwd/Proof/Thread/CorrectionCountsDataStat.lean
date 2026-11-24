-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataStat0
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataStat1

@[expose] public section

/-! # `Counts`: the data of the final part, the statistics word

The credit of the load of `l` follows that load (which sets the word); the sites after it follow
the credit (which sets `1 / l'`) or each other; every other step keeps the word, its reading and
the item (`pre_finStat`; the reading: `CorrectionCountsDataRecip`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem pre_finStat {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} (h : finStat d' st) :
    ((d.site = .ldL st ∧ ∃ ac bs, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok d'.aw) ∨
      (finStat d st ∧ d'.aw = d.aw)) ∧ d'.i = d.i := by
  rcases (show st = 0 ∨ st = 1 by omega) with hst | hst
  · exact pre_finStat0 hn hst h
  · exact pre_finStat1 hn hst h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
