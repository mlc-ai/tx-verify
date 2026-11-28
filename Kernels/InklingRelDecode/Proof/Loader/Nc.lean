-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow

/-- No event payload stops an active Loader fragment. -/
public theorem no_stop {L g d e} (live : d.site ≠ .dispatch) :
    next L g d e ≠ some none := by
  intro stop
  cases hs : d.site <;> simp only [next,hs] at stop
  all_goals try unfold readResult at stop
  all_goals repeat' first
    | contradiction | (solve | cases stop) | (solve | simp [hs] at live) | split at stop
  all_goals rename_i bs _; cases h : (rebuild 3 bs).toOption <;> simp [h] at stop

end PTX.Kernels.InklingRelDecode.Proof.Loader
