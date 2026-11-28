-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Flow

/-- No event payload stops an active Dispatch fragment. -/
public theorem no_stop {L g d e} (live : d.site ≠ .loaderEntry ∧ d.site ≠ .mmaEntry) :
    next L g d e ≠ some none := by
  intro stop
  cases hs : d.site <;> simp only [next,hs] at stop
  all_goals repeat' first | (solve | cases stop) | (solve | simp [hs] at live) | split at stop
  all_goals rename_i bs _; cases h : readTarget bs <;> simp [h] at stop

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
