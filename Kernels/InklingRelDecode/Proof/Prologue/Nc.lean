-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow

/-- No event payload stops an active Prologue fragment. -/
public theorem no_stop {Q L g d e} (live : d.site ≠ .exit) :
    next Q L g d e ≠ some none := by
  intro stop
  cases hs : d.site <;> simp only [next,hs] at stop
  all_goals repeat' first
    | contradiction | (solve | cases stop) | (solve | simp [hs] at live) | split at stop

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
