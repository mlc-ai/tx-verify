-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow

/-- No event payload stops an active Softmax fragment. -/
public theorem no_stop {ent L g d e} (live : d.site ≠ .epilogue) :
    next ent L g d e ≠ some none := by
  intro stop
  cases hs : d.site <;> simp only [next,hs] at stop
  all_goals repeat' first | (solve | cases stop) | (solve | simp [hs] at live) | split at stop

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
