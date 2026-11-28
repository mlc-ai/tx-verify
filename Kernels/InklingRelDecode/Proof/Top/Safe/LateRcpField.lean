-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Softmax.Export.RcpLate

@[expose] public section

/-! # The reciprocal's operand is not a zero -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Assumption

variable {L : Launch} {X : Execution}

/-- **The operand of `rcp.approx` (pc 2602, register 1762) is not a zero**
(`Iface.LateValues.rcp`). -/
theorem Safe.rcp :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → t.pc = 2602 →
      ∀ x : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok x) → x ≠ 0 :=
  fun _ _ _ hl hpc => Softmax.Export.rcp_late hl hpc

end PTX.Kernels.InklingRelDecode.Proof.Top
