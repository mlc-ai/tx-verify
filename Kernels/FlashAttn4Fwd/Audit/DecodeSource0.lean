-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! `Decode.prepare` computes the instructions of `instrs` from index 0, 1225 of them. -/

@[expose] public section

namespace PTX.Kernels.FlashAttn4Fwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

-- The kernel reduction of `prepare` resolves every nested scope of the function.
set_option maxHeartbeats 1000000

theorem source_0 : (prepare Generated.FlashAttn4Fwd.module.globals source).map
    (fun p => (p.instrs.drop 0).take 1225) = .ok ((instrs.drop 0).take 1225) := by
  -- Stated against the closed part `instrs0`, the reduction compares only this slice.
  have h : (instrs.drop 0).take 1225 = instrs0 := by kernel_rfl
  rw [h]
  kernel_rfl

end PTX.Kernels.FlashAttn4Fwd.DecodeAudit
