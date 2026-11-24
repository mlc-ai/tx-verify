-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeResolved
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! `Decode.prepare` computes the instructions of `instrs` from index 2302, 2302 of them. -/

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000


theorem source_1 : (prepare Generated.TmlFa4Fwd.module.globals source).map
    (fun p => (p.instrs.drop 2302).take 2302) = .ok ((instrs.drop 2302).take 2302) := by
  -- Stated against the closed part `instrs1`, the reduction compares only this slice.
  have h : (instrs.drop 2302).take 2302 = instrs1 := by kernel_rfl
  rw [h]
  rw [prepare_eq]
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
