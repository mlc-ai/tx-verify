-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! `Decode.prepare` computes the instructions of `instrs` from index 2709 to the end. -/

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000


theorem source_3 : (prepare Generated.FlashMlaSparseDecodeH64.module.globals source).map
    (fun p => p.instrs.drop 2709) = .ok (instrs.drop 2709) := by
  -- Stated against the closed part `instrs3`, the reduction compares only this slice.
  have h : instrs.drop 2709 = instrs3 := by kernel_rfl
  rw [h]
  kernel_rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.DecodeAudit
