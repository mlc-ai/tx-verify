-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! `Decode.prepare` computes the instructions of `instrs` from index 714, 714 of them. -/

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000


theorem source_1 : (prepare Generated.InklingRelDecode.module.globals source).map
    (fun p => (p.instrs.drop 714).take 714) = .ok ((instrs.drop 714).take 714) := by
  -- Stated against the closed part `instrs1`, the reduction compares only this slice.
  have h : (instrs.drop 714).take 714 = instrs1 := by kernel_rfl
  rw [h]
  kernel_rfl

end PTX.Kernels.InklingRelDecode.DecodeAudit
