-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! The instructions of `instrs` from index 1536, 256 of them decode to the same slice of
`Decoded.kernel.code`. -/

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

theorem code_6 : code env 1536 ((instrs.drop 1536).take 256) =
    .ok ((Decoded.kernel.code.drop 1536).take 256) := by
  kernel_rfl

end PTX.Kernels.InklingRelDecode.DecodeAudit
