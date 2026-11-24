-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! The instructions of `instrs` from index 1024, 256 of them decode to the same slice of
`Decoded.kernel.code`. -/

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

theorem code_4 : code env 1024 ((instrs.drop 1024).take 256) =
    .ok ((Decoded.kernel.code.drop 1024).take 256) := by
  kernel_rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.DecodeAudit
