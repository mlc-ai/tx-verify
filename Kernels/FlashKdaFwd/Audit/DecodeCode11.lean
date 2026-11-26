-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! The instructions of `instrs` from index 2816, 256 of them decode to the same slice of
`Decoded.kernel.code`. -/

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

theorem code_11 : code env 2816 ((instrs.drop 2816).take 256) =
    .ok ((Decoded.kernel.code.drop 2816).take 256) := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
