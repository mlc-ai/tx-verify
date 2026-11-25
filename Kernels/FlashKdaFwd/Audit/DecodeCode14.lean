-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! The instructions of `instrs` from index 3584 to the end decode to the same slice of
`Decoded.kernel.code`. -/

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

theorem code_14 : code env 3584 (instrs.drop 3584) = .ok (Decoded.kernel.code.drop 3584) := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
