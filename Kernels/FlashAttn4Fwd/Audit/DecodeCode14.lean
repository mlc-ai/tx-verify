-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! The instructions of `instrs` from index 4046, 289 of them decode to the same slice of
`Decoded.kernel.code`. -/

@[expose] public section

namespace PTX.Kernels.FlashAttn4Fwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

theorem code_14 : code env 4046 ((instrs.drop 4046).take 289) =
    .ok ((Decoded.kernel.code.drop 4046).take 289) := by
  kernel_rfl

end PTX.Kernels.FlashAttn4Fwd.DecodeAudit
