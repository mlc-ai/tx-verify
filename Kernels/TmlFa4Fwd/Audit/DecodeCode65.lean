-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! The instructions of `instrs` from index 4160, 64 of them decode to the same slice of
`Decoded.kernel.code`. -/

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

theorem code_65 : code env 4160 ((instrs.drop 4160).take 64) =
    .ok ((Decoded.kernel.code.drop 4160).take 64) := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
