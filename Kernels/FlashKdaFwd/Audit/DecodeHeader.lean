-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeResolved
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! `Decode.prepare` computes the environment `env` and the kernel header of
`Decoded.kernel`. -/

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000


theorem header_eq : (prepare Generated.FlashKdaFwd.module.globals source).map
    (fun p => (p.env, p.header)) = .ok (env, Decoded.metadata) := by
  rw [prepare_eq]
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
