-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Audit.DecodePrep
-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.
import all Init.Data.ToString.Extra
import all Init.Data.Repr

/-! `Decode.prepare` computes the environment `env` and the kernel header of
`Decoded.kernel`. -/

@[expose] public section

namespace PTX.Kernels.FlashAttn4Fwd.DecodeAudit

open PTX PTX.Decode

set_option maxRecDepth 100000

-- The kernel reduction of `prepare` resolves every nested scope of the function.
set_option maxHeartbeats 1000000

theorem header_eq : (prepare Generated.FlashAttn4Fwd.module.globals source).map
    (fun p => (p.env, p.header)) = .ok (env, { Decoded.kernel with code := [] }) := by
  kernel_rfl

end PTX.Kernels.FlashAttn4Fwd.DecodeAudit
