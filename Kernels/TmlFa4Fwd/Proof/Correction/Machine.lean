-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Data.Machine

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction

/-- The strict machine used by the value proofs. -/
noncomputable abbrev code := Data.code

end PTX.Kernels.TmlFa4Fwd.Proof.Correction
