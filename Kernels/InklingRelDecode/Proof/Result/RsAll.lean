-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RsOSource
public import Kernels.InklingRelDecode.Proof.Result.RsOAcc
public import Kernels.InklingRelDecode.Proof.Result.RsWords

@[expose] public section

/-!
# The result layer's protocol-level premises, second part: umbrella

`RsEpiLoad` (the epilogue's load event with its state and the poll of `o_final` before it),
`RsOSource` (`Out.Inputs.oSource` for the epilogue's own load: `OSource`, `oSource_of`),
`RsOAcc` (`Out.Inputs.oAcc`: `oAcc_of`; the orders of `OAcc.base`, the values from `OAccPrem`),
`RsWords` (`Out.Inputs.mmaWords` from `BaseWordRead` and `NumWordRead`).
The thread-layer half of `OAcc.base` and the end of the MMA warp's loop are
`Interface/RsMmaBack.lean` (`pv_base_pred`, `exists_pv7`, `between_bef`, `fin_iter`); the MMA
lane's elections are `Interface/RsElect.lean` (`lead_of_pv0`, `lead_of_finCommit`).
-/
