-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvSingle
public import Kernels.InklingRelDecode.Proof.Protocol.KvRecords

@[expose] public section

/-!
# The KV ring's record fault freedom and the barrier records: umbrella

`Lib.KvSingle` (the single-CTA ring library at the KV slot: `full_tx_bounds`, `empty_tx_zero`,
`fault_free`), `KvRecords` (`recordsOk_of_ctas`: `Safety.Protocol.recordsOk` for the kernel's
twelve barriers per CTA). The initializations are the second tree's (`Proof2/Safety/InitAll`).
-/
