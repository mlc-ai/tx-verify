-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.SwStore
public import Kernels.InklingRelDecode.Proof.Result.SwPTile

@[expose] public section

/-!
# The softmax region's rescale and probability words in the result layer: umbrella

`Thread/SwShape` (the event shapes of the rescale load and store: `Sm.shape_ldO`, `shape_stO`),
`Interface/SwStO` (the state at the rescale store follows the load: `Sv.stO_pred`),
`Interface/SwTcSt` (the program's two `tcgen05.st` instructions and the state before one:
`Interface.tcst_event_state`), `Result/SwStore` (`Rs.store_of`: the `store` field of
`Rs.OAccPrem` for `Out.alphaRow`, from the premises `OLoadSrc`, `SmBaseZero`, `OStIter`),
`Result/SwPTile` (`Rs.pv_aTmem`, `Rs.pv_a_cell`: the Tensor Memory A-operand decode;
`Rs.pTile_of`: `Out.Inputs.pTile` from the premises `PReadSrc`, `SmBaseZero`).
The umbrella is not imported by `OutAll`, `RsAll` or `SvAll`.
-/
