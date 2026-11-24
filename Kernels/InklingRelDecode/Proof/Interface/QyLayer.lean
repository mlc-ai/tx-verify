-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.QyBar

@[expose] public section

/-! # What the result layer's `Qy` files use of the protocol layer

The softmax threads' states that a lane's polls of `p_ready` imply (`Qy.arrivals_of_polls`,
`Qy.tmemSt_of_arrivals`) and the barrier-0 counts at `bar20` (`Qy.exit_bound20`,
`Qy.b128_of20`). -/
