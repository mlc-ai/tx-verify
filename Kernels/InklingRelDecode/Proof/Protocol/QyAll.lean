-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.QyBar

@[expose] public section

/-! # The protocol layer's `Qy` files

* `QyBar`: the softmax threads' states that a lane's polls of `p_ready` imply
  (`arrivals_of_polls`, `bar21_of_arrivals`, `tmemSt_of_arrivals`) and the barrier-0 counts at
  `bar20` (`exit_bound20`, `b128_of20`), on every consistent execution. -/
