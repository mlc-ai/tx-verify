-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.FrLdL
public import Kernels.InklingRelDecode.Proof.Protocol.FrSm
public import Kernels.InklingRelDecode.Proof.Protocol.FrAccess

@[expose] public section

/-!
# Protocol layer: `Interface.FaultRest` from the value chain

* `FrLdL`: the scratch load of the softmax region reads bytes that rebuild;
* `FrSm`: `Sm.next` and `DComp.smNext` are never `none` at an event of a launched thread, and
  `faultRest_of`;
* `FrAccess`: `Tmem1.access_shape_of`, the footprint of every Tensor Memory access.
-/
