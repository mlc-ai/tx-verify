-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FrBias
public import Kernels.InklingRelDecode.Proof.Interface.FrShfl
public import Kernels.InklingRelDecode.Proof.Interface.FrNnSt
public import Kernels.InklingRelDecode.Proof.Interface.FrEpi
public import Kernels.InklingRelDecode.Proof.Interface.FrTcData

@[expose] public section

/-!
# Interface layer: value facts for `Interface.FaultRest`

* `FrBias`: the bytes of the softmax region's bias loads rebuild;
* `FrShfl`: the exchanges of the lazy-rescale test have outcomes (`shfl_min_ok`, `shfl11_ok`,
  `shfl12_ok`);
* `FrNnSt`: `Sm.NnInv` at every softmax state, `exit_noFault`;
* `FrEpi`: the epilogue's zero test and reciprocal have outcomes (`epi_wait_ok`);
* `FrTcData`: the states that issue a `tcgen05.ld` or `tcgen05.st` with their address and shape.
-/
