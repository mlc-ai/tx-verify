-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PlEpiTm
public import Kernels.InklingRelDecode.Proof.Interface.PlFault

/-!
# The placement, fault and uniformity facts of the thread layer: umbrella

* `PlEpiTm`: `epiTm_of`, the epilogue's Tensor Memory base is 0 (`InputsRest.epiTm` is built).
* `PlFault`: `faultFree_of`, `Safety.Protocol.faultFree` from `FaultRest` (the softmax region's and
  the epilogue's value-dependent sites).
-/
