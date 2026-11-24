-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.RdShape
public import Kernels.InklingRelDecode.Proof.Thread.SwShape
public import Kernels.InklingRelDecode.Proof.Interface.All

@[expose] public section

/-!
# Thread-layer event shapes of the softmax region, for the layers above

Re-exports `Sm.shape_waitLdO` (`Thread/RdShape.lean`) through the interface.
-/
