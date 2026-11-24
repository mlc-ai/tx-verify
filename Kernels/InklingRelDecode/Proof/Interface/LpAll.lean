-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpAll

@[expose] public section

/-!
# The protocol layer's loader runs, for the result layer

Re-exports `Protocol/LpAll.lean` (the loader's anchored run and its progress from the exit) to the
result layer, as `RdLayer.lean` does for `Protocol/RdAll.lean`. No module of the protocol layer
imports this file.
-/
