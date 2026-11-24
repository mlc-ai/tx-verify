-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RdAll

@[expose] public section

/-!
# The protocol layer's anchored runs, for the result layer

Re-exports `Protocol/RdAll.lean` (the softmax thread's poll counts along its states, the MMA lane's
anchored run and commit numbering, the uniqueness of its states at one site and iteration) to the
result layer. No module of the protocol layer imports this file.
-/
