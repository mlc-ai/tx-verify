-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.LateThread

public section

/-! # The entry of the epilogue, as importers see it

`EpiAt` (`Common.LateThread`) states the lane's state at its first epilogue event on the value
thread machine. Its statement names that machine, so the exports of the softmax and the epilogue
(and the glue above them) name it through `EpiEntry`, whose body only the two exports open
(`import all`). -/

namespace PTX.Kernels.InklingRelDecode.Proof

/-- **The lane enters the epilogue typed** at its event `i` (`EpiAt`). -/
def EpiEntry (Q : Params) (L : Launch) (X : Execution) (g i : Nat) : Prop := EpiAt Q L X g i

end PTX.Kernels.InklingRelDecode.Proof
