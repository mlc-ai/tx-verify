-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
public import Kernels.TmlFa4Fwd.Proof.Softmax.DataStoreSite
import Kernels.TmlFa4Fwd.Proof.SmWarp.NumAll
import Kernels.TmlFa4Fwd.Proof.Softmax.DataStore

@[expose] public section

/-! # The softmax fragment's numeric steps and data stores -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

theorem numSteps (hp : Pre p L m) : NumAll p L := numAll hp

theorem storeSafe (hp : Pre p L m) (g : Nat) : Softmax.DataStoreSafe p L g :=
  Softmax.dataStoreSafe hp g

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
