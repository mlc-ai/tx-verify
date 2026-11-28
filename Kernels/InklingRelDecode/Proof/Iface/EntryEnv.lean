-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedG

@[expose] public section

/-! # The tags of the registers at the entry of the softmax

The registers the softmax's typed windows start from, at program counter 574, with the tag each
holds there. The prologue proves that a lane that fires the barrier before the softmax has them
(`Prologue.Export.entry_tags`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX PTX.Flow.TyG

/-- The tags at the entry of the softmax (program counter 574). -/
def entryEnv : EnvF :=
  [(3, .old .pred), (177, .old .pred), (199, .old (.bits 16)), (462, .old (.bits 32)),
    (463, .dat32), (464, .old (.bits 32)), (478, .old (.bits 32)), (481, .old (.bits 32)),
    (482, .old (.bits 32)), (483, .old (.bits 32)), (484, .old (.bits 32)),
    (485, .old (.bits 32)), (486, .old (.bits 32)), (487, .old (.bits 32)),
    (490, .old (.bits 32)), (525, .old (.bits 32)), (527, .old (.bits 32)),
    (532, .old (.bits 32)), (533, .old (.bits 32)), (610, .old (.bits 32)),
    (1912, .old (.bits 32)), (2019, .old (.bits 64)), (2023, .old (.bits 64)),
    (2024, .old (.bits 64))]

end PTX.Kernels.InklingRelDecode.Proof.Iface
