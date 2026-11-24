-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Spec
public import Lemmas.Execution.NoBarArrive

@[expose] public section

namespace PTX.Kernels.BlockSum

/-- The kernel has no `bar.arrive` instruction, so its executions have no `bar.arrive` event. -/
instance noBarArrive : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

end PTX.Kernels.BlockSum
