-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Protocol.NamedBarPhaseKeys

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX

set_option maxRecDepth 100000 in
/-- The kernel has no `bar.arrive`. -/
theorem noBarArrive : kernel.NoBarArrive := by
  unfold Kernel.NoBarArrive
  decide +kernel

instance : Fact kernel.NoBarArrive := ⟨noBarArrive⟩

end PTX.Kernels.InklingRelDecode.Proof
