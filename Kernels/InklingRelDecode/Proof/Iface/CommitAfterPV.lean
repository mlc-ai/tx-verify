-- SPDX-License-Identifier: Apache-2.0
-- iface: CommitAfterPV producer=W status=row-proved domain=complete
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Iface

/-- The elected PV issuer reaches its final notification in a complete execution. -/
def CommitAfterPV (L : Launch) (X : Execution) : Prop :=
  Complete L X → ∀ {g k pc sp}, X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩ →
    pc = 2546 ∨ pc = 2548 → ∃ j > k, ∃ sp', X.get (g,j) = some ⟨2553,.tc (.commit sp')⟩

end PTX.Kernels.InklingRelDecode.Proof.Iface
