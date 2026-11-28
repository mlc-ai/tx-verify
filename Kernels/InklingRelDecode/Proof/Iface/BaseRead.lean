-- SPDX-License-Identifier: Apache-2.0
-- iface: BaseRead producer=C status=proved domain=consistent
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.Regs

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

def BaseRead (L : Launch) (X : Execution) : Prop :=
  ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
    a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
    bs = (PTX.Proof.b32 0).toBytes.map some

end PTX.Kernels.InklingRelDecode.Proof.Iface
