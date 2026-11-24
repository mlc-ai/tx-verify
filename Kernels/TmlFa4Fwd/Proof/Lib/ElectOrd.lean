-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Order.ElectOrdinal
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll

@[expose] public section

/-! # The elections of two lanes of a warp are met in order

Every election of the code has the full mask (`elect_full`), so it is no role's fact. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof

theorem elect_ord {L : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : ElectOrdinal L X :=
  elect_ordinal hX

end PTX.Kernels.TmlFa4Fwd.Proof
