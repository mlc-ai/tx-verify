-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.NoTma
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.FaultFree
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime

@[expose] public section

/-! # ERR-OBJECT-LIFETIME (the parts other than initialization and publication): the rest of the
mbarrier object lifetime (`TmaRest`)

`Safe.tmaRest` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-OBJECT-LIFETIME (the parts other than initialization and publication)**: no record of an
object faults (`no_fault`), no access meets an object's bytes, no two copies of a `cp.async` group
overlap and no copy is masked. -/
theorem Safe.tmaRest (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    TmaRest l m X where
  fault := fun o r hr _ => no_fault hp hX (launchFollow hp hX) o r hr
  acc := acc_free hp hX (launchFollow hp hX)
  overlap := no_overlap hp hX (launchFollow hp hX)
  masked := no_masked hp hX (launchFollow hp hX)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
