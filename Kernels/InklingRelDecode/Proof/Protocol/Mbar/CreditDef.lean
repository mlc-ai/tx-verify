-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarTime
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarHistory
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.Sched PTX.MbarRing MbarRow

/-- A waiting consumer permits at most one outstanding issue on its own slot.
The producer can already have issued the notification that will unblock it. -/
def Credit (L : Launch) (m : Mem0) (X : Execution) (o : Object) :=
  ∀ c g, Waiting L m X o c g → (X.tr (KV.leader L X c 7)).countP (commitsTo (o.loc L c))
    ≤ okPolls (o.loc L c) (X.tr g)+1

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
