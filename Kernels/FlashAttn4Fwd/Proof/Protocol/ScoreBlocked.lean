-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Protocol.MbarCommitObj
public import Lemmas.Protocol.UnitObjBlocker
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyObj

@[expose] public section

/-! # Who blocks the S-full and O-full objects

Stage `st`'s S-full object (`sFullBar`) and O-full object (`oFullBar`) of each CTA have count 1
and are completed by the MMA thread's commits alone (`SFullFacts`, `OFullFacts`: no thread
arrives and no copy completes on them; `TmemFacts`: no bulk copy, cancellation request or
invalidation). Their histories start with their only initialization (`SFullInit`, `OFullInit`,
premises, as the other table barriers' `InitFirst`).

* **SBlocked**, **OBlocked** (`sBlocked`, `oBlocked`): the arrival units of the object's history
  are its phase number (`MbarRing.Blocker.commitObj_blocked`), so its current phase awaits the
  notification of the next commit.
* **PBlocked** (`pBlocked`): a P-ready object is a unit object of its 512 producers (`pObj`), so
  some producer (`pThread`) has recorded no more arrivals on it than its phase number
  (`MbarRing.Unit.Obj.blocked`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof MBarrier

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The initialization premise** of the S-full objects (count 1). -/
def SFullInit (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 → PairTmaRing.InitFirst X (sFullBar L c st) 1

/-- **The initialization premise** of the O-full objects (count 1). -/
def OFullInit (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 → PairTmaRing.InitFirst X (oFullBar L c st) 1

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
