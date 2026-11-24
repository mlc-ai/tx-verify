-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.MmaReadyOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.MmaReady
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy Thread.Mma
open Thread.Mma.Observation (readyObject)
open Prologue (warpIndex)

/-- Every actual MMA lane follows the three-slot sequence of successful ready operands. -/
theorem followsOperands {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hw : warpIndex l g = 12) : FollowsOperands l X g := by
  intro index slot parity acquire scope hPoll
  obtain ⟨hSlot, hParity⟩ := readyOperandAtPrefix hp hX hw hPoll
  exact ⟨Fin.ext hSlot, hParity⟩

/-- The abstract ring counter and parity describe all actual successful MMA ready polls. -/
theorem followsRing {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hw : warpIndex l g = 12) : FollowsRing l X g :=
  (followsOperands hp hX hw).followsRing

end PTX.Kernels.TmlFa4Fwd.Protocol.MmaReady

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.MbarRing
open Prologue (warpIndex)

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
