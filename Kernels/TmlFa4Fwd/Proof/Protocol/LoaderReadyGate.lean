-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReady
public import Kernels.TmlFa4Fwd.Proof.Protocol.MmaReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy
open Thread.Loader

noncomputable section

/-- Reusing a slot past the acquired generation depends on that acquire.
The producer ordinal is taken from its abstract publication history. -/
def CausalReuse (l : Launch) (X : Execution) (wait : EvId) (slot : Fin 3)
    (phase : Nat) : Prop :=
  ∀ issue, X.AsyncArrive issue (readyObject l wait.1 slot) true →
    X.async.arrived issue = true → phase < generation l X issue slot →
    Relation.TransGen (DepStep l kernel X) (.thread wait, true) (.async issue .arriveOn, false)

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
