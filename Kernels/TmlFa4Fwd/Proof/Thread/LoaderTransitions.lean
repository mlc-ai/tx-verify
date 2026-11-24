-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX
open PTX.Kernels.TmlFa4Fwd.Loader
open DecodedObservation

noncomputable section

/-- The producer's empty-slot object is distinct from its ready object. -/
def emptyObject (l : Launch) (g : Nat) (slot : Fin 3) : Loc :=
  Prologue.initObject l (g / l.block) (emptySlot slot)

/-- A classified commit closes the pending ordinary group and retains its exact issued vectors. -/
theorem commitStep {l : Launch} {X : Execution} {g index : Nat} {e : Event} {packet : Packet}
    (he : X.get (g, index) = some e) (h : observe l g e = .commit packet) :
    let d := atPrefix l X g index
    let after := atPrefix l X g (index + 1)
    after.pendingCopies = [] ∧ after.lastCommit = some ⟨packet, d.pendingCopies.reverse⟩ := by
  rw [prefixStep he]
  exact advanceCommit h

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
