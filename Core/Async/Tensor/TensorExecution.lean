-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events
public import Core.MBarrier.AsyncMBarrier

@[expose] public section

namespace PTX
noncomputable section

/-! ## DEP-TENSOR-LOAD-ORIGIN — tensor effects belong to actual instruction instances
Statement: Every recorded tensor load copy belongs to an actual issue with the same descriptor,
  coordinates, destination, mbarrier, scope and CTA group, including each per-destination copy of a
  multicast load. Its descriptor is valid and its effects and routing obey the rules of a tensor
  load.

Defs: TensorOk

Source:
- §9.7.10.28.5.3 (asynchronous copy initiated by instruction)

Direction: reading

Applies: 1D–5D tiled and 2D `.tile::gather4` tensor loads, including each per-destination copy of a
  `.multicast::cluster` load

Premises: Every recorded effect identifies an existing issue with exactly the same descriptor,
  coordinates, destination, mbarrier, scope and CTA-group modifier.

Effect: Consistent.tensor and the tensor case of `AsyncCopy.Notifies` (OBJ-MBAR-OBSERVE). Tensor
  notifications resolve through objectAction and ObjectsOk requires their history entries. An
  issue may have no observation yet. Missing observation denotes no recorded effects. It also
  denotes no completed operation. AsyncDrained requires its notification before kernel
  completion.
-/
/-- Every recorded tensor load of `X` belongs to an actual issue and has a valid descriptor, valid
effects and valid routing. -/
def TensorOk (L : Launch) (X : Execution) : Prop :=
  ∀ i observation, X.tensor i = some observation →
    (∃ mapAddress, X.TensorIssue i mapAddress observation.spec) ∧
    TensorCopy.CopyOk observation.spec observation.effects ∧
    TensorCopy.RoutingOk L (i.1 / L.block) observation.spec ∧
    TensorDescriptor.Valid observation.spec.descriptor

end
end PTX
