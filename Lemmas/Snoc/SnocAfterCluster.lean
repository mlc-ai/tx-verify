-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocBlockingConsistent

@[expose] public section

/-! Appending a non-shuffle event to a thread whose last event is a cluster operation. That
last event returns once the appended event exists, so its readiness is the only release the
append needs, and the appended event creates no shuffle obligation. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

theorem snoc_rendezvous_after_cluster (hX : Consistent L K A mem0 X) {pc : Nat} {c : ClusterOp}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster c⟩)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) :
    (LastReady L X g ↔ Ready L X (g, (X.tr g).length - 1)) ∧ ShflOk L (X.snoc g e r) := by
  refine ⟨⟨fun h => h pc (.cluster c) hlast rfl, fun h _ _ _ _ => h⟩, snoc_shflOk hX.shfl hns⟩

end
end PTX
