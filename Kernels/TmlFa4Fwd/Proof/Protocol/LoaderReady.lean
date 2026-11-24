-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy
open Thread.Loader

noncomputable section
open Classical

/-- The producer's generation before issuing its next publication for this slot. -/
def generation (l : Launch) (X : Execution) (issue : EvId) (slot : Fin 3) : Nat :=
  (atPrefix l X issue.1 issue.2).published.countP (fun pub => pub.slot == slot)

/-- A successful acquire of a particular completed generation in the consumer's CTA. -/
structure Completed (l : Launch) (X : Execution) (wait : EvId) (slot : Fin 3)
    (phase : Nat) where
  acquire : ReadyAcquire l X wait slot
  position : Nat
  poll : Record Ref
  record : (X.objects (readyObject l wait.1 slot))[position]? = some poll
  id : poll.id = .thread wait
  success : poll.reply.waited = some true
  observed : observedAt (X.objects (readyObject l wait.1 slot)) position = some phase

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Once its tracked writes have completed, a pending publication has a counted extension. -/
theorem pendingPublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {issue : EvId} {slot : Fin 3}
    (he : X.AsyncArrive issue (readyObject l issue.1 slot) true)
    (hPending : X.async.arrived issue = false)
    (hWrites : ∀ copy, TracksCpAsync X copy issue → (X.async.copies copy).writeBytes.isSome) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l :=
  pending_cpAsyncArrive_extendsInOrder Assumptions.wfStep hX he hPending hWrites

/-- A pending Q or Bias tensor input can read, write, or notify while its backed input
region is protected by the output frame. -/
theorem pendingTensorInput (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {address : Nat} {spec : TensorCopy.Spec}
    (he : X.TensorIssue i address spec)
    (hPending : (X.tensor i).any (fun o => o.effects.notified) = false) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  exact pending_tensor_inOrder Assumptions.wfStep hX (tensorInputOperands hp hX hFrame) he
    hPending

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
