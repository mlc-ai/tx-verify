-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Kernels.FlashAttn4Fwd.Proof.Interface.Init
public import Kernels.FlashAttn4Fwd.Proof.Interface.Result
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread

@[expose] public section

/-! # What the thread layer exports for the asynchronous obligations of progress

The progress layer shows that an issued tensor load, tensor store or MMA of a maximal execution
has completed. Each completion is a step the model allows once the operation's inputs are fixed:
a load's global bytes, a store's staging bytes, an MMA's operands. The protocols fix them from
the thread layer's exports (`AsyncInputs`): the existing interface structures, and the facts of
single threads that no structure holds yet (`ProgressAsyncFacts`):

* **Issue checks.** A tensor load is routed from its CTA and reads a map with a valid descriptor
  (`copy_route`); a tensor store's specification is valid (`store_valid`). The instructions issue
  only then (`Flow.fires_cpTensor_route`, `Flow.fires_cpTensorStore_form`).
* **Writes.** A thread's write carries as many bytes as its footprint (`write_length`) and does
  not release (`no_release`).
* **MMA operands in shared memory.** An MMA's read of a shared byte reads a Q or KV ring region
  (`mma_reads`, the region premise of the output staging). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

/-- The thread layer's facts for the asynchronous obligations that no other structure holds. -/
structure ProgressAsyncFacts (L : Launch) (X : Execution) : Prop where
  /-- A tensor load is routed from its CTA, through a map with a valid descriptor. -/
  copy_route : ∀ {i : EvId} {pc a : Nat} {s : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a s⟩ →
      TensorCopy.RoutingOk L (i.1 / L.block) s ∧ TensorDescriptor.Valid s.descriptor
  /-- A tensor store's specification is valid for its CTA. -/
  store_valid : ∀ {i : EvId} {pc a : Nat} {s : TensorStore.Spec},
    X.get i = some ⟨pc, .tensorStore a s⟩ → TensorStore.Valid (i.1 / L.block) s
  /-- A thread's write carries as many bytes as its footprint. -/
  write_length : ∀ {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte},
    X.get e = some ⟨pc, .wr a bs⟩ → bs.length = a.size
  /-- No thread's write releases. -/
  no_release : ∀ {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte},
    X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  /-- An MMA's read of a shared byte reads a Q or KV ring region. -/
  mma_reads : ∀ i isB idx l, AsyncCovers X i (.mmaRead isB idx) l → l.space = .shared →
    ∃ c b, FBar.isFull b ∧ InRegion L c b l

/-- The thread layer's exports the asynchronous obligations of progress use. -/
structure AsyncInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  cluster : ClusterFacts L X
  init : InitFacts L X
  tmem : TmemFacts L X
  rings : RingFacts L X
  ringCopies : RingCopies P L X
  async : AsyncFacts P L X
  output : OutputFacts L X
  store : StoreFacts P L X
  writes : WriteFacts L X
  score : ScoreFacts L X
  tc : TcFacts L X
  tcmma : TcMmaThreadFacts L X
  progress : ProgressAsyncFacts L X

end
end PTX.Kernels.FlashAttn4Fwd.Proof
