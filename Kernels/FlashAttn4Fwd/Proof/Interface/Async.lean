-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem

@[expose] public section

/-! # What the thread layer exports for the asynchronous branches of safety

The facts of single threads that the mbarrier, tensor-copy, tensor-allocation and shared-lifetime
branches of `Unsafe` need beyond the protocols' interfaces (`RingFacts`, `TmemFacts`,
`OutputFacts`, `ClusterFacts`):

* **Barriers.** Every mbarrier operation of a thread (arrival, poll, commit target) names a barrier
  of the table (`FBar`) in a CTA of the thread's pair (`mbar_pair`); every tensor copy completes on
  a ring barrier (`copy_ring`). (The initializations are `InitFacts`.)
* **Places.** A thread's shared accesses are of its own CTA (`access_own`); an MMA's operands are
  in its pair (`mma_pair`); a tensor store reads its own CTA (`store_base`).
* **Boxes.** A copy loads for an item its loader started (`copy_started`): the use's work item is
  below the item count; a tensor store's box is inside the O map (`store_bounds`); the kernel
  issues no tensor prefetch (`no_prefetch`).

The fields are proved from the roles' run invariants (the sites of their barrier operations,
copies, MMAs and stores). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The thread layer's facts for the asynchronous branches. -/
structure AsyncFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- Every mbarrier operation (arrival, poll, commit target, invalidation) names a table barrier
  of a CTA of its issuer's pair. -/
  mbar_pair : ∀ {e : EvId} {m : Loc}, X.UsesMbar e m →
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L e.1 / 2
  /-- Every tensor copy completes on a ring barrier. -/
  copy_ring : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → ∃ (b : FBar) (c : Nat), b.ring ∧ sp.mbar = b.loc L c
  /-- A thread's shared accesses are of its own CTA. -/
  access_own : ∀ {g k : Nat} {a : Acc} {w : Bool}, X.Access (g, k) a w → a.loc.space = .shared →
    a.loc.cta = ctaOf L g
  /-- An MMA's operand CTAs are in its issuer's pair. -/
  mma_pair : ∀ {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → s.lowCta / 2 = ctaOf L i.1 / 2 ∧ s.highCta / 2 = ctaOf L i.1 / 2
  /-- A tensor store reads its own CTA. -/
  store_base : ∀ {i : EvId} {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue i a s →
    s.sharedBase.cta = ctaOf L i.1
  /-- A copy on a ring full barrier loads for an item its thread started: the work item of the
  copy's use is below the item count. -/
  copy_started : ∀ {g k pc a c : Nat} {b : FBar} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = b.loc L c → b.isFull →
      workOf L g (useItem P b (((X.tr g).take k).countP (issuesTo (b.loc L c)) / b.copies)) <
        totOf L
  /-- A tensor store's box is inside its map. -/
  store_bounds : ∀ {i : EvId} {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue i a s →
    ¬ TensorHasOob s.descriptor s.origin s.rows
  /-- The kernel issues no tensor prefetch. -/
  no_prefetch : ∀ {i : EvId} {pc a : Nat} {s : TensorPrefetch.Spec},
    X.get i ≠ some ⟨pc, .tensorPrefetch a s⟩

namespace Safety

/-- The records other than initializations of the table barriers that are neither ring nor
handshake barriers are fault-free (the protocols of the score handoff, P-ready, O-full,
statistics credit, output staging and free barriers; the spare barriers have none). Proved by
`Faults.otherFaultFree`. -/
def OtherFaultFree (L : Launch) (X : Execution) : Prop :=
  ∀ (b : FBar), b.ring = false → b ≠ .dealloc → ∀ (cta : Nat) {r : MBarrier.Record AsyncCopy.Ref},
    r ∈ X.objects (b.loc L cta) → (∀ n, r.action ≠ .init n) → r.fault = none

end Safety

end
end PTX.Kernels.FlashAttn4Fwd.Proof
