-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.Lifetime
public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotFacts
public import Kernels.FlashAttn4Fwd.Proof.Protocol.HsInitProof
public import Kernels.FlashAttn4Fwd.Proof.Protocol.Schedule

@[expose] public section

/-! # The memory-operation branches' protocol inputs

This file sits at the top of the proof tree, outside the layer order (as `SafeFacts.lean` does):
it supplies the safety layer's TMA, tensor, tensor-allocation and shared-lifetime branches with
the protocols' exports, in the statements those branches take:

* every table barrier's users are of its cluster (`tableUsers`), so it is initialized first
  (`tableInit`, `InitFirst.init_first`);
* the loader's tile coordinates are in range (`coordsInRange`, `Schedule.coords_lt`);
* the handshake barrier's initialization (`HsInitProof.hsInit`) and the rings'
  (`InitFirst.ringInit`) give the fault-free records;
* a tensor load's barrier is initialized and published to it (`tensorLoadInit`, the tensor-load
  case of `MbarUninit`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every table barrier's users are of its cluster.** -/
theorem tableUsers (hX : Consistent L kernel asms mem0 X) (hr : RingFacts L X)
    (ha : AsyncFacts P L X) (b : FBar) (cta : Nat) : InitFirst.Users L X (b.loc L cta) where
  arrive _ he := by
    obtain ⟨b', c', hm, hc'⟩ := ha.mbar_pair (.inl ⟨_, _, _, _, _, he⟩)
    rw [hm]; exact hc'.symm
  wait _ he := by
    obtain ⟨b', c', hm, hc'⟩ := ha.mbar_pair (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩)))))
    rw [hm]; exact hc'.symm
  tensor he hm := by
    obtain ⟨b', c', hring, hm'⟩ := ha.copy_ring he
    obtain ⟨-, hc', -⟩ := hr.issue (Frame.lt_of_get hX he) he hm' hring
    rw [← hm, hm']
    show _ = c' / 2
    rw [hc', pairBase]
    omega

/-- **Every table barrier is initialized first.** -/
theorem tableInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hr : RingFacts L X)
    (ha : AsyncFacts P L X) : Safety.TableInit L X :=
  fun b cta => InitFirst.init_first hpre hX hc htm hi b cta (tableUsers hX hr ha b cta)

/-- **The loader's tile coordinates are in range.** -/
theorem coordsInRange (hpre : Pre P L mem0) : Safety.CoordsInRange P L := by
  intro w hw
  have h1 := Schedule.totOf_items hpre
  have h2 := totOf_lt hpre
  rw [Schedule.coords_eq hpre (by omega)]
  exact Schedule.coords_lt hpre (by omega)

/-- **No TMA copy or barrier operation is unsafe.** -/
theorem tmaSafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    (hi : InitFacts L X) (hplaced : Safety.SharedPlaced L X)
    (hother : Safety.OtherFaultFree L X) : ¬ TmaUnsafe L mem0 X :=
  Safety.no_tmaUnsafe hpre hX hc hr htm ha (tableInit hpre hX hc htm hi hr ha)
    (ClusterStart.init_published hpre hX hc)
    (Rings.ring_fault_free hpre hX hr htm (InitFirst.ringInit hpre hX hc htm hi hr))
    (fun cta _ hrec => TmemAlloc.fault_free hpre hX htm (HsInitProof.hsInit hpre hX hc htm hi cta)
      hrec)
    hother hplaced

/-- **No tensor copy is unsafe.** -/
theorem tensorSafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (ha : AsyncFacts P L X) (hcp : RingCopies P L X) : ¬ TensorUnsafe X :=
  Safety.no_tensorUnsafe hpre hX hr hcp ha (coordsInRange hpre)

/-- **A tensor load's mbarrier is initialized, and the initialization is published to the load**
(the tensor-load case of `MbarUninit`). -/
theorem tensorLoadInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (ha : AsyncFacts P L X)
    (hcp : RingCopies P L X) (hi : InitFacts L X) {g k pc address : Nat}
    {s : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue address s⟩) :
    ∃ i count, X.MbInit i s.mbar count ∧ InitPublished L X i (g, k) s.mbar :=
  Safety.load_initPublished hpre hX hr hcp ha hc (InitFirst.init_exists hpre hX hc hi)
    (ClusterStart.init_published hpre hX hc) he

/-- **No tensor access is outside its allocation.** -/
theorem tensorAllocSafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X) :
    ¬ TensorAllocationUnsafe L mem0 X :=
  Safety.no_tensorAllocationUnsafe hpre hX hr hcp ha (coordsInRange hpre)

/-- **No shared byte is used outside its lifetime.** -/
theorem lifetimeSafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (htm : TmemFacts L X) (hs : ScoreFacts L X)
    (ho : OutputFacts L X) (hc : ClusterFacts L X) (ha : AsyncFacts P L X)
    (hpeer : Safety.PeerThreadFinished L X) (hcopy : Safety.CopyFinished L X)
    (hmma : Safety.MmaFinished L X) (hcommit : Safety.CommitFinished L X) :
    ¬ SharedLifetimeUnsafe L kernel asms X :=
  Safety.no_sharedLifetimeUnsafe hpre hX hr hcp htm hs ho hc ha
    (ClusterStart.peer_started hpre hX hc) hpeer hcopy hmma hcommit

end
end PTX.Kernels.FlashAttn4Fwd.Proof
