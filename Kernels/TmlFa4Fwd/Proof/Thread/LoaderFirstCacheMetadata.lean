-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstCacheProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue

noncomputable section

/-- The saved first K metadata at the cursor after the successful empty acquire. -/
def PrimingKeyMetadataReady {p : Params} {l : Launch} {X : Execution}
    {g batch head tile shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : PrimingKeyEmptyReady p l X g batch head tile shuffles votes ends) : Prop :=
  ∀ lane < 32, ∀ slot : Fin 2,
    let base := primingLaneRow tile (32*warpIndex l g+lane)
    PrimingMetadataAt p l X (warpLane l g lane) (cur.pos lane) batch (base+64*slot.val) slot

/-- Both scratch cells retain their writes through the successful empty acquire. -/
theorem primingKeyMetadataOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {g batch head tile shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hTile : 128*tile+127 < 2^31)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 488
      (loaderScratchIterationFrame p l batch head tile (warpIndex l g) 0) shuffles votes ends)
    (ready : ∀ lane < 32,
      (∀ (i : Nat) (loc : Loc), ¬ X.AsyncArrive (warpLane l g lane,i) loc true) →
      ∃ s, stateBefore (X.objects (Thread.Mma.Observation.emptyObject l g 0))
        (X.objects (Thread.Mma.Observation.emptyObject l g 0)).length = some s ∧ s.phase = 0) :
    ∃ done : PrimingKeyEmptyReady p l X g batch head tile shuffles votes ends,
      PrimingKeyMetadataReady done := by
  obtain ⟨middle,hFirst⟩ := primingScratchWarpWithTrace hp hMax writes hg hw hb hTile 0 cur
  obtain ⟨last,hSecond⟩ := primingScratchWarpWithTrace hp hMax writes hg hw hb hTile 1 middle
  obtain ⟨done,hWait⟩ := primingKeyEmptyReadyWithTrace hp hMax hg last ready
  refine ⟨done,?_⟩
  intro lane hl slot
  let g' := warpLane l g lane
  let base := primingLaneRow tile (32*warpIndex l g+lane)
  let first := primingScratchEvents p l g' batch base 0
  let second := primingScratchEvents p l g' batch base 1
  have h0 : middle.pos lane = cur.pos lane+first.length := (hFirst lane hl).1
  have h1 : last.pos lane = middle.pos lane+second.length := (hSecond lane hl).1
  obtain ⟨n,h2,hTail⟩ := hWait lane hl
  have hTrace : (X.tr g').drop (cur.pos lane) = first ++ second ++
      List.replicate n (primingKWaitEvent l g' false) ++
        (primingKWaitEvent l g' true :: (X.tr g').drop (done.pos lane)) := by
    simpa only [List.append_assoc,g'] using
      ((hFirst lane hl).2.trans (congrArg (first ++ ·) ((hSecond lane hl).2.trans
        (congrArg (second ++ ·) hTail))))
  have hIndex : done.pos lane = cur.pos lane+first.length+second.length+n+1 := by
    rw [h2,h1,h0]
  exact hIndex.symm ▸ primingMetadataFromObservedTrace hMax.1 hTrace slot

end
end PTX.Kernels.TmlFa4Fwd.Loader
