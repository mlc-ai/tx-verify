-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderScratchProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstCacheOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.Mma
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyExactOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue

noncomputable section

/-- The first K packet's actual warp cursor after the scratch writes. -/
abbrev PrimingKeyScratchReady (p : Params) (l : Launch) (X : Execution)
    (g batch head tile shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 515
    (loaderScratchIterationFrame p l batch head tile (warpIndex l g) 1) shuffles votes ends

/-- The first K packet's actual warp cursor after the successful empty acquire. -/
abbrev PrimingKeyEmptyReady (p : Params) (l : Launch) (X : Execution)
    (g batch head tile shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 520
    (loaderScratchIterationFrame p l batch head tile (warpIndex l g) 1) shuffles votes ends

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch head tile shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : PrimingKeyScratchReady p l X g batch head tile shuffles votes ends)
    (ready : ∀ lane < 32,
      (∀ (i : Nat) (loc : Loc), ¬ X.AsyncArrive (warpLane l g lane,i) loc true) →
      ∃ s, stateBefore (X.objects (Thread.Mma.Observation.emptyObject l g 0))
        (X.objects (Thread.Mma.Observation.emptyObject l g 0)).length = some s ∧ s.phase = 0)
include hp hMax hg cur ready

/-- Finish the initial K empty wait when a lane that has published no tile has a fresh object. -/
theorem primingKeyEmptyReadyWithTrace :
    ∃ done : PrimingKeyEmptyReady p l X g batch head tile shuffles votes ends,
      ∀ lane < 32, ∃ n,
        let thread := warpLane l g lane
        done.pos lane = cur.pos lane+n+1 ∧
          (X.tr thread).drop (cur.pos lane) = List.replicate n (primingKWaitEvent l thread false) ++
            (primingKWaitEvent l thread true :: (X.tr thread).drop (done.pos lane)) := by
  let warp := warpIndex l g
  let base := fun lane => primingLaneRow tile (32*warp+lane)
  let frame := fun lane => primingKPackFrame p l batch head tile warp lane
  let G := fun lane => primingKWaitFacts p l batch (base lane) ++ frame lane
  have hFrame (lane : Nat) : PrimingKWaitExtra (frame lane) := primingKFrameWait ..
  obtain ⟨started,hStart,hBefore⟩ :=
    cur.toSchedulerWarpAt.advanceLocalPreserving (pc' := 517) (G := G) (fun lane hl =>
      primingKWaitPrepare hp (hFrame lane) (cur.checkpoint lane hl))
  let start := cur.reframe started hStart hBefore
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWidth : l.sharedBase + 56 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase + 56) % 8 = 0 := by have := hp.shared.1; omega
  let site := Thread.Loader.primingEmptySite 0
  have hFresh (lane : Nat) (_hl : lane < 32) : ∀ pair ∈ G lane, pair.1 ≠ site.result := by
    intro pair hm he
    rcases List.mem_append.mp hm with hOld | hNew
    · have hx := List.mem_map_of_mem (f := Prod.fst) hOld
      rw [he] at hx
      exact (show site.result ∉ (primingKWaitFacts p l batch (base lane)).map Prod.fst
        from of_decide_eq_true rfl) hx
    · exact (hFrame lane).resultFresh pair hNew he
  obtain ⟨waited,hTrace⟩ :=
    loaderWarpWaitOfReadyLastTrace hMax hg hBlock (Thread.Loader.primingEmptyCode 0)
    (by decide) hWidth hAlign start hFresh
    (fun _ _ => List.mem_append_left _ List.mem_cons_self)
    (fun _ _ => List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (fun lane hl {_ _} hr hLocal hAt =>
      ready lane hl (Thread.Loader.noCachePublicationAtFirstEmpty hMax.1 hr hLocal hAt.1))
  obtain ⟨result,hFinish,hResult⟩ := waited.toSchedulerWarpAt.advanceLocalPreserving
    (pc' := 520) (G := loaderScratchIterationFrame p l batch head tile (warpIndex l g) 1)
    (fun lane hl => ⟨_,.refl,(waited.checkpoint lane hl).mono
      (waited.checkpoint lane hl).2.2.2.2.2.2⟩)
  refine ⟨waited.reframe result hFinish hResult,?_⟩
  intro lane hl
  obtain ⟨n,hAt,hEvents⟩ := hTrace lane hl
  refine ⟨n,?_,?_⟩
  · change result.pos lane = _
    change waited.pos lane = started.pos lane+n+1 at hAt
    rw [hFinish,hAt,hStart]
  · change _ = _ ++ (_ :: (X.tr (warpLane l g lane)).drop (result.pos lane))
    change (X.tr (warpLane l g lane)).drop (started.pos lane) = _ at hEvents
    rw [hFinish,← hStart]
    exact hEvents

end
end PTX.Kernels.TmlFa4Fwd.Loader
