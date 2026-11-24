-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleRoute
public import Kernels.TmlFa4Fwd.Proof.MmaScanCounter

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The scheduler ABI remains available across a request-group scan. -/
def fallbackBaseFrame (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) :
    List (Nat × Value) :=
  (7140, b32 p.heads) :: (1215, b32 (laneOf l g)) :: schedulerEntry p l g warp

/-- At the scan head, each lane still holds the completed groups' common work cutoff. -/
def fallbackScanFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (first cutoff : Nat) : List (Nat × Value) :=
  (7238, b32 cutoff) ::
    Mma.groupScanFacts .softmaxSelect first p.batch (g / l.block) ++ fallbackBaseFrame p l g warp

private theorem initializeFallback (l : Launch) (g : Nat) {cta batch cutoff : Nat}
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel [] l g 3 3155 [(1072, b32 cta), (7247, b32 batch), (7244, b32 cutoff)]
      3158 ((7238, b32 cutoff) :: Mma.groupScanFacts .softmaxSelect 0 batch cta) := by
  intro t ht
  dsimp only [Mma.groupScanFacts, Mma.scanSite]
  seg_fp ht using norm_bits

/-- The real first-group miss initializes the continuing warp search with its computed cutoff. -/
theorem warpFallbackStartPreserving {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3155 (firstRouteFacts p l g warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 3158 (fun lane =>
        fallbackScanFacts p l (warpLane l g lane) warp 0
          (tilePrefix p (min p.batch 31) * p.heads)) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let cta := thread / l.block
  let cutoff := tilePrefix p (min p.batch 31) * p.heads
  let F := fallbackBaseFrame p l thread warp
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hCta : cta + 1 < 2 ^ 31 := by
    have hGrid : cta < l.grid :=
      (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hThread
    have hBound := hp.grid.2.2
    omega
  have ht := cur.checkpoint lane hl
  have hRegs := ht.2.2.2.2
  have hF : Holds (cur.state lane).regs F := by
    exact ⟨hRegs.2.2.2.2.2.1, hRegs.2.2.2.2.2.2.2.1, hRegs.2.2.2.2.2.2.2.2.2⟩
  have hBatch := holds_lookup hF (show F.lookup 7247 = some (b32 p.batch) from rfl)
  have hCTA := holds_lookup hF (show F.lookup 1072 = some (b32 cta) from rfl)
  have hAt : At (cur.state lane) 3155
      [(1072, b32 cta), (7247, b32 p.batch), (7244, b32 cutoff)] :=
    ht.mono ⟨hCTA, hBatch, hRegs.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := (initializeFallback l thread hCta).apply hAt
  have hStraight : ((kernel.code.drop 3155).take (3 - 1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hWrites : ((kernel.code.drop 3155).take 3).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSaved := holdsSchedulerFrame hF (fun _ hr => schedulerLocalFrame hWrites hStraight hu
    ht.1.ge (by rw [ht.1]) hr) (fun _ hx => List.mem_map_of_mem hx)
  have hRun := Mma.groupScanLocalRun .softmaxSelect (by decide) (by decide) hAt.1 hStraight hu
  refine ⟨u, run_rtg hRun, hU.mono ?_⟩
  rw [fallbackScanFacts, List.cons_append, holds_cons, holds_append]
  exact ⟨hU.2.2.2.2.1, hU.2.2.2.2.2, hSaved⟩
/-- The real first-group miss initializes the continuing warp search with its computed cutoff. -/
theorem warpFallbackStart {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3155 (firstRouteFacts p l g warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 3158 (fun lane =>
        fallbackScanFacts p l (warpLane l g lane) warp 0
          (tilePrefix p (min p.batch 31) * p.heads)) shuffles votes ends,
      next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := warpFallbackStartPreserving hp hg cur
  exact ⟨next,hPos⟩


/-- The next scan group carries both the clipped batch cursor and the previous work cutoff. -/
def fallbackAdvanceFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (first cutoff : Nat) : List (Nat × Value) :=
  (1218, b32 (first + 31)) :: (7244, b32 (g / l.block + 1)) ::
    Mma.groupScanFacts .softmaxSelect (min (first + 31) p.batch) p.batch (g / l.block) ++
    ((7238, b32 cutoff) :: fallbackBaseFrame p l g warp)

/-- The scheduler either reaches the protected reads or bypasses them at the batch limit. -/
theorem warpFallbackAdvancePreserving {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes first cutoff : Nat} {warp : Fin 8}
    (hFirst : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3158 (fun lane =>
      fallbackScanFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g (if p.batch ≤ first + 31 then 3209 else 3163)
        (fun lane => fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff)
        shuffles votes ends, next.pos = cur.pos ∧ next.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let cta := thread / l.block
  let F := (7238, b32 cutoff) :: fallbackBaseFrame p l thread warp
  have hAdvance : first + 31 < 2 ^ 31 := by
    have hBatch := hp.shape.2.2.2.2.2
    omega
  have ht := cur.checkpoint lane hl
  have hAt : At (cur.state lane) (Mma.scanSite .softmaxSelect).head
      (Mma.groupScanFacts .softmaxSelect first p.batch cta ++ F) := by
    apply ht.mono
    have h := ht.2.2.2.2
    change Holds (cur.state lane).regs ((7238, b32 cutoff) ::
      (Mma.groupScanFacts .softmaxSelect first p.batch cta ++ fallbackBaseFrame p l thread warp))
      at h
    rw [holds_cons, holds_append] at h
    rw [holds_append]
    exact ⟨h.2.1, h.1, h.2.2⟩
  have hWrites : ((kernel.code.drop (Mma.scanSite .softmaxSelect).head).take 5).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u, hu, hU⟩ := Mma.advanceGroupScanPreserving .softmaxSelect hAdvance hp.shape.2.1
    (g := thread) hWrites hAt
  exact ⟨u, run_rtg hu, hU⟩
/-- The scheduler either reaches the protected reads or bypasses them at the batch limit. -/
theorem warpFallbackAdvance {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes first cutoff : Nat} {warp : Fin 8}
    (hFirst : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3158 (fun lane =>
      fallbackScanFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g (if p.batch ≤ first + 31 then 3209 else 3163)
        (fun lane => fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff)
        shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := warpFallbackAdvancePreserving hp hFirst cur
  exact ⟨next,hPos⟩


end
end PTX.Kernels.TmlFa4Fwd.Softmax
