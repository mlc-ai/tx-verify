-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmOpeningProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringWaitProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPointerProgress
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundPageIndex
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderFirstCachePhase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
open LocalAccessCode (DoesNotClobber)

def warmFirstTile (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-2

private def warmFirstPageFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (slot : Fin 2) : List (Nat × Value) :=
  let tile := warmFirstTile p l g batch
  let tid := warpLane l g lane%l.block
  [(7175,b32 slot.val),(8,.pred (decide (slot=0))),(1118,b32 (128*tile)),
    (1119,b32 (8*(tid%8)))] ++ warmFirstFrame p l g batch lane

private def warmFirstPageIndexedFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (slot : Fin 2) : List (Nat × Value) :=
  let tile := warmFirstTile p l g batch
  let tid := warpLane l g lane%l.block
  [(1969,b32 (primingLaneRow tile tid)),(1964,b32 (64*slot.val))] ++
    warmFirstPageFrame p l g batch lane slot

private theorem warmFirstIndexOfStarted {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch : Nat} (hTile : 128*warmFirstTile p l g batch+127 < 2^31)
    (c : WarmCacheStarted p l X g batch) :
    ∃ idx : SchedulerWarpReached l X g 929
        (fun lane => warmFirstPageIndexedFrame p l g batch lane 0)
        c.shuffles c.votes c.ends,
      idx.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let tile := warmFirstTile p l g batch
  let F := warmFirstFrame p l g batch lane
  have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hC := c.reached.checkpoint lane hl
  have hRegs : Holds (c.reached.state lane).regs F := hC.2.2.2.2
  have hAt : At (c.reached.state lane) 917
      ([(1116,b32 tile),(7174,b32 0),(1061,b32 tid)]++F) := by
    apply hC.mono
    refine ⟨hRegs.2.2.2.2.2.1,hRegs.1,?_,hRegs⟩
    exact holds_mem hRegs (by
      simp [F,warmFirstFrame,openingWarmPublishedFrame,openingWarmFrame,
        warmStartFrame,warmPageRoots,warmLaneRoots,tid,t])
  obtain ⟨u,hu,hU⟩ := warmFirstIndexRunWithRowSeed (g := t) hTile hTid
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hAt
  exact ⟨u,run_rtg hu,hU⟩

private theorem warmFirstRowBound {p : Params} {l : Launch} {g batch : Nat}
    (hTile : 128*warmFirstTile p l g batch+127 < 2^31) (tid : Nat) (slot : Fin 2) :
    primingLaneRow (warmFirstTile p l g batch) tid+64*slot.val < 2^31 := by
  have hs := slot.isLt
  have hm := Nat.mod_lt (tid/8) (by decide : 0 < 8)
  have hn := Nat.mod_lt tid (by decide : 0 < 8)
  unfold primingLaneRow kvCopyColumn
  simp only [Bool.false_eq_true,ite_false]
  omega

private theorem warmFirstPageGuard {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shuffles votes : Nat} (hb : batch < p.batch)
    (hTile : 128*warmFirstTile p l g batch+127 < 2^31) (slot : Fin 2)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 929
      (fun lane => warmFirstPageIndexedFrame p l g batch lane slot) shuffles votes ends) :
    let row := fun lane => primingLaneRow (warmFirstTile p l g batch) (warpLane l g lane%l.block) +
      64*slot.val
    ∃ gate : SchedulerWarpReached l X g 939
        (fun lane => recurringPageGuardInput p l 0 slot batch (row lane) ++
          warmFirstPageFrame p l g batch lane slot) shuffles votes ends,
      gate.pos = cur.pos := by
  dsimp only
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tile := warmFirstTile p l g batch
  let tid := t%l.block
  let base := primingLaneRow tile tid
  let row := base+64*slot.val
  let F := warmFirstPageFrame p l g batch lane slot
  have hSmall : row < 2^31 := warmFirstRowBound hTile tid slot
  have hLen : p.kLength batch < 2^31 := by have := (hp.lengths batch hb).2.2; omega
  have hs := cur.checkpoint lane hl
  have hAt : At (cur.state lane) 929 (recurringPageIndexInput 0 base (p.kLength batch) slot) := by
    apply hs.mono
    simp only [recurringPageIndexInput,recurringPageSite,Holds]
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hs.2.2.2.2 rfl
  obtain ⟨u,hu,hU⟩ := recurringPageIndexCore (l := l) (g := t) 0 slot hSmall hLen
    (cur.state lane) hAt
  obtain ⟨huA,huF⟩ := loaderLinear (regs := F.map Prod.fst) (lo := 929) (n := 10)
    (by decide) (by decide) hs.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hF := holdsSchedulerFrame (show Holds (cur.state lane).regs F from hs.2.2.2.2.2.2)
    huF (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u,run_rtg huA,hU.mono ?_⟩
  change Holds u.regs (recurringPageGuardInput p l 0 slot batch row ++ F)
  apply (holds_append ..).mpr
  refine ⟨(holds_append ..).mpr ⟨hU.2.2.2.2,?_⟩,hF⟩
  simp only [pageStoreCarry,recurringPageBatchInputs,recurringPageStoreSite,recurringPageSite,
    List.cons_append,Holds]
  repeat' apply And.intro
  all_goals first | trivial | exact holds_lookup hF rfl | exact holds_lookup hU.2.2.2.2 rfl

private theorem warmFirstPageRefreshFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (slot : Fin 2) : RecurringRefreshFrame 0 (warmFirstPageFrame p l g batch lane slot) := by
  let F := warmFirstPageFrame p l g batch lane slot
  constructor
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · intro pair hm hEq
    have hNo : (recurringPageSite 0).physicalPage ∉ F.map Prod.fst := of_decide_eq_true rfl
    exact hNo (hEq ▸ List.mem_map_of_mem hm)
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

private theorem warmSecondIndexOfPage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch shuffles votes : Nat}
    (hTile : 128*warmFirstTile p l g batch+127 < 2^31)
    {ends : Nat → Option TState}
    (done : SchedulerWarpReached l X g 954
      (fun lane => warmFirstPageFrame p l g batch lane 0) shuffles votes ends) :
    ∃ idx : SchedulerWarpReached l X g 929
        (fun lane => warmFirstPageIndexedFrame p l g batch lane 1) shuffles votes ends,
      idx.pos = done.pos := by
  apply done.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let tile := warmFirstTile p l g batch
  let F := warmFirstFrame p l g batch lane
  have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hs := done.checkpoint lane hl
  have hIn : At (done.state lane) 954 ([(8,.pred true),(1118,b32 (128*tile))]++F) :=
    hs.mono ⟨hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2⟩
  obtain ⟨u,hu,hU⟩ := warmPageSlotRoute (g := t) true
    (by set_option maxRecDepth 100000 in kernel_rfl) hIn
  have hSeed : At u 921
      ([(1118,b32 (128*tile)),(1061,b32 tid),(7175,b32 (1 : Fin 2).val),(775,.pred false)]++F) := by
    apply hU.mono
    have hRegs := hU.2.2.2.2
    refine ⟨hRegs.2.2.1,holds_mem hRegs.2.2.2 ?_,hRegs.1,hRegs.2.1,hRegs.2.2.2⟩
    simp [F,warmFirstFrame,openingWarmPublishedFrame,openingWarmFrame,
      warmStartFrame,warmPageRoots,warmLaneRoots,tid,t]
  obtain ⟨v,hv,hV⟩ := warmPageIndexRunFromSlot (g := t) hTile hTid 1 false
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeed
  exact ⟨v,run_rtg (run_comp hu hv),hV⟩

/-- The warm K prelude carries the physical ring cursor and its lane's column. -/
def warmFirstPagesFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  (1119,b32 (8*(warpLane l g lane%l.block%8)))::warmFirstFrame p l g batch lane

def warmFirstSlotRow (p : Params) (l : Launch) (g batch lane : Nat) (slot : Fin 2) : Nat :=
  primingLaneRow (warmFirstTile p l g batch) (warpLane l g lane%l.block)+64*slot.val

def warmFirstMetadata (p : Params) (l : Launch) (X : Execution)
    (g batch lane index : Nat) (slot : Fin 2) (isRow : Bool) : Prop :=
  let t := warpLane l g lane
  let row := warmFirstSlotRow p l g batch lane slot
  let op := recurringScratchWord 0 isRow
  PrimingCellValue X t index op.store (scratchReloadAccess l t op slot)
    (b32 (if isRow then row%16 else primingScratchPage p batch row)).toBytes

/-- Both lane-private page slots have been refreshed before the warm K acquire. -/
structure WarmFirstPages (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 957 (warmFirstPagesFrame p l g batch) shuffles votes ends
  unpublishedKey : ∀ lane < 32, ∀ index < reached.pos lane,
    ¬ X.AsyncArrive (warpLane l g lane,index) (readyObject l (warpLane l g lane) 2) true
  cells : ∀ lane < 32, ∀ slot isRow,
    warmFirstMetadata p l X g batch lane (reached.pos lane) slot isRow

variable {p : Params} {l : Launch}

set_option maxRecDepth 4096 in
/-- A loader warp actually writes both private scratch slots on its first warm visit. -/
theorem WarmCacheStarted.refreshPagesWithRankOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (c : WarmCacheStarted p l X g batch) :
    ∃ next : WarmFirstPages p l X g batch, next.shuffles = c.shuffles := by
  let tile := warmFirstTile p l g batch
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hTile : 128*tile+127 < 2^31 := by dsimp [tile,warmFirstTile]; omega
  obtain ⟨idx,hIndex⟩ := warmFirstIndexOfStarted hp hTile c
  obtain ⟨gate,hGate⟩ := warmFirstPageGuard hp hb hTile 0 idx
  let row := fun lane => primingLaneRow tile (warpLane l g lane%l.block)+64*(0 : Fin 2).val
  obtain ⟨first,hFirst⟩ := recurringPageRefreshWarpOfMaximal hp hMax hFrame hg hw hb 0 0 row
    (fun lane _ => warmFirstRowBound hTile (warpLane l g lane%l.block) 0)
    (fun lane _ => warmFirstPageRefreshFrame p l g batch lane 0) gate
  obtain ⟨idx',hIndex'⟩ := warmSecondIndexOfPage hp hTile first
  obtain ⟨gate',hGate'⟩ := warmFirstPageGuard hp hb hTile 1 idx'
  let row' := fun lane => primingLaneRow tile (warpLane l g lane%l.block)+64*(1 : Fin 2).val
  obtain ⟨second,hSecond⟩ := recurringPageRefreshWarpOfMaximal hp hMax hFrame hg hw hb 0 1 row'
    (fun lane _ => warmFirstRowBound hTile (warpLane l g lane%l.block) 1)
    (fun lane _ => warmFirstPageRefreshFrame p l g batch lane 1) gate'
  obtain ⟨reached,hReached⟩ := second.advanceLocalWithPosition (pc' := 957)
    (G := warmFirstPagesFrame p l g batch) (by
    intro lane hl
    let t := warpLane l g lane
    let F := warmFirstPagesFrame p l g batch lane
    have hs := second.checkpoint lane hl
    have hAt : At (second.state lane) 954 ([(8,.pred false),(1118,b32 (128*tile))]++F) :=
      hs.mono hs.2.2.2.2.2
    obtain ⟨u,hu,hU⟩ := warmPageSlotRoute (g := t) false
      (by set_option maxRecDepth 100000 in kernel_rfl) hAt
    exact ⟨u,run_rtg hu,hU.mono hU.2.2.2.2.2.2.2⟩)
  refine ⟨⟨c.shuffles,c.votes,c.ends,reached,?_,?_⟩,rfl⟩
  · intro lane hl i hi
    have hBefore : gate.pos lane = c.reached.pos lane := congrFun (hGate.trans hIndex) lane
    have hBetween : gate'.pos lane = first.pos lane := congrFun (hGate'.trans hIndex') lane
    have hAfter : reached.pos lane = second.pos lane := congrFun hReached lane
    rw [hAfter] at hi
    by_cases hOld : i < c.reached.pos lane
    · exact c.unpublishedKey lane hl i hOld
    by_cases hNew : i < first.pos lane
    · exact (hFirst lane hl).2.2.2.1 i (hBefore.symm ▸ Nat.le_of_not_gt hOld) hNew _
    exact (hSecond lane hl).2.2.2.1 i (hBetween.symm ▸ Nat.le_of_not_gt hNew) hi _
  · intro lane hl slot flag
    let t := warpLane l g lane
    let start := gate.pos lane
    let r := primingLaneRow tile (t%l.block)
    let step := start+primingScratchReads p batch r+2
    let stop := step+primingScratchReads p batch (r+64)+2
    have hRow0 : row lane = r := by simp [row,r,t]
    have hRow1 : row' lane = r+64 := rfl
    obtain ⟨hP0,hStore0,hWord0,_,hRead0⟩ := hFirst lane hl
    dsimp only at hP0 hStore0 hWord0 hRead0
    rw [hRow0] at hP0 hStore0 hWord0 hRead0
    have hStep : gate'.pos lane = step := (congrFun (hGate'.trans hIndex') lane).trans hP0
    obtain ⟨hP1,hStore1,hWord1,_,hRead1⟩ := hSecond lane hl
    dsimp only at hP1 hStore1 hWord1 hRead1
    rw [hStep,hRow1] at hP1 hStore1 hWord1 hRead1
    have hStop : reached.pos lane = stop := (congrFun hReached lane).trans hP1
    have hWords0 : WarmPageWords p l X t start batch r 0 := ⟨hRead0,hStore0,hWord0⟩
    have hWords1 : WarmPageWords p l X t step batch (r+64) 1 := ⟨hRead1,hStore1,hWord1⟩
    have hLast := warmPageWordsLatestAtExit hWords0 hWords1 slot flag
    rw [hStop]
    fin_cases slot <;> cases flag
    · refine ⟨start+primingScratchReads p batch r,by dsimp [step,stop]; omega, hStore0,?_⟩
      intro k hk j hj a hAccess hCover
      exact hLast k hk j hj a hAccess hCover
    · refine ⟨start+primingScratchReads p batch r+1,by dsimp [step,stop]; omega, hWord0,?_⟩
      intro k hk j hj a hAccess hCover
      exact hLast k hk j hj a hAccess hCover
    · refine ⟨step+primingScratchReads p batch (r+64),by dsimp [stop]; omega,hStore1,?_⟩
      intro k hk j hj a hAccess hCover
      exact hLast k hk j hj a hAccess hCover
    · refine ⟨step+primingScratchReads p batch (r+64)+1,by dsimp [stop]; omega,hWord1,?_⟩
      intro k hk j hj a hAccess hCover
      exact hLast k hk j hj a hAccess hCover

/-- The first warm metadata checkpoint is also available without its shuffle rank. -/
theorem WarmCacheStarted.refreshPagesOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (c : WarmCacheStarted p l X g batch)
    : Nonempty (WarmFirstPages p l X g batch) := by
  obtain ⟨next,_⟩ := c.refreshPagesWithRankOfMaximal hp hMax hFrame hg hw hb hLo hHi
  exact ⟨next⟩

/-- After the two private slots, actual address arithmetic reaches the first K reuse gate. -/
theorem WarmFirstPages.firstKeyGate {m : Mem0} {X : Execution} (hp : Pre p l m) {g batch : Nat}
    (c : WarmFirstPages p l X g batch) :
    ∃ gate : RecurringCacheGate l X g 0 2
        (warmFirstPagesFrame p l g batch) c.shuffles c.votes c.ends,
      gate.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let F := warmFirstPagesFrame p l g batch lane
  have hs := c.reached.checkpoint lane hl
  have hSeg : Seg kernel [] l t 3 957 [(7179,b32 2),(2535,b32 l.sharedBase)]
      960 [(1976,b32 (l.sharedBase+72)),(1122,b32 (l.sharedBase+16))] := by
    have hMem := hp.shared.2.1
    have hb : l.sharedBase < 2^32 := by omega
    have hAddr : l.sharedBase+16 < 2^32 := by omega
    have hEmpty : l.sharedBase+72 < 2^32 := by omega
    intro s h
    seg_fp h using
      (norm_bits [Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hAddr,Nat.mod_eq_of_lt hEmpty])
  have hAt : At (c.reached.state lane) 957
      ([(7179,b32 2),(2535,b32 l.sharedBase)]++F) := by
    apply hs.mono
    have hF : Holds (c.reached.state lane).regs F := hs.2.2.2.2
    exact ⟨hF.2.2.2.1,holds_mem hF (by
      simp [F,warmFirstPagesFrame,warmFirstFrame,openingWarmPublishedFrame,openingWarmFrame,
        warmStartFrame]),hF⟩
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeg hAt
  refine ⟨u,run_rtg hu,hU.mono ?_⟩
  have hF : Holds u.regs F := hU.2.2.2.2.2.2
  exact ⟨hU.2.2.2.2.1,hF.2.2.2.2.1,hU.2.2.2.2.2.1,hF⟩

/-- The first warm K packet acquires the spare slot in every maximal execution. -/
theorem WarmFirstPages.acquireFirstKeyPreservingLocalOfMaximal {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (c : WarmFirstPages p l X g batch) :
    ∃ done : RecurringCacheAcquired l X g 0 2
        (warmFirstPagesFrame p l g batch) c.shuffles c.votes c.ends,
      ∀ lane < 32, (∃ j, j+1 = done.pos lane ∧
        EmptyAcquire l X (warpLane l g lane,j) 2 1) ∧
        ∀ slot isRow, warmFirstMetadata p l X g batch lane (done.pos lane) slot isRow := by
  obtain ⟨gate,hPos⟩ := c.firstKeyGate hp
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hFresh : ∀ lane < 32, (recurringEmptyWait 0).result ∉
      (warmFirstPagesFrame p l g batch lane).map Prod.fst := fun _ _ => of_decide_eq_true rfl
  have hReady (lane : Nat) (hl : lane < 32)
      (hQuiet : ∀ j ≥ gate.pos lane, ∀ loc, ¬ X.AsyncArrive (warpLane l g lane,j) loc true) :
      CacheEmptyReady l X g 2 := by
    let t := warpLane l g lane
    have hs := (Step.sameWarp_lane hBlock hg hl).1
    have hWarp : warpIndex l g = warpIndex l t := hs.2
    have hThis : 14 ≤ warpIndex l t := hWarp ▸ hw
    have hBefore : ∀ i, ¬ X.AsyncArrive (t,i) (readyObject l t 2) true := by
      intro i
      by_cases hi : i < c.reached.pos lane
      · exact c.unpublishedKey lane hl i hi
      · exact hQuiet i (by rw [congrFun hPos lane]; omega) _
    have hReleased := Protocol.Loader.cacheEmptyPhaseBeforeSlotPublication hp hMax (g := t)
      hs.1.2.1 hThis 2 hBefore
    rw [show Thread.Mma.Observation.emptyObject l t 2 =
      Thread.Loader.emptyObject l g (kvUseStage 2) from by
        change initObject l (t/l.block) _ = initObject l (g/l.block) _
        have hCta : g/l.block = t/l.block := hs.1.2.2
        rw [hCta]
        rfl] at hReleased
    obtain ⟨st,hSt,hPhase⟩ := hReleased
    exact ⟨st,hSt,by rw [hPhase]; decide⟩
  obtain ⟨done,hDone⟩ :=
    gate.acquirePreservingLocalOfBlockedMaximal hp hMax hg 0 hFresh hReady
  refine ⟨done,fun lane hl => ?_⟩
  obtain ⟨j,hGateBefore,hJ,hAcquired⟩ := (hDone lane hl).1
  refine ⟨⟨j,hJ,hAcquired⟩,fun slot isRow => ?_⟩
  obtain ⟨write,hBefore,hStore,hLast⟩ := c.cells lane hl slot isRow
  have hLe : c.reached.pos lane ≤ j := congrFun hPos lane ▸ hGateBefore
  refine ⟨write,by omega,hStore,?_⟩
  intro k hk i hi a ha hc
  by_cases hOld : i < c.reached.pos lane
  · exact hLast k hk i hOld a ha hc
  exact False.elim ((hDone lane hl).2 i
    (by rw [congrFun hPos lane]; omega) hi a ha)

def warmFirstKeyCarry (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  recurringBarrierFacts l 0 2 1 ++ warmFirstPagesFrame p l g batch lane

def warmFirstKeyPointerCarry (p : Params) (l : Launch) (g batch lane : Nat) (more : Bool) :
    List (Nat × Value) :=
  (9,.pred more) :: warmFirstKeyCarry p l g batch lane

private def warmFirstKeyHeadBase (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  p.kLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.kLayout.headStride)

set_option maxRecDepth 4096 in
private theorem warmFirstPointerSeedOfAcquired {X : Execution} {g batch shuffles votes : Nat}
    {ends : Nat → Option TState}
    (cur : RecurringCacheAcquired l X g 0 2 (warmFirstPagesFrame p l g batch) shuffles votes ends) :
    ∃ start : SchedulerWarpReached l X g 966 (fun lane =>
      recurringScratchSaveInput l 0 0 p.kLayout.pageStride p.kLayout.rowStride
        (warmFirstKeyHeadBase p l g batch) ++ warmFirstKeyPointerCarry p l g batch lane true)
      shuffles votes ends, start.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let F := warmFirstKeyCarry p l g batch lane
  have hs : At (cur.state lane) 963 F := cur.checkpoint lane hl
  obtain ⟨u,hu,hU⟩ := warmPointerSeed (g := t) (cur.state lane) (hs.mono trivial)
  have hKeep : ((kernel.code.drop 963).take 3).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSeq : ((kernel.code.drop 963).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨huA,huF⟩ := loaderLinear (regs := F.map Prod.fst) (lo := 963) (n := 3)
    (by decide) (by decide) hs.1 hKeep hSeq hu
  have hF := holdsSchedulerFrame hs.2.2.2.2 huF (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u,run_rtg huA,hU.mono ?_⟩
  apply (holds_append ..).mpr
  refine ⟨?_,hU.2.2.2.2.2.2.1,hF⟩
  simp only [recurringScratchSaveInput,recurringScratchCarry,recurringSaveInputs,
    pointerReloadBase,pointerReloadAddress,List.cons_append,List.nil_append,Holds,
    warmFirstKeyHeadBase]
  repeat' apply And.intro
  all_goals first | trivial | exact holds_lookup hF rfl | exact holds_lookup hU.2.2.2.2 rfl

private theorem warmFirstKeySaveFrame (p : Params) (l : Launch) (g batch lane : Nat) (more : Bool) :
    RecurringSaveFrame 0 (warmFirstKeyPointerCarry p l g batch lane more) := by
  let F := warmFirstKeyPointerCarry p l g batch lane more
  have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7656 ∧ r ≠ 7658)) = true := rfl
  have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7656 ∧ pair.1 ≠ 7658 :=
    of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
  exact ⟨by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).1,
    by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).2,
    by set_option maxRecDepth 100000 in kernel_rfl⟩

set_option maxRecDepth 4096 in
private theorem warmKeyPointerSlotOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) (more : Bool)
    {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g 966 (fun lane =>
      recurringScratchSaveInput l 0 slot p.kLayout.pageStride p.kLayout.rowStride
        (warmFirstKeyHeadBase p l g batch) ++ warmFirstKeyPointerCarry p l g batch lane more)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ isRow,
      warmFirstMetadata p l X g batch lane (start.pos lane) slot isRow) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    ∃ done : SchedulerWarpReached l X g 978
        (fun lane => warmFirstKeyPointerCarry p l g batch lane more) shuffles votes ends,
      ∀ lane < 32,
        let t := warpLane l g lane
        let dst := pointerSaveAccess l t 0 slot
        let bs := (b64 (primingKRowPointer p batch head
          (warmFirstSlotRow p l g batch lane slot))).toBytes
        PrimingCellValue X t (done.pos lane) 977 dst bs ∧
        ∀ {saved : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (start.pos lane) saved cell data →
          DoesNotClobber cell ⟨977,.wr dst bs⟩ →
          PrimingCellValue X t (done.pos lane) saved cell data := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let base := warmFirstKeyHeadBase p l g batch
  let ps := p.kLayout.pageStride
  let rs := p.kLayout.rowStride
  let row := fun lane => warmFirstSlotRow p l g batch lane slot
  let page := fun lane => primingScratchPage p batch (row lane)
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hPS : ps < 2 ^ 64 := (hp.objectBytes 1 40 8 ps (by simp [ps,Params.objectWords])).1
  have hRS : rs < 2 ^ 64 := (hp.objectBytes 1 24 8 rs (by simp [rs,Params.objectWords])).1
  have hPageSigned (lane : Nat) : page lane < 2 ^ 31 := by
    dsimp [page,primingScratchPage]
    split
    · rename_i h
      exact ((hp.pageTable batch hb).2 (row lane/16) (by omega)).2
    · decide
  have hPayload (lane : Nat) :
      sourceScratchPayload (page lane) (row lane%16) ps rs base =
        primingKRowPointer p batch head (row lane) ∧
      sourceScratchPayload (page lane) (row lane%16) ps rs base < 2^64 := by
    have h := sourceScratchPayload_live hp 0 (primingScratchPageBound hp (row := row lane) hb)
      (Nat.mod_lt (row lane) (by decide)) hh
    exact ⟨h.1,h.2.1⟩
  obtain ⟨done,_,hSaved⟩ := recurringPointerSaveWarpPreservingOfMaximal hp hMax hg hw 0 slot page
    (fun lane => row lane%16) (fun lane _ => hPageSigned lane)
    (fun _ _ => (Nat.mod_lt _ (by decide : 0 < 16)).trans (by decide))
    hPS hRS (fun lane _ => (hPayload lane).2)
    (fun lane _ => warmFirstKeySaveFrame p l g batch lane more) start hCells
  refine ⟨done,fun lane hl => ?_⟩
  have h := hSaved lane hl
  dsimp only at h ⊢
  rw [(hPayload lane).1] at h
  exact h

set_option maxRecDepth 4096 in
private theorem warmSecondPointerSeed {X : Execution} {g batch shuffles votes : Nat}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 978
      (fun lane => warmFirstKeyPointerCarry p l g batch lane true) shuffles votes ends) :
    ∃ start : SchedulerWarpReached l X g 966 (fun lane =>
      recurringScratchSaveInput l 0 1 p.kLayout.pageStride p.kLayout.rowStride
        (warmFirstKeyHeadBase p l g batch) ++ warmFirstKeyPointerCarry p l g batch lane false)
      shuffles votes ends, start.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let F := warmFirstKeyCarry p l g batch lane
  have hs : At (cur.state lane) 978 ((9,.pred true)::F) := cur.checkpoint lane hl
  obtain ⟨u,hu,hU⟩ := warmPointerRoute (g := t) true
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  obtain ⟨v,hv,hV⟩ := warmPointerSecondEntry (g := t)
    (by set_option maxRecDepth 100000 in kernel_rfl) hU
  have hF := hV.2.2.2.2.2.2
  refine ⟨v,run_rtg (run_comp hu hv),hV.mono ?_⟩
  apply (holds_append ..).mpr
  refine ⟨?_,hV.2.2.2.2.2.1,hF⟩
  simp only [recurringScratchSaveInput,recurringScratchCarry,recurringSaveInputs,
    pointerReloadBase,pointerReloadAddress,List.cons_append,List.nil_append,Holds,
    warmFirstKeyHeadBase]
  repeat' apply And.intro
  all_goals first | trivial | exact holds_lookup hF rfl | exact holds_lookup hV.2.2.2.2 rfl

set_option maxRecDepth 4096 in
/-- Both computed K pointers are saved in their actual private slots before packing. -/
theorem WarmFirstPages.saveKeyPointersOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (c : WarmFirstPages p l X g batch) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    ∃ done : SchedulerWarpReached l X g 978
        (fun lane => warmFirstKeyPointerCarry p l g batch lane false) c.shuffles c.votes c.ends,
      ∀ lane < 32, ∀ slot : Fin 2,
        PrimingCellValue X (warpLane l g lane) (done.pos lane) 977
          (pointerSaveAccess l (warpLane l g lane) 0 slot)
          (b64 (primingKRowPointer p batch head
            (warmFirstSlotRow p l g batch lane slot))).toBytes :=
  by
  obtain ⟨acquired,hAcquired⟩ := c.acquireFirstKeyPreservingLocalOfMaximal hp hMax hg hw
  obtain ⟨start,hStart⟩ := warmFirstPointerSeedOfAcquired acquired
  have hCells (lane : Nat) (hl : lane < 32) (slot : Fin 2) (flag : Bool) :
      warmFirstMetadata p l X g batch lane (start.pos lane) slot flag := by
    rw [hStart]
    exact (hAcquired lane hl).2 slot flag
  obtain ⟨first,hFirst⟩ := warmKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 0 true
    start (fun lane hl flag => hCells lane hl 0 flag)
  obtain ⟨secondStart,hSecondStart⟩ := warmSecondPointerSeed first
  have hSecondCells (lane : Nat) (hl : lane < 32) (flag : Bool) :
      warmFirstMetadata p l X g batch lane (secondStart.pos lane) 1 flag := by
    rw [hSecondStart]
    apply (hFirst lane hl).2 (hCells lane hl 1 flag)
    intro dst _ hKind
    cases hKind
    rintro ⟨loc,hLoc,hWrite⟩
    simp [pointerSaveAccess,pointerSaveAddress,pointerReloadAddress,Acc.Covers,Loc.InRange]
      at hWrite
    cases flag <;>
      simp [scratchReloadAccess,recurringScratchWord,kvLocalOffset,Acc.Covers,Loc.InRange]
        at hLoc <;> omega
  obtain ⟨second,hSecond⟩ := warmKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 1 false
    secondStart hSecondCells
  refine ⟨second,fun lane hl slot => ?_⟩
  fin_cases slot
  · apply (hSecond lane hl).2
    · rw [hSecondStart]
      exact (hFirst lane hl).1
    · intro dst _ hKind
      cases hKind
      rintro ⟨loc,hLoc,hWrite⟩
      simp [pointerSaveAccess,pointerSaveAddress,pointerReloadAddress,Acc.Covers,Loc.InRange]
        at hLoc hWrite
      omega
  · exact (hSecond lane hl).1

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
