-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundHead
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundGateReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringWaitProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPointerProgress
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundPageIndex
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed
import Kernels.TmlFa4Fwd.Proof.LoaderWarmFirstRow
import Kernels.TmlFa4Fwd.Flow.Code.Part014

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
open LocalAccessCode (DoesNotClobber)

private def warmRoundPageFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) : List (Nat × Value) :=
  let tile := warmRoundTile p l g batch round
  let tid := warpLane l g lane%l.block
  [(7175,b32 slot.val),(8,.pred (decide (slot=0))),(1118,b32 (128*tile)),
    (1119,b32 (8*(tid%8)))] ++ warmRoundFrame p l g batch round lane

private def warmRoundPageIndexedFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) : List (Nat × Value) :=
  let tile := warmRoundTile p l g batch round
  let tid := warpLane l g lane%l.block
  [(1969,b32 (primingLaneRow tile tid)),(1964,b32 (64*slot.val))] ++
    warmRoundPageFrame p l g batch round lane slot

private theorem warmRoundIndexRun {l : Launch} {g high round tid : Nat}
    (hRound : round ≤ high) (hTile : 128*(high-round)+127 < 2^31) (hHigh : 128*high < 2^32)
    (hTid : tid < 512) {s : TState} {F : List (Nat × Value)}
    (hKeep₁ : ((kernel.code.drop 917).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hKeep₂ : ((kernel.code.drop 921).take 8).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 917 ([(1116,b32 high),(7174,b32 round),(1061,b32 tid)] ++ F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 929 ([(1969,b32 (primingLaneRow (high-round) tid)),(1964,b32 0),(7175,b32 0),
        (8,.pred true),(1118,b32 (128*(high-round))),(1119,b32 (8*(tid%8)))] ++ F) := by
  obtain ⟨seed,hSeed,hAt⟩ := warmPageTileSeedCore (l := l) (g := g) hRound hHigh s
    (hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩)
  have hKeep : ((kernel.code.drop 917).take 4).all
      (fun ins => (1061 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hm
    simp only [List.all_cons,Bool.and_eq_true]
    refine ⟨?_,List.all_eq_true.mp hKeep₁ ins hm⟩
    have hTidSafe : ((kernel.code.drop 917).take 4).all
        (fun i => !(writesRegs i.op).contains 1061) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact List.all_eq_true.mp hTidSafe ins hm
  obtain ⟨hSeedA,hFrame⟩ := loaderLinear (regs := 1061 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hKeep (by set_option maxRecDepth 100000 in kernel_rfl) hSeed
  have hTidS := (hFrame 1061 (by simp)).trans hs.2.2.2.2.2.2.1
  have hf := holdsSchedulerFrame ((holds_append ..).mp hs.2.2.2.2).2 hFrame
    (fun r hm => .tail 1061 (List.mem_map_of_mem hm))
  have hInput : At seed 921 ([(1118,b32 (128*(high-round))),(1061,b32 tid),
      (7175,b32 (0 : Fin 2).val),(775,.pred true)] ++ F) :=
    hAt.mono ⟨hAt.2.2.2.2.1,hTidS,hAt.2.2.2.2.2.1,hAt.2.2.2.2.2.2.1,hf⟩
  obtain ⟨u,hu,hU⟩ := warmPageIndexRunFromSlot hTile hTid 0 true hKeep₂ hInput
  exact ⟨u,run_rtg (run_comp hSeedA hu),by simpa using hU⟩

private theorem warmRoundIndexOfHead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round : Nat}
    (hRound : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hHigh : 128*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-2)+127 < 2^31)
    (c : WarmRoundHead p l X g batch round) :
    ∃ idx : SchedulerWarpReached l X g 929
        (fun lane => warmRoundPageIndexedFrame p l g batch round lane 0)
        c.shuffles c.votes c.ends,
      idx.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  let F := warmRoundFrame p l g batch round lane
  have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hC := c.reached.checkpoint lane hl
  have hRegs : Holds (c.reached.state lane).regs F := hC.2.2.2.2
  have hAt : At (c.reached.state lane) 917
      ([(1116,b32 (n-2)),(7174,b32 round),(1061,b32 tid)]++F) := by
    apply hC.mono
    refine ⟨hRegs.2.2.2.2.2.1,hRegs.1,?_,hRegs⟩
    exact holds_mem hRegs (by
      simp [F,warmRoundFrame,openingWarmFrame,
        warmStartFrame,warmPageRoots,warmLaneRoots,tid,t])
  obtain ⟨u,hu,hU⟩ := warmRoundIndexRun (g := t) (show round ≤ n-2 by omega)
    (show 128*(n-2-round)+127 < 2^31 by omega) (by omega) hTid
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hAt
  exact ⟨u,hu,hU⟩

private theorem warmRoundRowBound {p : Params} {l : Launch} {g batch round : Nat}
    (hTile : 128*warmRoundTile p l g batch round+127 < 2^31) (tid : Nat) (slot : Fin 2) :
    primingLaneRow (warmRoundTile p l g batch round) tid+64*slot.val < 2^31 := by
  have hs := slot.isLt
  have hm := Nat.mod_lt (tid/8) (by decide : 0 < 8)
  have hn := Nat.mod_lt tid (by decide : 0 < 8)
  unfold primingLaneRow kvCopyColumn
  simp only [Bool.false_eq_true,ite_false]
  omega

private theorem warmRoundPageGuard {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round shuffles votes : Nat} (hb : batch < p.batch)
    (hTile : 128*warmRoundTile p l g batch round+127 < 2^31) (slot : Fin 2)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 929
      (fun lane => warmRoundPageIndexedFrame p l g batch round lane slot) shuffles votes ends) :
    let row := fun lane =>
      primingLaneRow (warmRoundTile p l g batch round) (warpLane l g lane%l.block)+64*slot.val
    ∃ gate : SchedulerWarpReached l X g 939
        (fun lane => recurringPageGuardInput p l 0 slot batch (row lane) ++
          warmRoundPageFrame p l g batch round lane slot) shuffles votes ends,
      gate.pos = cur.pos := by
  dsimp only
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tile := warmRoundTile p l g batch round
  let tid := t%l.block
  let base := primingLaneRow tile tid
  let row := base+64*slot.val
  let F := warmRoundPageFrame p l g batch round lane slot
  have hSmall : row < 2^31 := warmRoundRowBound hTile tid slot
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

private theorem warmRoundPageRefreshFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) : RecurringRefreshFrame 0 (warmRoundPageFrame p l g batch round lane slot) := by
  let F := warmRoundPageFrame p l g batch round lane slot
  constructor
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · intro pair hm hEq
    have hNo : (recurringPageSite 0).physicalPage ∉ F.map Prod.fst := of_decide_eq_true rfl
    exact hNo (hEq ▸ List.mem_map_of_mem hm)
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

private theorem warmRoundSecondIndexOfPage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round shuffles votes : Nat}
    (hTile : 128*warmRoundTile p l g batch round+127 < 2^31)
    {ends : Nat → Option TState}
    (done : SchedulerWarpReached l X g 954
      (fun lane => warmRoundPageFrame p l g batch round lane 0) shuffles votes ends) :
    ∃ idx : SchedulerWarpReached l X g 929
        (fun lane => warmRoundPageIndexedFrame p l g batch round lane 1) shuffles votes ends,
      idx.pos = done.pos := by
  apply done.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let tile := warmRoundTile p l g batch round
  let F := warmRoundFrame p l g batch round lane
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
    simp [F,warmRoundFrame,openingWarmFrame,
      warmStartFrame,warmPageRoots,warmLaneRoots,tid,t]
  obtain ⟨v,hv,hV⟩ := warmPageIndexRunFromSlot (g := t) hTile hTid 1 false
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeed
  exact ⟨v,run_rtg (run_comp hu hv),hV⟩

/-- The warm K prelude carries the physical ring cursor and its lane's column. -/
def warmRoundPagesFrame (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  (1119,b32 (8*(warpLane l g lane%l.block%8)))::warmRoundFrame p l g batch round lane

def warmRoundSlotRow (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2) :
    Nat :=
  primingLaneRow (warmRoundTile p l g batch round) (warpLane l g lane%l.block)+64*slot.val

def warmRoundMetadata (p : Params) (l : Launch) (X : Execution)
    (g batch round lane index : Nat) (slot : Fin 2) (isRow : Bool) : Prop :=
  let t := warpLane l g lane
  let row := warmRoundSlotRow p l g batch round lane slot
  let op := recurringScratchWord 0 isRow
  PrimingCellValue X t index op.store (scratchReloadAccess l t op slot)
    (b32 (if isRow then row%16 else primingScratchPage p batch row)).toBytes

/-- Both lane-private page slots of warm round `round` have been refreshed before its K
acquire. -/
structure WarmRoundPages (p : Params) (l : Launch) (X : Execution) (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 957 (warmRoundPagesFrame p l g batch round)
    shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+64*round
  cells : ∀ lane < 32, ∀ slot isRow,
    warmRoundMetadata p l X g batch round lane (reached.pos lane) slot isRow

set_option maxRecDepth 4096 in
/-- A loader warp actually writes both private scratch slots in each warm round. -/
theorem WarmRoundHead.refreshPagesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : WarmRoundHead p l X g batch round) :
    Nonempty (WarmRoundPages p l X g batch round) := by
  let tile := warmRoundTile p l g batch round
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hTile : 128*tile+127 < 2^31 := by dsimp [tile,warmRoundTile]; omega
  obtain ⟨idx,hIndex⟩ := warmRoundIndexOfHead hp hRound (by omega) c
  obtain ⟨gate,hGate⟩ := warmRoundPageGuard hp hb hTile 0 idx
  let row := fun lane => primingLaneRow tile (warpLane l g lane%l.block)+64*(0 : Fin 2).val
  obtain ⟨first,hFirst⟩ := recurringPageRefreshWarpOfMaximal hp hMax hFrame hg hw hb 0 0 row
    (fun lane _ => warmRoundRowBound hTile (warpLane l g lane%l.block) 0)
    (fun lane _ => warmRoundPageRefreshFrame p l g batch round lane 0) gate
  obtain ⟨idx',hIndex'⟩ := warmRoundSecondIndexOfPage hp hTile first
  obtain ⟨gate',hGate'⟩ := warmRoundPageGuard hp hb hTile 1 idx'
  let row' := fun lane => primingLaneRow tile (warpLane l g lane%l.block)+64*(1 : Fin 2).val
  obtain ⟨second,hSecond⟩ := recurringPageRefreshWarpOfMaximal hp hMax hFrame hg hw hb 0 1 row'
    (fun lane _ => warmRoundRowBound hTile (warpLane l g lane%l.block) 1)
    (fun lane _ => warmRoundPageRefreshFrame p l g batch round lane 1) gate'
  obtain ⟨reached,hReached⟩ := second.advanceLocalWithPosition (pc' := 957)
    (G := warmRoundPagesFrame p l g batch round) (by
    intro lane hl
    let t := warpLane l g lane
    let F := warmRoundPagesFrame p l g batch round lane
    have hs := second.checkpoint lane hl
    have hAt : At (second.state lane) 954 ([(8,.pred false),(1118,b32 (128*tile))]++F) :=
      hs.mono hs.2.2.2.2.2
    obtain ⟨u,hu,hU⟩ := warmPageSlotRoute (g := t) false
      (by set_option maxRecDepth 100000 in kernel_rfl) hAt
    exact ⟨u,run_rtg hu,hU.mono hU.2.2.2.2.2.2.2⟩)
  refine ⟨⟨c.shuffles,c.votes,c.ends,reached,c.rank,?_⟩⟩
  intro lane hl slot flag
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

set_option maxRecDepth 4096 in
/-- After the two private slots, actual address arithmetic reaches the round's K reuse gate. -/
theorem WarmRoundPages.keyGate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round : Nat} (c : WarmRoundPages p l X g batch round) :
    ∃ gate : RecurringCacheGate l X g 0 (cacheUseOfRound round)
        (warmRoundPagesFrame p l g batch round) c.shuffles c.votes c.ends,
      gate.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let use := cacheUseOfRound round
  let F := warmRoundPagesFrame p l g batch round lane
  have hs := c.reached.checkpoint lane hl
  have hF : Holds (c.reached.state lane).regs F := hs.2.2.2.2
  have hAt : At (c.reached.state lane) 957
      (recurringBarrierInput l 0 (kvUseStage use) (cacheEmptyParity use)++F) := by
    apply hs.mono
    refine (holds_append ..).mpr ⟨⟨hF.2.2.2.1,holds_mem hF ?_,hF.2.2.2.2.1,trivial⟩,hF⟩
    simp [F,warmRoundPagesFrame,warmRoundFrame,openingWarmFrame,warmStartFrame]
  obtain ⟨u,hu,hU⟩ := roundStraightFrameAll (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringBarrierPrep hp (g := t) 0 (kvUseStage use) (cacheEmptyParity use)) hAt
  exact ⟨u,run_rtg hu,hU⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch round : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
include hp hMax hFrame hg hw hb hLo hHi hReleased

/-- The K packet of warm round `round` passes its empty poll once the MMA has returned the
earlier generations of its slot. The lane-side bound comes from the shuffle rank. -/
theorem WarmRoundPages.acquireKeyPreservingLocalOfMaximal (c : WarmRoundPages p l X g batch round) :
    ∃ done : RecurringCacheAcquired l X g 0 (cacheUseOfRound round)
        (warmRoundPagesFrame p l g batch round) c.shuffles c.votes c.ends,
      ∀ lane < 32, (∃ j, j+1 = done.pos lane ∧
        EmptyAcquire l X (warpLane l g lane,j) (kvUseStage (cacheUseOfRound round))
          (cacheEmptyParity (cacheUseOfRound round))) ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  obtain ⟨gate,hPos⟩ := c.keyGate hp
  have hFresh : ∀ lane < 32, (recurringEmptyWait 0).result ∉
      (warmRoundPagesFrame p l g batch round lane).map Prod.fst := fun _ _ => of_decide_eq_true rfl
  obtain ⟨done,hDone⟩ := gate.acquireOfReleases hp hMax hFrame hg hw hb hLo hHi 0 hFresh
    (by rw [c.rank]; unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega) hReleased
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

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
def warmRoundKeyCarry (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  recurringBarrierFacts l 0 (kvUseStage (cacheUseOfRound round))
    (cacheEmptyParity (cacheUseOfRound round)) ++ warmRoundPagesFrame p l g batch round lane

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
def warmRoundKeyPointerCarry (p : Params) (l : Launch) (g batch round lane : Nat)
    (more : Bool) : List (Nat × Value) :=
  (9,.pred more) :: warmRoundKeyCarry p l g batch round lane

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
private def warmRoundKeyHeadBase (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  p.kLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.kLayout.headStride)

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
set_option maxRecDepth 4096 in
private theorem warmRoundPointerSeedOfAcquired {p : Params} {l : Launch} {X : Execution}
    {g batch round shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : RecurringCacheAcquired l X g 0 (cacheUseOfRound round)
      (warmRoundPagesFrame p l g batch round)
      shuffles votes ends) :
    ∃ start : SchedulerWarpReached l X g 966 (fun lane =>
      recurringScratchSaveInput l 0 0 p.kLayout.pageStride p.kLayout.rowStride
        (warmRoundKeyHeadBase p l g batch) ++ warmRoundKeyPointerCarry p l g batch round lane true)
      shuffles votes ends, start.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let F := warmRoundKeyCarry p l g batch round lane
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
    warmRoundKeyHeadBase]
  repeat' apply And.intro
  all_goals first | trivial | exact holds_lookup hF rfl | exact holds_lookup hU.2.2.2.2 rfl

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
private theorem warmRoundKeySaveFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (more : Bool) :
    RecurringSaveFrame 0 (warmRoundKeyPointerCarry p l g batch round lane more) := by
  let F := warmRoundKeyPointerCarry p l g batch round lane more
  have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7656 ∧ r ≠ 7658)) = true := rfl
  have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7656 ∧ pair.1 ≠ 7658 :=
    of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
  exact ⟨by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).1,
    by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).2,
    by set_option maxRecDepth 100000 in kernel_rfl⟩

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
set_option maxRecDepth 4096 in
private theorem warmRoundKeyPointerSlotOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) (more : Bool)
    {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g 966 (fun lane =>
      recurringScratchSaveInput l 0 slot p.kLayout.pageStride p.kLayout.rowStride
        (warmRoundKeyHeadBase p l g batch) ++ warmRoundKeyPointerCarry p l g batch round lane more)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ isRow,
      warmRoundMetadata p l X g batch round lane (start.pos lane) slot isRow) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    ∃ done : SchedulerWarpReached l X g 978
        (fun lane => warmRoundKeyPointerCarry p l g batch round lane more) shuffles votes ends,
      ∀ lane < 32,
        let t := warpLane l g lane
        let dst := pointerSaveAccess l t 0 slot
        let bs := (b64 (primingKRowPointer p batch head
          (warmRoundSlotRow p l g batch round lane slot))).toBytes
        PrimingCellValue X t (done.pos lane) 977 dst bs ∧
        ∀ {saved : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (start.pos lane) saved cell data →
          DoesNotClobber cell ⟨977,.wr dst bs⟩ →
          PrimingCellValue X t (done.pos lane) saved cell data := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let base := warmRoundKeyHeadBase p l g batch
  let ps := p.kLayout.pageStride
  let rs := p.kLayout.rowStride
  let row := fun lane => warmRoundSlotRow p l g batch round lane slot
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
    (fun lane _ => warmRoundKeySaveFrame p l g batch round lane more) start hCells
  refine ⟨done,fun lane hl => ?_⟩
  have h := hSaved lane hl
  dsimp only at h ⊢
  rw [(hPayload lane).1] at h
  exact h

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
set_option maxRecDepth 4096 in
private theorem warmRoundSecondPointerSeed {p : Params} {l : Launch} {X : Execution}
    {g batch round shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 978
      (fun lane => warmRoundKeyPointerCarry p l g batch round lane true) shuffles votes ends) :
    ∃ start : SchedulerWarpReached l X g 966 (fun lane =>
      recurringScratchSaveInput l 0 1 p.kLayout.pageStride p.kLayout.rowStride
        (warmRoundKeyHeadBase p l g batch) ++ warmRoundKeyPointerCarry p l g batch round lane false)
      shuffles votes ends, start.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let F := warmRoundKeyCarry p l g batch round lane
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
    warmRoundKeyHeadBase]
  repeat' apply And.intro
  all_goals first | trivial | exact holds_lookup hF rfl | exact holds_lookup hV.2.2.2.2 rfl

set_option maxRecDepth 4096 in
/-- Both computed K pointers are saved in their actual private slots before packing. -/
theorem WarmRoundPages.saveKeyPointersOfMaximal (c : WarmRoundPages p l X g batch round) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    ∃ done : SchedulerWarpReached l X g 978
        (fun lane => warmRoundKeyPointerCarry p l g batch round lane false)
        c.shuffles c.votes c.ends,
      ∀ lane < 32, ∀ slot : Fin 2,
        PrimingCellValue X (warpLane l g lane) (done.pos lane) 977
          (pointerSaveAccess l (warpLane l g lane) 0 slot)
          (b64 (primingKRowPointer p batch head
            (warmRoundSlotRow p l g batch round lane slot))).toBytes :=
  by
  obtain ⟨acquired,hAcquired⟩ :=
    c.acquireKeyPreservingLocalOfMaximal hp hMax hFrame hg hw hb hLo hHi hReleased
  obtain ⟨start,hStart⟩ := warmRoundPointerSeedOfAcquired acquired
  have hCells (lane : Nat) (hl : lane < 32) (slot : Fin 2) (flag : Bool) :
      warmRoundMetadata p l X g batch round lane (start.pos lane) slot flag := by
    rw [hStart]
    exact (hAcquired lane hl).2 slot flag
  obtain ⟨first,hFirst⟩ := warmRoundKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 0 true
    start (fun lane hl flag => hCells lane hl 0 flag)
  obtain ⟨secondStart,hSecondStart⟩ := warmRoundSecondPointerSeed first
  have hSecondCells (lane : Nat) (hl : lane < 32) (flag : Bool) :
      warmRoundMetadata p l X g batch round lane (secondStart.pos lane) 1 flag := by
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
  obtain ⟨second,hSecond⟩ := warmRoundKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 1 false
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

omit hp hMax hFrame hg hw hb hLo hHi hReleased in
/-- The page and row words of the warm scratch slots lie apart from every saved pointer. -/
theorem metadataApartFromPointerSave (l : Launch) (t : Nat) (site : Fin 4) (slot slot' : Fin 2)
    (flag : Bool) (pc : Nat) (bs : List Byte) :
    DoesNotClobber (scratchReloadAccess l t (recurringScratchWord 0 flag) slot)
      ⟨pc,.wr (pointerSaveAccess l t site slot') bs⟩ := by
  intro dst _ hKind
  cases hKind
  rintro ⟨loc,hLoc,hWrite⟩
  have hs := slot.isLt
  have hs' := slot'.isLt
  simp [pointerSaveAccess,pointerSaveAddress,pointerReloadAddress,Acc.Covers,Loc.InRange]
    at hWrite
  cases flag <;>
    simp [scratchReloadAccess,recurringScratchWord,kvLocalOffset,Acc.Covers,Loc.InRange]
      at hLoc <;> split at hWrite <;> omega

set_option maxRecDepth 4096 in
/-- Both K pointers are saved and the page and row words of both scratch slots stay current. -/
theorem WarmRoundPages.saveKeyPointersKeepingOfMaximal (c : WarmRoundPages p l X g batch round) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    ∃ done : SchedulerWarpReached l X g 978
        (fun lane => warmRoundKeyPointerCarry p l g batch round lane false)
        c.shuffles c.votes c.ends,
      ∀ lane < 32, (∀ slot : Fin 2,
        PrimingCellValue X (warpLane l g lane) (done.pos lane) 977
          (pointerSaveAccess l (warpLane l g lane) 0 slot)
          (b64 (primingKRowPointer p batch head
            (warmRoundSlotRow p l g batch round lane slot))).toBytes) ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  obtain ⟨acquired,hAcquired⟩ :=
    c.acquireKeyPreservingLocalOfMaximal hp hMax hFrame hg hw hb hLo hHi hReleased
  obtain ⟨start,hStart⟩ := warmRoundPointerSeedOfAcquired acquired
  have hCells (lane : Nat) (hl : lane < 32) (slot : Fin 2) (flag : Bool) :
      warmRoundMetadata p l X g batch round lane (start.pos lane) slot flag := by
    rw [hStart]
    exact (hAcquired lane hl).2 slot flag
  obtain ⟨first,hFirst⟩ := warmRoundKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 0 true
    start (fun lane hl flag => hCells lane hl 0 flag)
  obtain ⟨secondStart,hSecondStart⟩ := warmRoundSecondPointerSeed first
  have hMid (lane : Nat) (hl : lane < 32) (slot : Fin 2) (flag : Bool) :
      warmRoundMetadata p l X g batch round lane (secondStart.pos lane) slot flag := by
    rw [hSecondStart]
    exact (hFirst lane hl).2 (hCells lane hl slot flag)
      (metadataApartFromPointerSave l _ 0 slot 0 flag _ _)
  obtain ⟨second,hSecond⟩ := warmRoundKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 1 false
    secondStart (fun lane hl flag => hMid lane hl 1 flag)
  refine ⟨second,fun lane hl => ⟨fun slot => ?_,fun slot flag => ?_⟩⟩
  · fin_cases slot
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
  · exact (hSecond lane hl).2 (hMid lane hl slot flag)
      (metadataApartFromPointerSave l _ 0 slot 1 flag _ _)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
