-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundHead
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundGateReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageHistory
import all Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageSlots
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringLengthSeed
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Lemmas.Flow.Run

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The KV tile loaded by steady round `round`. The rounds proceed towards tile zero. -/
def steadyRoundTile (p : Params) (l : Launch) (g batch round : Nat) : Nat :=
  Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-2-round

/-- The live registers of a loader lane at the head of steady round `round`. -/
def steadyRoundFrame (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  steadyCacheHeadFrame l round (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (steadyRoundCarry p l g batch lane)

/-- The round frame with the tile index and its row offset, which the K packet reads. -/
def steadyRoundTileFrame (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  let tile := steadyRoundTile p l g batch round
  [(1144,b32 tile),(1145,b32 (128*tile))] ++ steadyRoundFrame p l g batch round lane

/-- The frame of the page loop while it refreshes slot `slot`. -/
def steadyRoundPageFrame (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2) :
    List (Nat × Value) :=
  let tid := warpLane l g lane%l.block
  [(7182,b32 slot.val),(11,.pred (decide (slot = 0))),
    (1148,b32 (primingLaneRow (steadyRoundTile p l g batch round) tid))] ++
    steadyRoundTileFrame p l g batch round lane

/-- The KV row of a lane's scratch slot in steady round `round`. -/
def steadyRoundSlotRow (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2) :
    Nat :=
  primingLaneRow (steadyRoundTile p l g batch round) (warpLane l g lane%l.block)+64*slot.val

/-- The page or row word of a scratch slot written by the page loop of steady round `round`
is the latest write of its cell at `index`. -/
def steadyRoundMetadata (p : Params) (l : Launch) (X : Execution)
    (g batch round lane index : Nat) (slot : Fin 2) (isRow : Bool) : Prop :=
  let t := warpLane l g lane
  let row := steadyRoundSlotRow p l g batch round lane slot
  let op := recurringScratchWord 2 isRow
  PrimingCellValue X t index op.store (scratchReloadAccess l t op slot)
    (b32 (if isRow then row%16 else primingScratchPage p batch row)).toBytes

/-- Both lane-private page slots of steady round `round` have been refreshed before its K
acquire. -/
structure SteadyRoundPages (p : Params) (l : Launch) (X : Execution) (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1427 (steadyRoundTileFrame p l g batch round)
    shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+64*round
  cells : ∀ lane < 32, ∀ slot isRow,
    steadyRoundMetadata p l X g batch round lane (reached.pos lane) slot isRow

set_option maxRecDepth 4096 in
private theorem steadyRoundTileLocal {l : Launch} {g high round tid : Nat} {s : TState}
    {F : List (Nat × Value)} (hRound : round ≤ high) (hHigh : 128*high+64 < 2^31)
    (hKeep : ((kernel.code.drop 1396).take 5).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1396 ([(1116,b32 high),(7181,b32 round),(2130,b32 (primingLaneRow 0 tid))] ++
      F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1401 ([(1148,b32 (primingLaneRow (high-round) tid)),(7182,b32 0),
        (778,.pred true)] ++ ([(1144,b32 (high-round)),(1145,b32 (128*(high-round)))] ++ F)) := by
  obtain ⟨u,hu,hU⟩ := roundStraightFrameAll (by decide) (by decide) hKeep
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (steadyPageTileSeed (l := l) (g := g) (tid := tid) hRound (by omega)) hs
  obtain ⟨v,hv,hV⟩ := steadyKeyCopyTileCore (l := l) (g := g) hRound (by omega) s
    (hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩)
  have hvA := (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv).1
  have hRest : run kernel Assumptions.all l g 3 v = some u := by
    have h := run_add (K := kernel) (A := Assumptions.all) (L := l) (g := g) 2 3 s
    rw [hvA,Option.bind_some] at h
    rw [← h]
    exact hu
  have hRest' := loaderRunWithoutAssumptions (lo := 1398) (len := 3) (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) hRest (le_of_eq hV.1.symm)
    (by rw [hV.1])
  obtain ⟨_,hKept⟩ := loaderLinear (regs := [1144,1145]) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hRest'
  exact ⟨u,run_rtg hu,hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,
    (hKept 1144 (by simp)).trans hV.2.2.2.2.1,(hKept 1145 (by simp)).trans hV.2.2.2.2.2.1,
    hU.2.2.2.2.2.2.2⟩⟩

set_option maxRecDepth 4096 in
private theorem steadyRoundTileOfHead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : SteadyRoundHead p l X g batch round) :
    ∃ start : SchedulerWarpReached l X g 1401 (fun lane =>
        [(7182,b32 (0 : Fin 2).val),(778,.pred (decide ((0 : Fin 2) = 0))),
          (1148,b32 (primingLaneRow (steadyRoundTile p l g batch round)
            (warpLane l g lane%l.block)))] ++ steadyRoundTileFrame p l g batch round lane)
        c.shuffles c.votes c.ends,
      start.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  let F := steadyRoundFrame p l g batch round lane
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hs := c.reached.checkpoint lane hl
  have hF : Holds (c.reached.state lane).regs F := hs.2.2.2.2
  have hAt : At (c.reached.state lane) 1396
      ([(1116,b32 (n-2)),(7181,b32 round),(2130,b32 (primingLaneRow 0 tid))] ++ F) := by
    refine hs.mono ⟨holds_mem hF ?_,hF.1,holds_mem hF ?_,hF⟩ <;>
      simp [F,n,steadyRoundFrame,steadyCacheHeadFrame,steadyRoundCarry,warmRoundCarry,tid,t]
  obtain ⟨u,hu,hU⟩ := steadyRoundTileLocal (g := t) (show round ≤ n-2 by omega) (by omega)
    (by set_option maxRecDepth 100000 in kernel_rfl) hAt
  exact ⟨u,hu,hU.mono ⟨hU.2.2.2.2.2.1,hU.2.2.2.2.2.2.1,hU.2.2.2.2.1,hU.2.2.2.2.2.2.2⟩⟩

set_option maxRecDepth 4096 in
private theorem steadyRoundSlotIndex {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round shuffles votes : Nat} (hb : batch < p.batch)
    (slot : Fin 2) {ends : Nat → Option TState}
    (hBound : ∀ lane < 32,
      primingLaneRow (steadyRoundTile p l g batch round) (warpLane l g lane%l.block)+64 < 2^31)
    (cur : SchedulerWarpReached l X g 1401 (fun lane =>
        [(7182,b32 slot.val),(778,.pred (decide (slot = 0))),
          (1148,b32 (primingLaneRow (steadyRoundTile p l g batch round)
            (warpLane l g lane%l.block)))] ++ steadyRoundTileFrame p l g batch round lane)
        shuffles votes ends) :
    ∃ gate : SchedulerWarpReached l X g 1413 (fun lane =>
        recurringPageGuardInput p l 1 slot batch (steadyRoundSlotRow p l g batch round lane slot) ++
          steadyRoundPageFrame p l g batch round lane slot) shuffles votes ends,
      gate.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let base := primingLaneRow (steadyRoundTile p l g batch round) tid
  let row := base+64*slot.val
  let F := steadyRoundPageFrame p l g batch round lane slot
  let T := steadyRoundTileFrame p l g batch round lane
  have hs := cur.checkpoint lane hl
  have hCore : Seg kernel [] l t 2 1401 [(7182,b32 slot.val),(778,.pred (decide (slot = 0)))]
      1403 [(11,.pred (decide (slot = 0))),(2131,b32 (64*slot.val))] := by
    fin_cases slot <;> intro u hu <;> seg_fp hu using rfl
  obtain ⟨a,ha,hA⟩ := hCore (cur.state lane) (hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩)
  let G := (7182,b32 slot.val) :: (1148,b32 base) :: T
  obtain ⟨haA,haF⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ha
  have hG := holdsSchedulerFrame
    (show Holds (cur.state lane).regs G from ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.2⟩) haF
    (fun _ hm => List.mem_map_of_mem hm)
  have hRow : row < 2^31 := by
    have h1 := slot.isLt
    have h2 := hBound lane hl
    simp only [row,base,tid,t]
    omega
  have hLen : p.kLength batch < 2^31 := by have := (hp.lengths batch hb).2.2; omega
  have hInput : At a 1403 (recurringPageIndexInput 1 base (p.kLength batch) slot) := by
    apply hA.mono
    simp only [recurringPageIndexInput,recurringPageSite,Holds]
    refine ⟨hG.2.1,hA.2.2.2.2.2.1,?_⟩
    repeat' apply And.intro
    all_goals first | trivial | exact holds_lookup hG rfl
  obtain ⟨u,hu,hU⟩ := recurringPageIndexCore (l := l) (g := t) 1 slot hRow hLen a hInput
  have hF : Holds a.regs F := ⟨hG.1,hA.2.2.2.2.1,hG.2⟩
  obtain ⟨huA,huF⟩ := loaderLinear (regs := F.map Prod.fst) (lo := 1403) (n := 10)
    (by decide) (by decide) hA.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hCarry := holdsSchedulerFrame hF huF (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u,run_rtg (run_comp haA huA),hU.mono ?_⟩
  change Holds u.regs (recurringPageGuardInput p l 1 slot batch row ++ F)
  apply (holds_append ..).mpr
  refine ⟨(holds_append ..).mpr ⟨hU.2.2.2.2,?_⟩,hCarry⟩
  simp only [pageStoreCarry,recurringPageBatchInputs,recurringPageStoreSite,recurringPageSite,
    List.cons_append,Holds]
  repeat' apply And.intro
  all_goals first
    | trivial
    | exact holds_lookup hCarry rfl
    | exact holds_lookup hU.2.2.2.2 rfl

private theorem steadyRoundRefreshFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) :
    RecurringRefreshFrame 1 (steadyRoundPageFrame p l g batch round lane slot) := by
  let F := steadyRoundPageFrame p l g batch round lane slot
  constructor
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · intro pair hm hEq
    have hNo : (recurringPageSite 1).physicalPage ∉ F.map Prod.fst := of_decide_eq_true rfl
    exact hNo (hEq ▸ List.mem_map_of_mem hm)
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

private theorem steadyRoundRowBound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch round : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (tid : Nat) :
    primingLaneRow (steadyRoundTile p l g batch round) tid+64 < 2^31 := by
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hm := Nat.mod_lt (tid/8) (by decide : 0 < 8)
  have hn := Nat.mod_lt tid (by decide : 0 < 8)
  unfold primingLaneRow kvCopyColumn steadyRoundTile
  simp only [Bool.false_eq_true,ite_false]
  omega

set_option maxRecDepth 4096 in
private theorem steadyRoundRouteLocal {p : Params} {l : Launch} {g batch round lane : Nat}
    {s : TState} (slot : Fin 2)
    (hs : At s 1424 (steadyRoundPageFrame p l g batch round lane slot)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) s u ∧
      At u (if decide (slot = 0) then 1401 else 1427)
        ([(7182,b32 1),(778,.pred false),
          (1148,b32 (primingLaneRow (steadyRoundTile p l g batch round)
            (warpLane l g lane%l.block)))] ++ steadyRoundTileFrame p l g batch round lane) := by
  obtain ⟨u,hu,hU⟩ := steadyPageSlotRoute (l := l) (g := warpLane l g lane)
    (F := steadyRoundTileFrame p l g batch round lane) (decide (slot = 0))
    (by set_option maxRecDepth 100000 in kernel_rfl) (hs.mono hs.2.2.2.2.2)
  exact ⟨u,run_rtg hu,hU⟩

set_option maxRecDepth 4096 in
/-- A loader warp refreshes both lane-private page slots in each steady round and reaches
the K gate with the tile index and its row offset in registers. -/
theorem SteadyRoundHead.refreshPagesOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : SteadyRoundHead p l X g batch round) :
    Nonempty (SteadyRoundPages p l X g batch round) := by
  have hBound : ∀ lane < 32,
      primingLaneRow (steadyRoundTile p l g batch round) (warpLane l g lane%l.block)+64 < 2^31 :=
    fun lane _ => steadyRoundRowBound hp hb hLo hHi _
  obtain ⟨start,hStart⟩ := steadyRoundTileOfHead hp hb hLo hHi hRound c
  obtain ⟨gate,hGate⟩ := steadyRoundSlotIndex hp hb 0 hBound start
  let row := fun lane => steadyRoundSlotRow p l g batch round lane 0
  obtain ⟨first,hFirst⟩ := recurringPageRefreshWarpOfMaximal hp hMax hFrame hg hw hb 1 0 row
    (fun lane hl => by have := hBound lane hl; simp only [row,steadyRoundSlotRow]; omega)
    (fun lane _ => steadyRoundRefreshFrame p l g batch round lane 0) gate
  obtain ⟨start',hStart'⟩ := first.advanceLocalWithPosition (pc' := 1401)
    (G := fun lane => [(7182,b32 (1 : Fin 2).val),(778,.pred (decide ((1 : Fin 2) = 0))),
      (1148,b32 (primingLaneRow (steadyRoundTile p l g batch round)
        (warpLane l g lane%l.block)))] ++
        steadyRoundTileFrame p l g batch round lane) (by
    intro lane hl
    obtain ⟨u,hu,hU⟩ := steadyRoundRouteLocal (lane := lane) 0 (first.checkpoint lane hl)
    exact ⟨u,hu,hU⟩)
  obtain ⟨gate',hGate'⟩ := steadyRoundSlotIndex hp hb 1 hBound start'
  let row' := fun lane => steadyRoundSlotRow p l g batch round lane 1
  obtain ⟨second,hSecond⟩ := recurringPageRefreshWarpOfMaximal hp hMax hFrame hg hw hb 1 1 row'
    (fun lane hl => by have := hBound lane hl; simp only [row',steadyRoundSlotRow]; omega)
    (fun lane _ => steadyRoundRefreshFrame p l g batch round lane 1) gate'
  obtain ⟨reached,hReached⟩ := second.advanceLocalWithPosition (pc' := 1427)
    (G := steadyRoundTileFrame p l g batch round) (by
    intro lane hl
    obtain ⟨u,hu,hU⟩ := steadyRoundRouteLocal (lane := lane) 1 (second.checkpoint lane hl)
    exact ⟨u,hu,hU.mono hU.2.2.2.2.2.2.2⟩)
  refine ⟨⟨c.shuffles,c.votes,c.ends,reached,c.rank,?_⟩⟩
  intro lane hl slot flag
  let t := warpLane l g lane
  let r := primingLaneRow (steadyRoundTile p l g batch round) (t%l.block)
  let begin := gate.pos lane
  let step := begin+primingScratchReads p batch r+2
  let stop := step+primingScratchReads p batch (r+64)+2
  have hRow0 : row lane = r := by simp [row,r,t,steadyRoundSlotRow]
  have hRow1 : row' lane = r+64 := rfl
  obtain ⟨hP0,hStore0,hWord0,_,hRead0⟩ := hFirst lane hl
  dsimp only at hP0 hStore0 hWord0 hRead0
  rw [hRow0] at hP0 hStore0 hWord0 hRead0
  have hStep : gate'.pos lane = step := by
    rw [congrFun hGate' lane,congrFun hStart' lane]
    exact hP0
  obtain ⟨hP1,hStore1,hWord1,_,hRead1⟩ := hSecond lane hl
  dsimp only at hP1 hStore1 hWord1 hRead1
  rw [hStep,hRow1] at hP1 hStore1 hWord1 hRead1
  have hStop : reached.pos lane = stop := (congrFun hReached lane).trans hP1
  have hWords0 : SteadyPageWords p l X t begin batch r 0 := ⟨hRead0,hStore0,hWord0⟩
  have hWords1 : SteadyPageWords p l X t step batch (r+64) 1 := ⟨hRead1,hStore1,hWord1⟩
  have hLast := steadyPageWordsLatestAtExit hWords0 hWords1 slot flag
  rw [hStop]
  fin_cases slot <;> cases flag
  · refine ⟨begin+primingScratchReads p batch r,by dsimp [step,stop]; omega,hStore0,?_⟩
    intro k hk j hj a hAccess hCover
    exact hLast k hk j hj a hAccess hCover
  · refine ⟨begin+primingScratchReads p batch r+1,by dsimp [step,stop]; omega,hWord0,?_⟩
    intro k hk j hj a hAccess hCover
    exact hLast k hk j hj a hAccess hCover
  · refine ⟨step+primingScratchReads p batch (r+64),by dsimp [stop]; omega,hStore1,?_⟩
    intro k hk j hj a hAccess hCover
    exact hLast k hk j hj a hAccess hCover
  · refine ⟨step+primingScratchReads p batch (r+64)+1,by dsimp [stop]; omega,hWord1,?_⟩
    intro k hk j hj a hAccess hCover
    exact hLast k hk j hj a hAccess hCover

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
