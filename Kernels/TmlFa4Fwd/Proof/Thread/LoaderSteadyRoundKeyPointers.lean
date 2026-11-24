-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundPages
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPointerProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadySpillRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValueGate
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
import Kernels.TmlFa4Fwd.Flow.Code.Part022

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
open LocalAccessCode (DoesNotClobber)

set_option maxRecDepth 4096 in
/-- After the page loop, the actual address arithmetic reaches the K gate of steady round
`round`. -/
theorem SteadyRoundPages.keyGate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch round : Nat} (c : SteadyRoundPages p l X g batch round) :
    ∃ gate : RecurringCacheGate l X g 2 (cacheUseOfRound round)
        (steadyRoundTileFrame p l g batch round) c.shuffles c.votes c.ends,
      gate.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let use := cacheUseOfRound round
  let F := steadyRoundTileFrame p l g batch round lane
  have hs := c.reached.checkpoint lane hl
  have hF : Holds (c.reached.state lane).regs F := hs.2.2.2.2
  have hAt : At (c.reached.state lane) 1427
      (recurringBarrierInput l 2 (kvUseStage use) (cacheEmptyParity use)++F) :=
    hs.mono ((holds_append ..).mpr ⟨⟨hF.2.2.2.2.2.1,hF.2.2.2.2.1,hF.2.2.2.2.2.2.1,trivial⟩,hF⟩)
  obtain ⟨u,hu,hU⟩ := roundStraightFrameAll (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringBarrierPrep hp (g := t) 2 (kvUseStage use) (cacheEmptyParity use)) hAt
  exact ⟨u,run_rtg hu,hU⟩

/-- The K packet of steady round `round` passes its empty poll once the MMA has returned
the earlier generations of its slot. The metadata words of the page loop stay current. -/
theorem SteadyRoundPages.acquireKeyOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
    (c : SteadyRoundPages p l X g batch round) :
    ∃ done : RecurringCacheAcquired l X g 2 (cacheUseOfRound round)
        (steadyRoundTileFrame p l g batch round) c.shuffles c.votes c.ends,
      ∀ lane < 32, ∀ slot isRow,
        steadyRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  obtain ⟨gate,hPos⟩ := c.keyGate hp
  have hFresh : ∀ lane < 32, (recurringEmptyWait 2).result ∉
      (steadyRoundTileFrame p l g batch round lane).map Prod.fst :=
    fun _ _ => of_decide_eq_true rfl
  obtain ⟨done,hDone⟩ := gate.acquireOfReleases hp hMax hFrame hg hw hb hLo hHi 2 hFresh
    (by rw [c.rank]; unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega) hReleased
  refine ⟨done,fun lane hl slot isRow => ?_⟩
  obtain ⟨j,hGateBefore,hJ,_⟩ := (hDone lane hl).1
  have hCell := c.cells lane hl slot isRow
  rw [← congrFun hPos lane] at hCell
  exact PrimingCellValue.ofQuietSpan hCell (by omega) (hDone lane hl).2

/-- The registers of the K packet of steady round `round` after its acquire. -/
def steadyRoundKeyCarry (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  recurringBarrierFacts l 2 (kvUseStage (cacheUseOfRound round))
    (cacheEmptyParity (cacheUseOfRound round)) ++ steadyRoundTileFrame p l g batch round lane

/-- The K row pointer of a lane's scratch slot in steady round `round`. -/
def steadyRoundKeyPointer (p : Params) (l : Launch) (g batch round lane : Nat) (slot : Fin 2) :
    Nat :=
  primingKRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (steadyRoundSlotRow p l g batch round lane slot)

private theorem steadyRoundKeySaveFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (more : Bool) :
    RecurringSaveFrame 2 ((12,.pred more) :: steadyRoundKeyCarry p l g batch round lane) := by
  let F := (12,.pred more) :: steadyRoundKeyCarry p l g batch round lane
  have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7771 ∧ r ≠ 7773)) = true := rfl
  have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7771 ∧ pair.1 ≠ 7773 :=
    of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
  exact ⟨by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).1,
    by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).2,
    by set_option maxRecDepth 100000 in kernel_rfl⟩

set_option maxRecDepth 4096 in
private theorem steadyRoundKeySaveInput {p : Params} {l : Launch} {g batch round lane : Nat}
    {s : TState} (slot : Fin 2) (more : Bool)
    (hs : At s 1436 ([(9539,b64 slot.val),(12,.pred more)] ++
      steadyRoundKeyCarry p l g batch round lane)) :
    At s 1436 (recurringScratchSaveInput l 2 slot p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.kLayout.headStride)) ++
      ((12,.pred more) :: steadyRoundKeyCarry p l g batch round lane)) := by
  refine hs.mono ((holds_append ..).mpr ⟨?_,hs.2.2.2.2.2⟩)
  have hF := hs.2.2.2.2
  simp only [recurringScratchSaveInput,recurringScratchCarry,recurringSaveInputs,
    pointerReloadBase,pointerReloadAddress,List.cons_append,List.nil_append,Holds]
  refine ⟨holds_mem hF ?_,holds_mem hF ?_,holds_mem hF ?_,holds_mem hF ?_,holds_mem hF ?_,
    hF.1,holds_mem hF ?_,trivial⟩ <;>
    simp [steadyRoundKeyCarry,steadyRoundTileFrame,steadyRoundFrame,steadyCacheHeadFrame,
      steadyRoundCarry,warmRoundCarry,openingWarmFrame,warmStartFrame,primingVScratchAbi,
      warmPageRoots,warmLaneRoots]

set_option maxRecDepth 4096 in
private theorem steadyRoundKeyPointerSlotOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) (more : Bool)
    {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g 1436 (fun lane =>
      recurringScratchSaveInput l 2 slot p.kLayout.pageStride p.kLayout.rowStride
        (p.kLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.kLayout.headStride)) ++
        ((12,.pred more) :: steadyRoundKeyCarry p l g batch round lane))
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ isRow,
      steadyRoundMetadata p l X g batch round lane (start.pos lane) slot isRow) :
    ∃ done : SchedulerWarpReached l X g 1448
        (fun lane => (12,.pred more) :: steadyRoundKeyCarry p l g batch round lane)
        shuffles votes ends,
      ∀ lane < 32,
        let t := warpLane l g lane
        let dst := pointerSaveAccess l t 2 slot
        let bs := (b64 (steadyRoundKeyPointer p l g batch round lane slot)).toBytes
        PrimingCellValue X t (done.pos lane) 1447 dst bs ∧
        ∀ {saved : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (start.pos lane) saved cell data →
          DoesNotClobber cell ⟨1447,.wr dst bs⟩ →
          PrimingCellValue X t (done.pos lane) saved cell data := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let base := p.kLayout.base+2*(head*p.kLayout.headStride)
  let ps := p.kLayout.pageStride
  let rs := p.kLayout.rowStride
  let row := fun lane => steadyRoundSlotRow p l g batch round lane slot
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
  obtain ⟨done,_,hSaved⟩ := recurringPointerSaveWarpPreservingOfMaximal hp hMax hg hw 2 slot page
    (fun lane => row lane%16) (fun lane _ => hPageSigned lane)
    (fun _ _ => (Nat.mod_lt _ (by decide : 0 < 16)).trans (by decide))
    hPS hRS (fun lane _ => (hPayload lane).2)
    (fun lane _ => steadyRoundKeySaveFrame p l g batch round lane more) start
    (fun lane hl isRow => by
      cases isRow
      · exact hCells lane hl false
      · exact hCells lane hl true)
  refine ⟨done,fun lane hl => ?_⟩
  have h := hSaved lane hl
  dsimp only at h ⊢
  rw [(hPayload lane).1] at h
  exact h

/-- The steady page and row words lie apart from every saved pointer. -/
theorem steadyMetadataApartFromPointerSave (l : Launch) (t : Nat) (site : Fin 4)
    (slot slot' : Fin 2) (flag : Bool) (pc : Nat) (bs : List Byte) :
    DoesNotClobber (scratchReloadAccess l t (recurringScratchWord 2 flag) slot)
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
/-- From its K acquire, a loader warp of steady round `round` saves both K pointers in
their private slots and reaches the K packet. The page and row words stay current. -/
theorem steadyRoundKeyPointersOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1433 (steadyRoundKeyCarry p l g batch round)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ slot isRow,
      steadyRoundMetadata p l X g batch round lane (cur.pos lane) slot isRow) :
    ∃ done : SchedulerWarpReached l X g 1451
        (fun lane => [(9539,b64 1),(779,.pred false)] ++ steadyRoundKeyCarry p l g batch round lane)
        shuffles votes ends,
      ∀ lane < 32, (∀ slot : Fin 2,
        PrimingCellValue X (warpLane l g lane) (done.pos lane) 1447
          (pointerSaveAccess l (warpLane l g lane) 2 slot)
          (b64 (steadyRoundKeyPointer p l g batch round lane slot)).toBytes) ∧
        ∀ slot isRow, steadyRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  let KC := steadyRoundKeyCarry p l g batch round
  obtain ⟨start0,hStart0⟩ := cur.advanceLocalWithPosition (pc' := 1436)
    (G := fun lane => recurringScratchSaveInput l 2 0 p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.kLayout.headStride)) ++
      ((12,.pred true) :: KC lane)) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      have hSeed : Seg kernel [] l (warpLane l g lane) 3 1433 [] 1436
          [(9539,b64 (0 : Fin 2).val),(12,.pred true)] := by
        intro v hv
        seg_fp hv using rfl
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hSeed (hs.mono hs.2.2.2.2)
      exact ⟨u,run_rtg hu,steadyRoundKeySaveInput 0 true hU⟩)
  obtain ⟨saved0,hSaved0⟩ := steadyRoundKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 0 true
    start0 (fun lane hl isRow => by rw [hStart0]; exact hCells lane hl 0 isRow)
  obtain ⟨start1,hStart1⟩ := saved0.advanceLocalWithPosition (pc' := 1436)
    (G := fun lane => recurringScratchSaveInput l 2 1 p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.kLayout.headStride)) ++
      ((12,.pred false) :: KC lane)) (by
      intro lane hl
      have hs := saved0.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := steadySpillRoute (l := l) (g := warpLane l g lane) (F := KC lane)
        false true (fun operand => by
          cases operand <;> (set_option maxRecDepth 100000 in kernel_rfl)) hs
      obtain ⟨v,hv,hV⟩ := steadySpillSecond (l := l) (g := warpLane l g lane) (F := KC lane)
        false (fun operand => by
          cases operand <;> (set_option maxRecDepth 100000 in kernel_rfl)) hU
      exact ⟨v,run_rtg (run_comp hu hv),steadyRoundKeySaveInput 1 false hV⟩)
  obtain ⟨saved1,hSaved1⟩ := steadyRoundKeyPointerSlotOfMaximal hp hMax hg hw hb hLo hHi 1 false
    start1 (fun lane hl isRow => by
      rw [hStart1]
      exact (hSaved0 lane hl).2 (by rw [hStart0]; exact hCells lane hl 1 isRow)
        (steadyMetadataApartFromPointerSave l _ 2 1 0 isRow _ _))
  obtain ⟨done,hDone⟩ := saved1.advanceLocalWithPosition (pc' := 1451)
    (G := fun lane => [(9539,b64 1),(779,.pred false)] ++ KC lane) (by
      intro lane hl
      have hs := saved1.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := steadySpillRoute (l := l) (g := warpLane l g lane) (F := KC lane)
        false false (fun operand => by
          cases operand <;> (set_option maxRecDepth 100000 in kernel_rfl)) hs
      exact ⟨u,run_rtg hu,hU⟩)
  have hMid (lane : Nat) (hl : lane < 32) (slot : Fin 2) (flag : Bool) :
      steadyRoundMetadata p l X g batch round lane (start1.pos lane) slot flag := by
    rw [hStart1]
    exact (hSaved0 lane hl).2 (by rw [hStart0]; exact hCells lane hl slot flag)
      (steadyMetadataApartFromPointerSave l _ 2 slot 0 flag _ _)
  refine ⟨done,fun lane hl => ⟨fun slot => ?_,fun slot flag => ?_⟩⟩
  · rw [hDone]
    fin_cases slot
    · apply (hSaved1 lane hl).2
      · rw [hStart1]
        exact (hSaved0 lane hl).1
      · intro dst _ hKind
        cases hKind
        rintro ⟨loc,hLoc,hWrite⟩
        simp [pointerSaveAccess,pointerSaveAddress,pointerReloadAddress,Acc.Covers,Loc.InRange]
          at hLoc hWrite
        omega
    · exact (hSaved1 lane hl).1
  · rw [hDone]
    exact (hSaved1 lane hl).2 (hMid lane hl slot flag)
      (steadyMetadataApartFromPointerSave l _ 2 slot 1 flag _ _)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
