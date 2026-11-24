-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundKeyPublication
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
open LocalAccessCode (DoesNotClobber)

/-- The steady K-to-V transition words name the ring position that follows the K use. -/
theorem steadyVTransitionWordsOfUse (use : Nat) :
    recurringVTransitionFacts 1 (kvUseStage use) (kvEmptyPhase use) =
      [(1170,b32 (kvUseStage (use+1)).val),(2141,loaderPhaseWord (kvEmptyPhase (use+1)))] := by
  have h := loaderRingWordsOfUse use
  exact congrArg (fun words : List (Nat × Value) =>
    [(1170,(words[0]?.map Prod.snd).getD (b32 0)),
     (2141,(words[1]?.map Prod.snd).getD (b32 0))]) h

/-- The registers of a steady round before its V gate: the stage and parity of the V use
and the K carry. -/
def steadyRoundValueCarry (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  let use := cacheUseOfRound round+1
  [(1170,b32 (kvUseStage use).val),(2141,loaderPhaseWord (kvEmptyPhase use))] ++
    steadyRoundKeyDone p l g batch round lane

/-- The registers of a steady round after its V acquire. -/
def steadyRoundValueAcquired (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  recurringBarrierFacts l 3 (kvUseStage (cacheUseOfRound round+1))
    (cacheEmptyParity (cacheUseOfRound round+1)) ++ steadyRoundValueCarry p l g batch round lane

/-- The round frame is part of the K carry. -/
theorem steadyRoundFrame_mem_keyDone {p : Params} {l : Launch} {g batch round lane : Nat}
    {x : Nat × Value} (hx : x ∈ steadyRoundFrame p l g batch round lane) :
    x ∈ steadyRoundKeyDone p l g batch round lane :=
  List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ hx))))

set_option maxRecDepth 4096 in
/-- After its K publication, a loader warp of steady round `round` reaches the V gate with
the stage and parity of the use after the K use. -/
theorem SteadyRoundKeyPublished.valueGate {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch round : Nat}
    (c : SteadyRoundKeyPublished p l X g batch round) :
    ∃ gate : RecurringCacheGate l X g 3 (cacheUseOfRound round+1)
        (steadyRoundValueCarry p l g batch round) c.shuffles c.votes c.ends,
      gate.pos = c.reached.pos := by
  apply c.reached.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let use := cacheUseOfRound round
  let F := steadyRoundKeyDone p l g batch round lane
  have hs := c.reached.checkpoint lane hl
  have hF : Holds (c.reached.state lane).regs F := hs.2.2.2.2
  have hAt : At (c.reached.state lane) 1603
      ([(7179,b32 (kvUseStage use).val),(7180,loaderPhaseWord (kvEmptyPhase use))] ++ F) := by
    refine hs.mono ⟨holds_mem hF ?_,holds_mem hF ?_,hF⟩ <;>
      exact steadyRoundFrame_mem_keyDone (by simp [steadyRoundFrame,steadyCacheHeadFrame,
        drainCarry,use])
  obtain ⟨u,hu,hU⟩ := roundStraightFrameAll (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringVTransitionRun (l := l) (g := t) 1 (kvUseStage use) (kvEmptyPhase use)) hAt
  have hWords : Holds u.regs
      [(1170,b32 (kvUseStage (use+1)).val),(2141,loaderPhaseWord (kvEmptyPhase (use+1)))] := by
    have h : Holds u.regs (recurringVTransitionFacts 1 (kvUseStage use) (kvEmptyPhase use)) :=
      ((holds_append ..).mp hU.2.2.2.2).1
    rwa [steadyVTransitionWordsOfUse] at h
  have hRest : Holds u.regs F := ((holds_append ..).mp hU.2.2.2.2).2
  have hV : At u 1608 (recurringBarrierInput l 3 (kvUseStage (use+1)) (cacheEmptyParity (use+1)) ++
      steadyRoundValueCarry p l g batch round lane) := by
    refine hU.mono ((holds_append ..).mpr ⟨⟨hWords.1,holds_mem hRest ?_,hWords.2.1,trivial⟩,
      hWords.1,hWords.2.1,hRest⟩)
    exact steadyRoundFrame_mem_keyDone (by simp [steadyRoundFrame,steadyCacheHeadFrame,drainCarry])
  obtain ⟨v,hv,hV'⟩ := roundStraightFrameAll (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringBarrierPrep hp (g := t) 3 (kvUseStage (use+1)) (cacheEmptyParity (use+1))) hV
  exact ⟨v,run_rtg (run_comp hu hv),hV'⟩

/-- A steady V packet passes its empty poll once the MMA has delivered the earlier
generations of the V slot. The metadata words of the page loop stay current. -/
theorem SteadyRoundKeyPublished.valueAcquireOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)))
    (c : SteadyRoundKeyPublished p l X g batch round) :
    ∃ done : SchedulerWarpReached l X g 1614 (steadyRoundValueAcquired p l g batch round)
        c.shuffles c.votes c.ends,
      ∀ lane < 32, ∀ slot isRow,
        steadyRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  obtain ⟨gate,hPos⟩ := c.valueGate hp
  have hFresh : ∀ lane < 32, (recurringEmptyWait 3).result ∉
      (steadyRoundValueCarry p l g batch round lane).map Prod.fst :=
    fun _ _ => of_decide_eq_true rfl
  obtain ⟨done,hDone⟩ := gate.acquireOfReleases hp hMax hFrame hg hw hb hLo hHi 3 hFresh
    (by rw [c.rank]; unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega) hReleased
  refine ⟨done,fun lane hl slot isRow => ?_⟩
  obtain ⟨j,hGateBefore,hJ,_⟩ := (hDone lane hl).1
  have hCell := c.metadata lane hl slot isRow
  rw [← congrFun hPos lane] at hCell
  exact PrimingCellValue.ofQuietSpan hCell (by omega) (hDone lane hl).2

/-- The V row pointer of a lane's scratch slot in steady round `round`. -/
def steadyRoundValuePointer (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) : Nat :=
  primingVRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (steadyRoundSlotRow p l g batch round lane slot)

private theorem steadyRoundValueSaveFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (more : Bool) :
    RecurringSaveFrame 3 ((13,.pred more) :: steadyRoundValueAcquired p l g batch round lane) := by
  let F := (13,.pred more) :: steadyRoundValueAcquired p l g batch round lane
  have hFresh : (F.map Prod.fst).all (fun r => decide (r ≠ 7815 ∧ r ≠ 7817)) = true := rfl
  have hf (pair : Nat × Value) (hm : pair ∈ F) : pair.1 ≠ 7815 ∧ pair.1 ≠ 7817 :=
    of_decide_eq_true (List.all_eq_true.mp hFresh _ (List.mem_map_of_mem hm))
  exact ⟨by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).1,
    by set_option maxRecDepth 100000 in kernel_rfl,fun pair hm => (hf pair hm).2,
    by set_option maxRecDepth 100000 in kernel_rfl⟩

set_option maxRecDepth 4096 in
private theorem steadyRoundValueSaveInput {p : Params} {l : Launch} {g batch round lane : Nat}
    {s : TState} (slot : Fin 2) (more : Bool)
    (hs : At s 1617 ([(9540,b64 slot.val),(13,.pred more)] ++
      steadyRoundValueAcquired p l g batch round lane)) :
    At s 1617 (recurringScratchSaveInput l 3 slot p.vLayout.pageStride p.vLayout.rowStride
      (p.vLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.vLayout.headStride)) ++
      ((13,.pred more) :: steadyRoundValueAcquired p l g batch round lane)) := by
  refine hs.mono ((holds_append ..).mpr ⟨?_,hs.2.2.2.2.2⟩)
  have hF := hs.2.2.2.2
  have hVA : Holds s.regs (steadyRoundValueAcquired p l g batch round lane) := hF.2.2
  have hVC : Holds s.regs (steadyRoundValueCarry p l g batch round lane) :=
    ((holds_append ..).mp hVA).2
  have hK : Holds s.regs (steadyRoundKeyDone p l g batch round lane) := hVC.2.2
  simp only [recurringScratchSaveInput,recurringScratchCarry,recurringSaveInputs,
    pointerReloadBase,pointerReloadAddress,List.cons_append,List.nil_append,Holds]
  refine ⟨holds_mem hK ?_,holds_mem hK ?_,holds_mem hK ?_,holds_mem hK ?_,holds_mem hK ?_,
    hF.1,holds_mem hK ?_,trivial⟩ <;>
    exact steadyRoundFrame_mem_keyDone (by
      simp [steadyRoundFrame,steadyCacheHeadFrame,steadyRoundCarry,warmRoundCarry,
        openingWarmFrame,warmStartFrame,primingVScratchAbi,warmPageRoots,warmLaneRoots])

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch round shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
include hp hMax hg hw hb

set_option maxRecDepth 4096 in
private theorem steadyRoundValuePointerSlotOfMaximal (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) (more : Bool)
    {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g 1617 (fun lane =>
      recurringScratchSaveInput l 3 slot p.vLayout.pageStride p.vLayout.rowStride
        (p.vLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.vLayout.headStride)) ++
        ((13,.pred more) :: steadyRoundValueAcquired p l g batch round lane))
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ isRow,
      steadyRoundMetadata p l X g batch round lane (start.pos lane) slot isRow) :
    ∃ done : SchedulerWarpReached l X g 1629
        (fun lane => (13,.pred more) :: steadyRoundValueAcquired p l g batch round lane)
        shuffles votes ends,
      ∀ lane < 32,
        let t := warpLane l g lane
        let dst := pointerSaveAccess l t 3 slot
        let bs := (b64 (steadyRoundValuePointer p l g batch round lane slot)).toBytes
        PrimingCellValue X t (done.pos lane) 1628 dst bs ∧
        ∀ {saved : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (start.pos lane) saved cell data →
          DoesNotClobber cell ⟨1628,.wr dst bs⟩ →
          PrimingCellValue X t (done.pos lane) saved cell data := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let base := p.vLayout.base+2*(head*p.vLayout.headStride)
  let ps := p.vLayout.pageStride
  let rs := p.vLayout.rowStride
  let row := fun lane => steadyRoundSlotRow p l g batch round lane slot
  let page := fun lane => primingScratchPage p batch (row lane)
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hPS : ps < 2 ^ 64 := (hp.objectBytes 2 40 8 ps (by simp [ps,Params.objectWords])).1
  have hRS : rs < 2 ^ 64 := (hp.objectBytes 2 24 8 rs (by simp [rs,Params.objectWords])).1
  have hPageSigned (lane : Nat) : page lane < 2 ^ 31 := by
    dsimp [page,primingScratchPage]
    split
    · rename_i h
      exact ((hp.pageTable batch hb).2 (row lane/16) (by omega)).2
    · decide
  have hPayload (lane : Nat) :
      sourceScratchPayload (page lane) (row lane%16) ps rs base =
        primingVRowPointer p batch head (row lane) ∧
      sourceScratchPayload (page lane) (row lane%16) ps rs base < 2^64 := by
    have h := sourceScratchPayload_live hp 1 (primingScratchPageBound hp (row := row lane) hb)
      (Nat.mod_lt (row lane) (by decide)) hh
    exact ⟨h.1,h.2.1⟩
  obtain ⟨done,_,hSaved⟩ := recurringPointerSaveWarpPreservingOfMaximal hp hMax hg hw 3 slot page
    (fun lane => row lane%16) (fun lane _ => hPageSigned lane)
    (fun _ _ => (Nat.mod_lt _ (by decide : 0 < 16)).trans (by decide))
    hPS hRS (fun lane _ => (hPayload lane).2)
    (fun lane _ => steadyRoundValueSaveFrame p l g batch round lane more) start
    (fun lane hl isRow => by
      cases isRow
      · exact hCells lane hl false
      · exact hCells lane hl true)
  refine ⟨done,fun lane hl => ?_⟩
  have h := hSaved lane hl
  dsimp only at h ⊢
  rw [(hPayload lane).1] at h
  exact h

set_option maxRecDepth 4096 in
/-- From its V acquire, a loader warp of steady round `round` saves both V pointers in their
private slots and reaches the V packet. The page and row words of the scratch slots supply
the pointers. -/
theorem steadyRoundValuePointersOfMaximal (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1614 (steadyRoundValueAcquired p l g batch round)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ slot isRow,
      steadyRoundMetadata p l X g batch round lane (cur.pos lane) slot isRow) :
    ∃ done : SchedulerWarpReached l X g 1632
        (fun lane => [(9540,b64 1),(780,.pred false)] ++
          steadyRoundValueAcquired p l g batch round lane)
        shuffles votes ends,
      ∀ lane < 32, ∀ slot : Fin 2,
        PrimingCellValue X (warpLane l g lane) (done.pos lane) 1628
          (pointerSaveAccess l (warpLane l g lane) 3 slot)
          (b64 (steadyRoundValuePointer p l g batch round lane slot)).toBytes := by
  let VA := steadyRoundValueAcquired p l g batch round
  obtain ⟨start0,hStart0⟩ := cur.advanceLocalWithPosition (pc' := 1617)
    (G := fun lane => recurringScratchSaveInput l 3 0 p.vLayout.pageStride p.vLayout.rowStride
      (p.vLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.vLayout.headStride)) ++
      ((13,.pred true) :: VA lane)) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      have hSeed : Seg kernel [] l (warpLane l g lane) 3 1614 [] 1617
          [(9540,b64 (0 : Fin 2).val),(13,.pred true)] := by
        intro v hv
        seg_fp hv using rfl
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hSeed (hs.mono hs.2.2.2.2)
      exact ⟨u,run_rtg hu,steadyRoundValueSaveInput 0 true hU⟩)
  obtain ⟨saved0,hSaved0⟩ := steadyRoundValuePointerSlotOfMaximal hp hMax hg hw hb hLo hHi 0 true
    start0 (fun lane hl isRow => by rw [hStart0]; exact hCells lane hl 0 isRow)
  obtain ⟨start1,hStart1⟩ := saved0.advanceLocalWithPosition (pc' := 1617)
    (G := fun lane => recurringScratchSaveInput l 3 1 p.vLayout.pageStride p.vLayout.rowStride
      (p.vLayout.base+2*((assignedCoordinates p batch (g/l.block)).2/6*p.vLayout.headStride)) ++
      ((13,.pred false) :: VA lane)) (by
      intro lane hl
      have hs := saved0.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := steadySpillRoute (l := l) (g := warpLane l g lane) (F := VA lane)
        true true (fun operand => by
          cases operand <;> (set_option maxRecDepth 100000 in kernel_rfl)) hs
      obtain ⟨v,hv,hV⟩ := steadySpillSecond (l := l) (g := warpLane l g lane) (F := VA lane)
        true (fun operand => by
          cases operand <;> (set_option maxRecDepth 100000 in kernel_rfl)) hU
      exact ⟨v,run_rtg (run_comp hu hv),steadyRoundValueSaveInput 1 false hV⟩)
  obtain ⟨saved1,hSaved1⟩ := steadyRoundValuePointerSlotOfMaximal hp hMax hg hw hb hLo hHi 1 false
    start1 (fun lane hl isRow => by
      rw [hStart1]
      exact (hSaved0 lane hl).2 (by rw [hStart0]; exact hCells lane hl 1 isRow)
        (steadyMetadataApartFromPointerSave l _ 3 1 0 isRow _ _))
  obtain ⟨done,hDone⟩ := saved1.advanceLocalWithPosition (pc' := 1632)
    (G := fun lane => [(9540,b64 1),(780,.pred false)] ++ VA lane) (by
      intro lane hl
      have hs := saved1.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := steadySpillRoute (l := l) (g := warpLane l g lane) (F := VA lane)
        true false (fun operand => by
          cases operand <;> (set_option maxRecDepth 100000 in kernel_rfl)) hs
      exact ⟨u,run_rtg hu,hU⟩)
  refine ⟨done,fun lane hl slot => ?_⟩
  rw [hDone]
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

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
