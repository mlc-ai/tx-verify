-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeySite
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadySite
import Kernels.TmlFa4Fwd.Proof.LoaderPointerRow
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- A recurring K vector's recorded use selects a logical paged row and column. -/
structure RecurringKeyVectorLocation (p : Params) (l : Launch) (X : Execution)
    (copy : EvId) (sp : AsyncCopy.Spec) (batch visit : Nat)
    (pair : Fin 16) (upper : Bool) : Prop where
  selected : tilePrefix p batch*p.heads ≤ copy.1/l.block ∧
    copy.1/l.block < tilePrefix p (batch+1)*p.heads
  use : recurringUseBefore X copy = 2*visit
  positive : 0 < visit
  bounded : visit < Mma.trips p batch (assignedCoordinates p batch (copy.1/l.block)).1
  address :
    let co := assignedCoordinates p batch (copy.1/l.block)
    let tile := Mma.trips p batch co.1-1-visit
    let key := kvCopyRow tile (copy.1%l.block) pair.val
    key < p.kLength batch ∧ sp.src.loc = p.kLayout.loc (p.page batch (key/16))
      (co.2/6) (key%16) (kvCopyColumn (copy.1%l.block) upper)

private theorem recurringKeyRowLive {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch tile visit lane : Nat} {pair : Fin 16}
    (hb : batch < p.batch) (hTile : 256*tile < p.qLength batch)
    (hVisit : 0 < visit) (hBound : visit < Mma.trips p batch tile) :
    kvCopyRow (Mma.trips p batch tile-1-visit) lane pair.val < p.kLength batch := by
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  have hLane := Nat.mod_lt (lane/8) (by decide : 0 < 8)
  have hPair := pair.isLt
  unfold kvCopyRow
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g j : Nat}
include hp hX hFrame

set_option maxRecDepth 100000 in
/-- Warm copies identify their exact K row from the same replay as the ring-use cursor. -/
theorem warmKeyVectorLocationOfUse {sp : AsyncCopy.Spec} (pair : Fin 16) (upper : Bool)
    (he : X.get (g,j) = some ⟨packetPlanePc (recurringPacketSite 0) pair upper,.copy sp⟩) :
    ∃ batch < p.batch, ∃ visit, RecurringKeyVectorLocation p l X (g,j)
      sp batch visit pair upper := by
  have h : WarmKeySite X (g,j) sp := ⟨pair,upper,he⟩
  have hWarp := h.issuer hp hX
  have hActive := h.active hp hX hFrame
  let lane := laneOf l g
  let pc := packetPlanePc (recurringPacketSite 0) pair upper
  let e : Event := ⟨pc,.copy sp⟩
  have hSelf : warpLane l g lane = g := by
    unfold warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g%l.block) 32
    omega
  have hg := event_thread_lt hX he
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hPc : 917 ≤ pc ∧ pc < 1348 := by fin_cases pair <;> cases upper <;> decide
  change 917 ≤ e.pc ∧ e.pc < 1348 at hPc
  have hRecord : X.get (warpLane l g lane,j) = some e := by rw [hSelf]; exact he
  obtain ⟨batch,hb,hLo,hHi,hProjection⟩ := actualWarmCacheProjection hp hX hg hWarp hLane
    (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hRecord hPc.1 (.inl (by omega))
    (fun _ hBad => by cases hBad)
  rcases hProjection with ⟨_,round,hRound,hUse,hRank⟩ | ⟨pos,hPos,hExit,hShfl⟩
  · have hProjection := keyProjectionAtCopy false pair upper
    change cacheRoundRemaining false pc = 2 ∧
      loaderShuffleTail 1348 pc+(2*pair.val+2) = 64 at hProjection
    change _ + cacheRoundRemaining false pc = _ at hUse
    change _ + loaderShuffleTail 1348 pc = _ at hRank
    rw [hSelf,hProjection.1] at hUse
    rw [hSelf] at hRank
    have hVector : WarmKeyVector p l X (g,j) batch round pair upper sp :=
      ⟨hLo,hHi,he,by
        change ((X.tr g).take j).countP Execution.isShfl =
          primingSearchShuffleCount batch+64+64*round+2*pair.val+2
        omega⟩
    change round < min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9
      at hRound
    have hLive : round+1 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 :=
      by have := Nat.min_le_left (Mma.trips p batch
          (assignedCoordinates p batch (g/l.block)).1-1) 9; omega
    have hSource := (hVector.source hp hX hFrame hb hWarp hActive).1
    refine ⟨batch,hb,round+1,⟨hLo,hHi⟩,by omega,by omega,hLive,?_⟩
    let co := assignedCoordinates p batch (g/l.block)
    have hRow := recurringKeyRowLive hp (pair := pair) (lane := g%l.block) hb
      (assignedCoordinates_valid hp hLo hHi).1 (show 0 < round+1 by omega) hLive
    have hTile : Mma.trips p batch co.1-1-(round+1) = Mma.trips p batch co.1-2-round := by omega
    change _ ∧ sp.src.loc = _
    rw [hTile] at hRow ⊢
    exact ⟨hRow,by simpa [primingScratchPage,hRow,co] using hSource⟩
  · have hWarm := actualWarmCacheUseBound hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hRecord
      (.inl ⟨0,pair,upper,sp,rfl⟩) hPc
    obtain ⟨b,hb',hLo',hHi',hLimit⟩ := hWarm
    obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hActive
    have hBatch := (hUnique b ⟨hb',hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst b
    have hOrd := countP_take_mono recurringPublicationMark (X.tr (warpLane l g lane)) hPos
    have hGrowth : recurringUseBefore X (warpLane l g lane,pos) ≤
        recurringUseBefore X (warpLane l g lane,j) := Nat.add_le_add_left hOrd _
    change recurringUseBefore X (warpLane l g lane,j) <
      2*(min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9+1) at hLimit
    change recurringUseBefore X (warpLane l g lane,pos) =
      2*(min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9+1) at hExit
    omega

set_option maxRecDepth 100000 in
/-- Steady copies identify their exact K row from the same replay as the ring-use cursor. -/
theorem steadyKeyVectorLocationOfUse {sp : AsyncCopy.Spec} (pair : Fin 16) (upper : Bool)
    (he : X.get (g,j) =
      some ⟨packetPlanePc (recurringPacketSite (steadySpillSite false)) pair upper,.copy sp⟩) :
    ∃ batch < p.batch, ∃ visit, RecurringKeyVectorLocation p l X (g,j)
      sp batch visit pair upper := by
  let copy : EvId := (g,j)
  have hWarp := copyLoaderWarp hp hX (show X.Copy copy sp from ⟨_,he⟩)
  let lane := laneOf l g
  let pc := packetPlanePc (recurringPacketSite (steadySpillSite false)) pair upper
  let e : Event := ⟨pc,.copy sp⟩
  have hPc : 1396 ≤ pc ∧ pc < 1741 := by fin_cases pair <;> cases upper <;> decide
  have hActive := loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he
    (show 297 < pc by omega) (show pc < 1862 by omega)
  change 1396 ≤ e.pc ∧ e.pc < 1741 at hPc
  have hSelf : warpLane l g lane = g := by
    unfold warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g%l.block) 32
    omega
  have hg := event_thread_lt hX he
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hRecord : X.get (warpLane l g lane,j) = some e := by rw [hSelf]; exact he
  obtain ⟨batch,hb,hLo,hHi,round,hMin,hRound,hUse,hShfl⟩ :=
    actualSteadyCacheProjection hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hRecord hPc
      (fun _ hBad => by cases hBad)
  let co := assignedCoordinates p batch (g/l.block)
  change round < Mma.trips p batch co.1-1 at hRound
  have hLive : round+1 < Mma.trips p batch co.1 := by omega
  have hMany : 11 ≤ Mma.trips p batch co.1 := by omega
  have hProjection := keyProjectionAtCopy true pair upper
  change cacheRoundRemaining true pc = 2 ∧
    loaderShuffleTail 1741 pc+(2*pair.val+2) = 64 at hProjection
  change _ + cacheRoundRemaining true pc = _ at hUse
  change _ + loaderShuffleTail 1741 pc = _ at hShfl
  rw [hSelf,hProjection.1] at hUse
  rw [hSelf] at hShfl
  have hCount : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch+640+64*(round-9)+steadyOperandRank false+2*pair.val+2 := by
    rw [hSelf]
    change _ = primingSearchShuffleCount batch+640+64*(round-9)+0+2*pair.val+2
    omega
  have hSource := (steadyPacketSource hp hX hFrame hg hWarp hLane hb hLo hHi hActive hMany
    hMin false pair upper (by rw [hSelf]; exact he) hCount).1
  let tile := Mma.trips p batch co.1-2-round
  let senderLane := steadyPairSender lane pair
  let sender := warpLane l g senderLane
  have hSender : senderLane < 32 := by
    unfold senderLane steadyPairSender pointerBroadcastLane
    omega
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hPeer := Step.sameWarp_lane hBlock hg hSender
  have hSenderTid : sender%l.block = 32*warpIndex l g+senderLane := by
    have hWarpEq := hPeer.1.2
    have hLaneEq := hPeer.2
    change warpIndex l g = warpIndex l sender at hWarpEq
    change laneOf l sender = senderLane at hLaneEq
    unfold warpIndex at hWarpEq ⊢
    unfold laneOf at hLaneEq
    omega
  have hTid : g%l.block = 32*warpIndex l g+lane := by unfold warpIndex lane laneOf; omega
  have hSlot : (steadyPairSlot pair).val = pair.val/8 := by fin_cases pair <;> rfl
  have hRowEq : steadyPairRow tile (sender%l.block) pair = kvCopyRow tile (g%l.block) pair.val := by
    rw [steadyPairRow,hSlot,hSenderTid,hTid]
    simpa only [senderLane,steadyPairSender,Nat.add_assoc]
      using kvCopyRow_of_pointerLane tile (warpIndex l g) lane pair.val
  change sp.src.loc = p.kLayout.loc (primingScratchPage p batch
      (steadyPairRow tile (sender%l.block) pair)) (co.2/6)
      (steadyPairRow tile (sender%l.block) pair % 16)
      (kvCopyColumn (warpLane l g lane%l.block) upper) at hSource
  rw [hRowEq,hSelf] at hSource
  refine ⟨batch,hb,round+1,⟨hLo,hHi⟩,by omega,by omega,hLive,?_⟩
  have hRow := recurringKeyRowLive hp (pair := pair) (lane := g%l.block) hb
    (assignedCoordinates_valid hp hLo hHi).1 (show 0 < round+1 by omega) hLive
  have hTile : Mma.trips p batch co.1-1-(round+1) = tile := by unfold tile; omega
  change _ ∧ sp.src.loc = _
  rw [hTile] at hRow ⊢
  exact ⟨hRow,by simpa [primingScratchPage,hRow,co] using hSource⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
