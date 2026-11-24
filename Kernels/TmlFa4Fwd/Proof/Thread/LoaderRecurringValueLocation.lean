-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmValueSite
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadySite
import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePacket
import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPacketSource
import Kernels.TmlFa4Fwd.Proof.LoaderPointerRow
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- The actual V copy's ring use identifies its logical paged row and input address. -/
structure RecurringValueVectorLocation (p : Params) (l : Launch) (X : Execution)
    (copy : EvId) (sp : AsyncCopy.Spec) (batch visit : Nat)
    (pair : Fin 16) (upper : Bool) : Prop where
  selected : tilePrefix p batch*p.heads ≤ copy.1/l.block ∧
    copy.1/l.block < tilePrefix p (batch+1)*p.heads
  use : recurringUseBefore X copy = 2*visit+1
  positive : 0 < visit
  bounded : visit < Mma.trips p batch (assignedCoordinates p batch (copy.1/l.block)).1
  address :
    let co := assignedCoordinates p batch (copy.1/l.block)
    let tile := Mma.trips p batch co.1-1-visit
    let key := kvCopyRow tile (copy.1%l.block) pair.val
    key < p.kLength batch ∧ sp.src.loc = p.vLayout.loc (p.page batch (key/16))
      (co.2/6) (key%16) (kvCopyColumn (copy.1%l.block) upper)

private theorem logicalRepeatedRowLive {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch tile visit lane : Nat} {pair : Fin 16}
    (hb : batch < p.batch) (hTile : 256*tile < p.qLength batch)
    (hVisit : 0 < visit) (hBound : visit < Mma.trips p batch tile) :
    kvCopyRow (Mma.trips p batch tile-1-visit) lane pair.val < p.kLength batch := by
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  have hLane := Nat.mod_lt (lane/8) (by decide : 0 < 8)
  have hPair := pair.isLt
  unfold kvCopyRow
  omega

private theorem pointerSenderTid {l : Launch} {g senderLane : Nat}
    (hg : g < l.threads) (hBlock : l.block%32 = 0) (hSender : senderLane < 32) :
    warpLane l g senderLane % l.block = 32*warpIndex l g+senderLane := by
  let sender := warpLane l g senderLane
  have hPeer := Step.sameWarp_lane hBlock hg hSender
  have hWarp := hPeer.1.2
  have hLane := hPeer.2
  change warpIndex l g = warpIndex l sender at hWarp
  change laneOf l sender = senderLane at hLane
  change sender % l.block = 32*warpIndex l g+senderLane
  unfold warpIndex at hWarp ⊢
  unfold laneOf at hLane
  omega

private theorem warpSelfLane (l : Launch) (g : Nat) :
    warpLane l g (laneOf l g) = g := by
  unfold warpLane laneOf
  have hLocal := Nat.mod_le g l.block
  have hLaneLe := Nat.mod_le (g%l.block) 32
  omega

set_option maxRecDepth 100000 in
/-- A warm V vector addresses the source row of its observed logical use. -/
theorem warmValueVectorLocationOfUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g j : Nat} {sp : AsyncCopy.Spec}
    (pair : Fin 16) (upper : Bool)
    (he : X.get (g,j) = some ⟨packetPlanePc (recurringPacketSite 1) pair upper,.copy sp⟩) :
    ∃ batch < p.batch, ∃ visit, RecurringValueVectorLocation p l X (g,j)
      sp batch visit pair upper := by
  have h : WarmValueSite X (g,j) sp := ⟨pair,upper,he⟩
  have hWarp := h.issuer hp hX
  have hActive := h.active hp hX hFrame
  let lane := laneOf l g
  let pc := packetPlanePc (recurringPacketSite 1) pair upper
  let e : Event := ⟨pc,.copy sp⟩
  have hSelf : warpLane l g lane = g := warpSelfLane l g
  have hg := event_thread_lt hX he
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hPc : 917 ≤ pc ∧ pc < 1348 := by fin_cases pair <;> cases upper <;> decide
  change 917 ≤ e.pc ∧ e.pc < 1348 at hPc
  have hRecord : X.get (warpLane l g lane,j) = some e := by rw [hSelf]; exact he
  obtain ⟨batch,hb,hLo,hHi,hProjection⟩ := actualWarmCacheProjection hp hX hg hWarp hLane
    (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hRecord hPc.1 (.inl (by omega))
    (fun _ hBad => by cases hBad)
  rcases hProjection with ⟨_,round,hRound,hUse,hRank⟩ | ⟨pos,hPos,hExit,_⟩
  · let co := assignedCoordinates p batch (g/l.block)
    let trips := Mma.trips p batch co.1
    let tile := trips-2-round
    change round < min (trips-1) 9 at hRound
    have hLive : round+1 < trips := by have := Nat.min_le_left (trips-1) 9; omega
    have hProjection := valueProjectionAtCopy false pair upper
    change cacheRoundRemaining false pc = 1 ∧
      loaderShuffleTail 1348 pc+(2*pair.val+2) = 32 at hProjection
    change _ + cacheRoundRemaining false pc = _ at hUse
    change _ + loaderShuffleTail 1348 pc = _ at hRank
    rw [hSelf,hProjection.1] at hUse
    have hCount : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch+64+64*round+32+2*pair.val+2 := by
      rw [hSelf] at hRank ⊢
      omega
    have hAddress := (warmValuePacketSource hp hX hFrame hg hWarp hLane hb hLo hHi hActive
      (iteration := round) pair upper hRecord hCount).1
    let senderLane := warmVShuffleSender lane pair
    let sender := warpLane l g senderLane
    have hSender : senderLane < 32 := by
      unfold senderLane warmVShuffleSender pointerBroadcastLane
      omega
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    have hSenderTid : sender%l.block = 32*warpIndex l g+senderLane :=
      pointerSenderTid hg hBlock hSender
    have hTid : g%l.block = 32*warpIndex l g+lane := by unfold warpIndex lane laneOf; omega
    have hHalf : (if pair.val < 8 then 0 else 64) = 64*(pair.val/8) := by fin_cases pair <;> decide
    have hRowEq :
        warmVInputRow tile (sender%l.block) pair = kvCopyRow tile (g%l.block) pair.val := by
      rw [warmVInputRow,hHalf,hSenderTid,hTid]
      simpa only [senderLane,warmVShuffleSender,Nat.add_assoc] using
        kvCopyRow_of_pointerLane tile (warpIndex l g) lane pair.val
    change sp.src.loc = p.vLayout.loc (primingScratchPage p batch
      (warmVInputRow tile (sender%l.block) pair)) (co.2/6)
      (warmVInputRow tile (sender%l.block) pair % 16)
      (kvCopyColumn (warpLane l g lane%l.block) upper) at hAddress
    rw [hRowEq,hSelf] at hAddress
    refine ⟨batch,hb,round+1,⟨hLo,hHi⟩,by omega,by omega,hLive,?_⟩
    have hRow := logicalRepeatedRowLive hp (pair := pair) (lane := g%l.block) hb
      (assignedCoordinates_valid hp hLo hHi).1 (show 0 < round+1 by omega) hLive
    have hTile : trips-1-(round+1) = tile := by unfold tile; omega
    change _ ∧ sp.src.loc = _
    rw [hTile] at hRow ⊢
    exact ⟨hRow,by simpa [primingScratchPage,hRow,co] using hAddress⟩
  · have hWarm := actualWarmCacheUseBound hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hRecord
      (.inl ⟨1,pair,upper,sp,rfl⟩) hPc
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
/-- A steady V vector addresses the source row of its observed logical use. -/
theorem steadyValueVectorLocationOfUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g j : Nat} {sp : AsyncCopy.Spec}
    (pair : Fin 16) (upper : Bool)
    (he : X.get (g,j) =
      some ⟨packetPlanePc (recurringPacketSite (steadySpillSite true)) pair upper,.copy sp⟩) :
    ∃ batch < p.batch, ∃ visit, RecurringValueVectorLocation p l X (g,j)
      sp batch visit pair upper := by
  let copy : EvId := (g,j)
  have hWarp := copyLoaderWarp hp hX (show X.Copy copy sp from ⟨_,he⟩)
  let lane := laneOf l g
  let pc := packetPlanePc (recurringPacketSite (steadySpillSite true)) pair upper
  let e : Event := ⟨pc,.copy sp⟩
  have hPc : 1396 ≤ pc ∧ pc < 1741 := by fin_cases pair <;> cases upper <;> decide
  have hActive := loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he
    (show 297 < pc by omega) (show pc < 1862 by omega)
  change 1396 ≤ e.pc ∧ e.pc < 1741 at hPc
  have hSelf : warpLane l g lane = g := warpSelfLane l g
  have hg := event_thread_lt hX he
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hRecord : X.get (warpLane l g lane,j) = some e := by rw [hSelf]; exact he
  obtain ⟨batch,hb,hLo,hHi,round,hMin,hRound,hUse,hRank⟩ :=
    actualSteadyCacheProjection hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hRecord hPc
      (fun _ hBad => by cases hBad)
  let co := assignedCoordinates p batch (g/l.block)
  let trips := Mma.trips p batch co.1
  let tile := trips-2-round
  change round < trips-1 at hRound
  have hLive : round+1 < trips := by omega
  have hMany : 11 ≤ trips := by omega
  have hProjection := valueProjectionAtCopy true pair upper
  change cacheRoundRemaining true pc = 1 ∧
    loaderShuffleTail 1741 pc+(2*pair.val+2) = 32 at hProjection
  change _ + cacheRoundRemaining true pc = _ at hUse
  change _ + loaderShuffleTail 1741 pc = _ at hRank
  rw [hSelf,hProjection.1] at hUse
  have hCount : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch+640+64*(round-9)+steadyOperandRank true+2*pair.val+2 := by
    rw [hSelf] at hRank ⊢
    change _ = primingSearchShuffleCount batch+640+64*(round-9)+32+2*pair.val+2
    omega
  have hAddress := (steadyPacketSource hp hX hFrame hg hWarp hLane hb hLo hHi hActive hMany
    hMin true pair upper hRecord hCount).1
  let senderLane := steadyPairSender lane pair
  let sender := warpLane l g senderLane
  have hSender : senderLane < 32 := by
    unfold senderLane steadyPairSender pointerBroadcastLane
    omega
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSenderTid : sender%l.block = 32*warpIndex l g+senderLane :=
    pointerSenderTid hg hBlock hSender
  have hTid : g%l.block = 32*warpIndex l g+lane := by unfold warpIndex lane laneOf; omega
  have hSlot : (steadyPairSlot pair).val = pair.val/8 := by fin_cases pair <;> rfl
  have hRowEq : steadyPairRow tile (sender%l.block) pair = kvCopyRow tile (g%l.block) pair.val := by
    rw [steadyPairRow,hSlot,hSenderTid,hTid]
    simpa only [senderLane,steadyPairSender,Nat.add_assoc]
      using kvCopyRow_of_pointerLane tile (warpIndex l g) lane pair.val
  change sp.src.loc = p.vLayout.loc (primingScratchPage p batch
      (steadyPairRow tile (sender%l.block) pair)) (co.2/6)
      (steadyPairRow tile (sender%l.block) pair % 16)
      (kvCopyColumn (warpLane l g lane%l.block) upper) at hAddress
  rw [hRowEq,hSelf] at hAddress
  refine ⟨batch,hb,round+1,⟨hLo,hHi⟩,by omega,by omega,hLive,?_⟩
  have hRow := logicalRepeatedRowLive hp (pair := pair) (lane := g%l.block) hb
    (assignedCoordinates_valid hp hLo hHi).1 (show 0 < round+1 by omega) hLive
  have hTile : trips-1-(round+1) = tile := by unfold tile; omega
  change _ ∧ sp.src.loc = _
  rw [hTile] at hRow ⊢
  exact ⟨hRow,by simpa [primingScratchPage,hRow,co] using hAddress⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
