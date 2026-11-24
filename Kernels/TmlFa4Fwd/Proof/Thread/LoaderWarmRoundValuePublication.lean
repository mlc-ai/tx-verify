-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValuePacket
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValuePacket
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondValueReload
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Flow.Code.Part020

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

theorem vStageWord (use : Nat) :
    b32 (((kvUseStage use).val+1)%3) = b32 (kvUseStage (use+1)).val := by
  congr 1
  rw [kvUseStage_val,kvUseStage_val]
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch round shuffles votes : Nat}
    {bias : Value} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
include hp hMax hg hw hb

set_option maxRecDepth 4096 in
/-- All sixteen V pairs of warm round `round` issue their vectors; the warp reaches the V
commit with the carry of the round. -/
theorem warmRoundVVectorsOfMaximal (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1209 (warmRoundVAcquired p l g batch round bias)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ slot isRow,
      warmRoundMetadata p l X g batch round lane (cur.pos lane) slot isRow) :
    Nonempty (SchedulerWarpReached l X g 1341
      (warmRoundVHalfFrame p l g batch round bias 1) (shuffles+32) votes ends) := by
  obtain ⟨r⟩ := warmRoundVPointersOfMaximal hp hMax hg hw hb hLo hHi cur hCells
  obtain ⟨first,hFirst⟩ := r.firstPairsOfMaximal hp hMax hg hb hLo hHi
  obtain ⟨low,hLow⟩ := first.advanceLocalWithPosition (pc' := warmValueNextPc 2)
    (G := warmRoundVHalfFrame p l g batch round bias 0)
    (fun lane hl => ⟨first.state lane,.refl,first.checkpoint lane hl⟩)
  obtain ⟨lowDone,hLowDone⟩ := warmRoundVHalfOfMaximal hp hMax hg hb hLo hHi (first := 2) 0
    (by decide) low 6 (by decide)
  have hh : (assignedCoordinates p batch (g/l.block)).2/6 < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hPtr (lane : Nat) (slot : Fin 2) :
      warmRoundValuePointer p l g batch round lane slot < 2^64 := by
    let row := warmRoundSlotRow p l g batch round lane slot
    obtain ⟨hEq,hLt,_⟩ := sourceScratchPayload_live hp 1
      (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide)) hh
    rw [hEq] at hLt
    simpa [warmRoundValuePointer,primingVRowPointer] using hLt
  have hAddr : l.localBase+warmVSecondReload.offset < 2^64 := by
    have h := hp.localMemory.2.1
    change l.localBase+8 < 2^64
    omega
  have hAlign : (l.localBase+warmVSecondReload.offset)%8 = 0 := by
    have h := hp.localMemory.1
    change (l.localBase+8)%8 = 0
    omega
  obtain ⟨reload,_,_⟩ := warmVSecondReload.warpReadPreservingOfMaximal hp hMax hg
    (by decide) Flow.code_1292 hAddr hAlign (by decide)
    (fun lane => warmRoundValuePointer p l g batch round lane 1) (fun lane _ => hPtr lane 1)
    lowDone
    (fun lane _ => by
      simp [warmVSecondReload,warmRoundVHalfFrame,warmRoundVPairFrame,warmRoundVRest,
        warmRoundVAcquired,warmRoundVCarry,openingWarmFrame,warmStartFrame,primingVScratchAbi])
    (fun lane _ fact hm => by
      have h : ((warmRoundVHalfFrame p l g batch round bias 0 lane).map Prod.fst).all
          (fun r => decide (r ≠ 2098 ∧ r ≠ 2099)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    (fun lane hl => hLowDone lane hl (by rw [hLow]; exact hFirst lane hl))
  obtain ⟨high,_⟩ := reload.advanceLocalWithPosition (pc' := warmVShufflePc 8)
    (G := warmRoundVHalfFrame p l g batch round bias 1) (by
      intro lane hl
      have hs := reload.checkpoint lane hl
      have k := hs.2.2.2.2
      exact ⟨reload.state lane,.refl,hs.mono ⟨k.1,k.2.1,k.2.2.2.2⟩⟩)
  obtain ⟨eight,_⟩ := warmRoundVLaterPairOfMaximal hp hMax hg hb hLo hHi 1 8 (by decide)
    ⟨by decide,by decide⟩ high
  obtain ⟨upper,_⟩ := eight.advanceLocalWithPosition (pc' := warmValueNextPc 9)
    (G := warmRoundVHalfFrame p l g batch round bias 1)
    (fun lane hl => ⟨eight.state lane,.refl,eight.checkpoint lane hl⟩)
  obtain ⟨done,_⟩ := warmRoundVHalfOfMaximal hp hMax hg hb hLo hHi (first := 9) 1
    (by decide) upper 7 (by decide)
  exact ⟨done⟩

omit hp hMax hg hw hb in
private theorem tailFrameOfHalf {R : Nat → Option Value} {p : Params} {l : Launch}
    {g batch round lane : Nat} {bias : Value}
    (hBias : bias = loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1)))
    (h : Holds R (warmRoundVHalfFrame p l g batch round bias 1 lane)) :
    Holds R (warmRoundTailFrame p l g batch round lane) := by
  subst hBias
  have hX := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hY := ((holds_append _ (recurringBarrierFacts l 0 (kvUseStage (cacheUseOfRound round))
    (cacheEmptyParity (cacheUseOfRound round)) ++ (1119,b32 (8*(warpLane l g lane%l.block%8))) ::
      ([(7174,b32 round),(7178,loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1))),
        (7179,b32 (kvUseStage (cacheUseOfRound round)).val),
        (7180,loaderPhaseWord (kvEmptyPhase (cacheUseOfRound round))),
        (1117,b32 (vPrimingResidual p batch (assignedCoordinates p batch (g/l.block)).1/2^31)),
        (1116,b32 (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-2)),
        (7,.pred (decide (10 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) &&
          warmResidueFlag (vPrimingResidual p batch (assignedCoordinates p batch (g/l.block)).1)))]
              ++
        [(164,.pred (warmResidueFlag (vPrimingResidual p batch
          (assignedCoordinates p batch (g/l.block)).1))),
          (7177,loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1)))] ++
        openingWarmFrame p l g batch lane ++ drainSchedulerFrame p l (warpLane l g lane)))
    (keySizes 16)).mp hX).1
  have hL := hY.2.2.2.2
  have hOD := hL.2.2.2.2.2.2.2.2.2
  refine ⟨?_,?_,holds_lookup h rfl,holds_mem hOD ?_,holds_lookup h rfl,holds_lookup h rfl,
    holds_lookup h rfl,holds_lookup h rfl,holds_lookup h rfl,holds_lookup h rfl,hOD⟩
  · rw [← vStageWord]
    exact holds_lookup h rfl
  · exact holds_lookup h rfl
  · simp [openingWarmFrame,warmStartFrame]

set_option maxRecDepth 4096 in
/-- From its V acquire, a loader warp of warm round `round` issues the V packet, commits it and
publishes its ready arrival. The Bias phases carried through V must be those of the next round:
warp 15 keeps them unchanged and warp 14 toggles them in its Bias block. -/
theorem warmRoundValuePublishedOfMaximal (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hBias : bias = loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1)))
    (hRank : shuffles = primingSearchShuffleCount batch+96+64*round) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1209 (warmRoundVAcquired p l g batch round bias)
      shuffles votes ends)
    (hCells : ∀ lane < 32, ∀ slot isRow,
      warmRoundMetadata p l X g batch round lane (cur.pos lane) slot isRow) :
    Nonempty (WarmRoundValuePublished p l X g batch round) := by
  classical
  obtain ⟨vec⟩ := warmRoundVVectorsOfMaximal hp hMax hg hw hb hLo hHi cur hCells
  let use := cacheUseOfRound round+1
  let threads := warpLane l g
  let addr := l.sharedBase+8*(kvUseStage use).val
  let stop := fun lane => vec.pos lane+2
  let ev : Nat → Event := fun lane =>
    ⟨reuseArrival 1,.asyncArrive (readyObject l (threads lane) (kvUseStage use)) true⟩
  let es : Nat → List Event := fun lane => [⟨1341,.asyncCommit⟩,ev lane]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hStage := (kvUseStage use).isLt
  have hWidth : addr+(copyArrivalAddress (recurringPacketSite 1)).2 < 2^32 := by
    have h := hp.shared.2.1
    change l.sharedBase+8*(kvUseStage use).val+32 < 2^32
    omega
  have hAlign : addr%8 = 0 := by
    have h := hp.shared.1
    dsimp [addr]
    omega
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (threads lane)).drop (vec.pos lane) =
        es lane ++ (X.tr (threads lane)).drop (stop lane) ∧
      At u 1343 (warmRoundTailFrame p l g batch round lane) ∧
      Run kernel Assumptions.all l (threads lane) {} ((X.tr (threads lane)).take (stop lane))
        (some u) ∧
      Run kernel Assumptions.all l (threads lane) u ((X.tr (threads lane)).drop (stop lane))
        (ends lane) ∧
      stop lane ≤ (X.tr (threads lane)).length ∧
      (stop lane = (X.tr (threads lane)).length → Step.Released l X (threads lane)) ∧
      X.get (threads lane,vec.pos lane+1) = some (ev lane) := by
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := vec.checkpoint lane hl
    have hAt : At (vec.state lane) (copyCommitPc (recurringPacketSite 1))
        [((copyArrivalAddress (recurringPacketSite 1)).1,b32 addr)] :=
      hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,trivial⟩
    obtain ⟨hc,ha,hPast,hTail⟩ := copyCommitAndArriveOfMaximal hMax
      (g := threads lane) hActor (recurringPacketSite 1) hAt hWidth hAlign
      (vec.localSteps lane hl) (vec.recorded lane hl) (vec.continuation lane hl)
      (vec.positive lane hl) (vec.bounded lane hl) (vec.released lane hl)
    have hLoc : (⟨.shared,threads lane/l.block,addr+32⟩ : Loc) =
        readyObject l (threads lane) (kvUseStage use) := by
      change _ = initObject l (threads lane/l.block) (readySlot (kvUseStage use))
      rw [readySlot_address]
    change X.get (threads lane,vec.pos lane+1) =
      some ⟨1342,.asyncArrive ⟨.shared,threads lane/l.block,addr+32⟩ true⟩ at ha
    rw [hLoc] at ha
    have hStop : stop lane = vec.pos lane+1+1 := rfl
    have hFrame : At (next (next (vec.state lane))) 1343
        (warmRoundTailFrame p l g batch round lane) :=
      hs.next.next.mono (tailFrameOfHalf hBias hs.2.2.2.2)
    refine ⟨_,?_,hFrame,hPast,hTail,?_,?_,ha⟩
    · change (X.tr (threads lane))[vec.pos lane]? = some ⟨1341,.asyncCommit⟩ at hc
      change (X.tr (threads lane))[vec.pos lane+1]? = some (ev lane) at ha
      have hlo := List.getElem?_eq_some_iff.mp hc
      have hhi := List.getElem?_eq_some_iff.mp ha
      rw [List.drop_eq_getElem_cons hlo.1,hlo.2,List.drop_eq_getElem_cons hhi.1,hhi.2,hStop]
      rfl
    · rw [hStop]
      exact len_of_get ha
    · rw [hStop]
      exact releasedIfLast ha (by intro h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hArrive using hLane
  have hOrd := vec.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨shuffles+32,votes,ends,⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (vec.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,by rw [hRank]; omega,
    fun lane hl => ⟨vec.pos lane+1,rfl,hArrive lane hl⟩⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
