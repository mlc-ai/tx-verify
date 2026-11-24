-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometryReads
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasAddresses
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningWaitHistory
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- The actual lane prefix and its event-free continuation to a decoded checkpoint. -/
structure OpeningLaneCursor (l : Launch) (X : Execution) (g pc : Nat)
    (facts : List (Nat × Value)) (ending : Option TState) where
  pos : Nat
  before : TState
  ready : TState
  positive : 0 < pos
  bounded : pos ≤ (X.tr g).length
  released : pos = (X.tr g).length → Step.Released l X g
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready
  checkpoint : At ready pc facts

/-- An event-free decoded segment advances the local part of an actual lane cursor. -/
theorem OpeningLaneCursor.advance {l : Launch} {X : Execution} {g pc pc' steps : Nat}
    {F G : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g pc F ending)
    (segment : Seg kernel Assumptions.all l g steps pc F pc' G) :
    Nonempty (OpeningLaneCursor l X g pc' G ending) := by
  obtain ⟨u, hr, hu⟩ := segment.apply c.checkpoint
  exact ⟨⟨c.pos,c.before,u,c.positive,c.bounded,c.released,c.recorded,c.continuation,
    c.localSteps.trans (run_rtg hr),hu⟩⟩

/-- Restrict the register frame of an actual cursor without changing its trace boundary. -/
def OpeningLaneCursor.weaken {l : Launch} {X : Execution} {g pc : Nat}
    {F G : List (Nat × Value)} {ending : Option TState}
    (c : OpeningLaneCursor l X g pc F ending) (h : Holds c.ready.regs G) :
    OpeningLaneCursor l X g pc G ending where
  pos := c.pos
  before := c.before
  ready := c.ready
  positive := c.positive
  bounded := c.bounded
  released := c.released
  recorded := c.recorded
  continuation := c.continuation
  localSteps := c.localSteps
  checkpoint := c.checkpoint.mono h

private theorem geometrySyncRegisters (l : Launch) (g : Nat) (stage : Fin 2) :
    ∀ pair ∈ firstGeometrySync l g stage, pair.1 ∈ firstGeometryCarryRegs := by
  intro pair hp
  simp only [firstGeometrySync,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact of_decide_eq_true rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (warp : Fin 8) (hb : batch < p.batch)
    (hTile : 256*(assignedCoordinates p batch (g/l.block)).1 < p.qLength batch)
    {ending : Option TState}
    (c : OpeningLaneCursor l X g 3274 (firstActiveTileFacts p l g warp batch) ending)
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
include hp hMax hg warp hb hTile c hCuQ hUsedK

/-- The same selected prefix reaches the acknowledgement with every initial score and Bias
address still live. -/
theorem openingGeometryAckCursorWithCarryOfSelected :
    ∃ after : OpeningLaneCursor l X g 3420
        (firstGeometryAckFacts p l g batch (assignedCoordinates p batch (g/l.block)).1
          (stageOf warp) ++ singleVisitGeometryCarry l g warp) ending,
      after.pos = c.pos + 3 ∧ FirstGeometryReads p X g c.pos batch := by
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let stage := stageOf warp
  let C := singleVisitGeometryCarry l g warp
  have hC := singleVisitGeometryCarryRegs l g warp
  let F := firstGeometrySync l g stage ++ C
  have hF : ∀ pair ∈ F, pair.1 ∈ firstGeometryCarryRegs := by
    intro pair hm
    rcases List.mem_append.mp hm with h | h
    · exact geometrySyncRegisters l g stage pair h
    · exact hC pair h
  obtain ⟨addr,hAddrRun,hAddr⟩ := (firstActiveBiasAddresses hp g warp batch).apply c.checkpoint
  have hAddr' : At addr 3367 (geometryAddressInputs p batch tile stage ++ F) := by
    simpa only [firstGeometryAddressInput,List.append_assoc] using hAddr
  obtain ⟨args,hArgsRun,hArgs⟩ :=
    (geometryAddressSegmentFramed hp g batch tile stage hb hF).apply hAddr'
  obtain ⟨last,u,hu,hPast,hRest,hLocal,hReads⟩ :=
    geometryReadsOfMaximal hp hMax hg stage hb hF hTile hArgs hCuQ hUsedK
      c.recorded c.continuation (c.localSteps.trans ((run_rtg hAddrRun).trans (run_rtg hArgsRun)))
      c.positive c.bounded c.released
  obtain ⟨hFacts,hGeometry⟩ := (holds_append ..).mp hu.2.2.2.2
  obtain ⟨hSync,hCarry⟩ := (holds_append ..).mp hFacts
  obtain ⟨v,hv,hV⟩ := (firstGeometryAckSetup hp g batch tile stage).apply
    (hu.mono ((holds_append ..).mpr ⟨hSync,hGeometry⟩))
  have hKept := holdsSchedulerFrame hCarry (geometryAckFrame false hu.1 hv) hC
  have hV' := hV.mono ((holds_append ..).mpr ⟨hV.2.2.2.2,hKept⟩)
  have hLast : X.get (g,c.pos+2) = _ := hReads.2.2
  have hPos : c.pos+2+1 = c.pos+3 := by omega
  refine ⟨⟨c.pos+3,last,v,by omega,?_,?_,hPast,hRest,hLocal.trans (run_rtg hv),hV'⟩,rfl,hReads⟩
  · exact hPos ▸ len_of_get hLast
  · exact hPos ▸ releasedIfLast hLast (by intro h; cases h)

omit hp hMax hg warp hb hTile c hCuQ hUsedK in
/-- The barrier history admits the requested parity only if its final phase has moved past it. -/
def OpeningPollReady (X : Execution) (loc : Loc) (parity : Nat) : Prop :=
  let log := X.objects loc
  ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase % 2 ≠ parity % 2

omit hp hMax hg warp hb hTile c hCuQ hUsedK in
private theorem openingAckFresh (p : Params) (l : Launch) (g batch tile : Nat) (stage : Fin 2) :
    ∀ pair ∈ firstGeometryAckFacts p l g batch tile stage, pair.1 ≠ 9750 ∧ pair.1 ≠ 9751 := by
  intro pair hPair
  simp only [firstGeometryAckFacts,firstGeometryFacts,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hPair
  rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact of_decide_eq_true rfl

omit hp hMax hg warp hb hTile c hCuQ hUsedK in
/-- The carried frame immediately after the first score acquire. -/
def openingScoreReturnedFacts (p : Params) (l : Launch) (g batch tile : Nat) (warp : Fin 8) :
    List (Nat × Value) :=
  [(1229, b32 (Mma.trips p batch tile-1)), (2770, b32 0)] ++
    firstGeometryAckFacts p l g batch tile (stageOf warp) ++ singleVisitGeometryCarry l g warp

/-- Actual selected-lane replay returns from the first score acquire with its full Bias
address frame and the real prefix and suffix at the first score load. -/
theorem openingScoreReturnOfSelected
    (hAckReady : (¬ ∃ j, Thread.Scores.CreditAcquired X (g,j)) →
      OpeningPollReady X (waitLoc l g (stageOf warp) 0) 1)
    (hScoreReady : (¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (g,j) (stageOf warp)) →
      OpeningPollReady X (waitLoc l g (stageOf warp) 1) 0) :
    ∃ ack score,
      X.get (g,ack) = some ⟨3420,.wait (waitLoc l g (stageOf warp) 0) 1 true true .cta⟩ ∧
      X.get (g,score) = some ⟨3425,.wait (waitLoc l g (stageOf warp) 1) 0 true true .cta⟩ ∧
      c.pos + 3 ≤ ack ∧ ack < score ∧
      ∃ after : OpeningLaneCursor l X g 3428
        (openingScoreReturnedFacts p l g batch (assignedCoordinates p batch (g/l.block)).1 warp)
        ending,
        after.pos = score + 1 := by
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let stage := stageOf warp
  let C := singleVisitGeometryCarry l g warp
  let F := firstGeometryAckFacts p l g batch tile stage ++ C
  have hC := singleVisitGeometryCarryRegs l g warp
  obtain ⟨d, hd, _⟩ :=
    openingGeometryAckCursorWithCarryOfSelected hp hMax hg warp hb hTile c hCuQ hUsedK
  obtain ⟨fails,last,after,hEvent,hPast,hRest,hLocal,hAt⟩ :=
    waitOfMaximal hp hMax hg stage 0 (phase := 1) (by decide)
      (F := F) (fun pair hm => by
        rcases List.mem_append.mp hm with hf | hf
        · exact (openingAckFresh p l g batch tile stage pair hf).1
        · have hNe : (waitSite 0).result ∉ firstGeometryCarryRegs := by decide
          exact fun hEq => hNe (hEq ▸ hC pair hf))
      (by simp [F,waitSite,firstGeometryAckFacts]) (by simp [F,waitSite,firstGeometryAckFacts])
      (fun hRun hTail hStop => hAckReady (noStatisticsCreditAtOpeningCursor hRun hTail hStop.1))
      d.positive d.bounded d.released d.checkpoint d.recorded
      d.continuation d.localSteps
  have hTrips := Mma.trips_bounds hp hb hTile
  have hKey := (hp.lengths batch hb).2.2
  have hTripSmall : Mma.trips p batch tile < 2^31 := by dsimp only [tile]; omega
  obtain ⟨hBase,hCarry⟩ := (holds_append ..).mp hAt.2.2.2.2
  obtain ⟨u,hu,hU⟩ :=
    (firstGeometryCountSetup p l g batch tile stage hTrips.1 hTripSmall).apply (hAt.mono hBase)
  let G := openingScoreReturnedFacts p l g batch tile warp
  have hKept := holdsSchedulerFrame hCarry (geometryAckFrame true hAt.1 hu) hC
  have hU' : At u 3425 G := hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,hKept⟩)
  have hFresh : ∀ pair ∈ G, pair.1 ≠ (waitSite 1).result := by
    intro pair hm
    simp only [G,openingScoreReturnedFacts,List.cons_append,List.nil_append,List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · rcases List.mem_append.mp hm with hf | hf
      · exact (openingAckFresh p l g batch tile stage pair hf).2
      · have hNe : (waitSite 1).result ∉ firstGeometryCarryRegs := by decide
        exact fun hEq => hNe (hEq ▸ hC pair hf)
  obtain ⟨retries,s,v,hScore,hScorePast,hScoreTail,hVLocal,hV⟩ :=
    waitOfMaximal hp hMax hg stage 1 (phase := 0) (by decide) (F := G) hFresh
      (by simp [G,openingScoreReturnedFacts,waitSite,firstGeometryAckFacts,stage])
      (by simp [G,openingScoreReturnedFacts,waitSite])
      (fun hRun hTail hStop => hScoreReady (noScoreAtOpeningCursor hRun hTail hStop.1 stage))
      (Nat.succ_pos _) (len_of_get hEvent)
      (releasedIfLast hEvent (by intro h; cases h)) hU' hPast hRest (hLocal.trans (run_rtg hu))
  let pos := d.pos+fails+1+retries
  let result : OpeningLaneCursor l X g 3428 G ending :=
    ⟨pos+1,s,v,Nat.succ_pos _,len_of_get hScore,
      releasedIfLast hScore (by intro h; cases h),hScorePast,hScoreTail,hVLocal,hV⟩
  exact ⟨d.pos+fails,pos,hEvent,hScore,by omega,by dsimp [pos]; omega,result,rfl⟩

/-- Given the statistics and score phase proofs, the same selected lane records its opening
statistics acknowledgement and the successful initial score acquire. -/
theorem openingScorePollOfSelected
    (hAckReady : (¬ ∃ j, Thread.Scores.CreditAcquired X (g,j)) →
      OpeningPollReady X (waitLoc l g (stageOf warp) 0) 1)
    (hScoreReady : (¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (g,j) (stageOf warp)) →
      OpeningPollReady X (waitLoc l g (stageOf warp) 1) 0) :
    ∃ ack score,
      X.get (g,ack) = some ⟨3420,.wait (waitLoc l g (stageOf warp) 0) 1 true true .cta⟩ ∧
      X.get (g,score) = some ⟨3425,.wait (waitLoc l g (stageOf warp) 1) 0 true true .cta⟩ ∧
      c.pos + 3 ≤ ack ∧ ack < score := by
  obtain ⟨ack,score,hAck,hScore,hLo,hLt,_⟩ :=
    openingScoreReturnOfSelected hp hMax hg warp hb hTile c hCuQ hUsedK hAckReady hScoreReady
  exact ⟨ack,score,hAck,hScore,hLo,hLt⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
