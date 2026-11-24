-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningScoreWarp
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.TcMma Prologue Epilogue

/-- The opening QK words are still live after the first Bias acquire. -/
structure OpeningScoreBeforeBias (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (state : TState) where
  wait : Nat
  acquire : Thread.Scores.FirstScoreAcquire l X (g,wait) stage
  words : Fin 4 → List Value
  values : FirstScores l X stage g (wait+1) state words

/-- An unchanged packed register frame transports the actual opening score words. -/
def OpeningScoreBeforeBias.withFrame {l : Launch} {X : Execution} {g : Nat} {stage : Fin 2}
    {before after : TState} (hScores : OpeningScoreBeforeBias l X g stage before)
    (hFrame : ∀ q : Fin 4, ∀ k < 16,
      after.regs (firstScorePairReg q k) = before.regs (firstScorePairReg q k)) :
    OpeningScoreBeforeBias l X g stage after :=
  ⟨hScores.wait,hScores.acquire,hScores.words,
    hScores.values.1,fun q k hk => (hFrame q k hk).trans (hScores.values.2 q k hk)⟩

private noncomputable def scorePairFacts (values : Fin 4 → List Value) : List (Nat × Value) :=
  (List.finRange 4).flatMap fun quarter =>
    (List.range 16).map fun k =>
      (firstScorePairReg quarter k,
        joinValue ((values quarter).getD (2*k) (b32 0))
          ((values quarter).getD (2*k+1) (b32 0)))

private theorem holdsScorePairs {R : Nat → Option Value} {values : Fin 4 → List Value}
    (h : ∀ quarter : Fin 4, ∀ k < 16, R (firstScorePairReg quarter k) =
      some (joinValue ((values quarter).getD (2*k) (b32 0))
        ((values quarter).getD (2*k+1) (b32 0)))) : Holds R (scorePairFacts values) := by
  suffices hAll : ∀ (facts : List (Nat × Value)), (∀ x ∈ facts, R x.1 = some x.2) →
      Holds R facts by
    apply hAll
    intro x hx
    obtain ⟨q,_,hm⟩ := List.mem_flatMap.mp hx
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    exact h q k (List.mem_range.mp hk)
  intro facts
  induction facts with
  | nil => intro _; trivial
  | cons x facts ih =>
    intro hMem
    exact ⟨hMem x List.mem_cons_self,ih (fun x hx => hMem x (List.mem_cons_of_mem _ hx))⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hGuard : SyncGuarded l kernel X)
    (hLayout : LayoutInjective X) {g batch count : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) (hCuQ : DrainCuQProtected p X)
    (hUsedK : UsedKProtected p X) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3274
      (fun _ => firstActiveTileFacts p l g ⟨warpIndex l g,hw⟩ batch) count 1 ends)
    (hAck : ∀ peer, SameWarp l g peer → (¬ ∃ j, Thread.Scores.CreditAcquired X (peer,j)) →
      OpeningPollReady X (waitLoc l peer (stageOf ⟨warpIndex l g,hw⟩) 0) 1)
    (hScore : ∀ peer, SameWarp l g peer →
      (¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (peer,j) (stageOf ⟨warpIndex l g,hw⟩)) →
      OpeningPollReady X (waitLoc l peer (stageOf ⟨warpIndex l g,hw⟩) 1) 0)
    (hBytes : OpeningScoreWords l X g)
    (hBias : let stage := stageOf ⟨warpIndex l g,hw⟩
      okPolls (Thread.Loader.biasReadyObject l (g/l.block) stage) (X.tr g) = 0 →
      OpeningPollReady X (waitLoc l g stage 2) 0)
include hp hMax hGuard hLayout hg hw hb hLo hHi hCuQ hUsedK cur hAck hScore hBytes hBias

/-- A selected warp with defined score words reaches the first Bias readiness acquisition
on the anchor lane, with the actual Bias address frame at the returned cursor. -/
theorem openingBiasOfSelectedWarpWithWordsAndCount :
    let warp : Fin 8 := ⟨warpIndex l g,hw⟩
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j (stageOf warp) ∧
      ∃ after : OpeningLaneCursor l X g 3501
        (openingScoreReturnedFacts p l g batch (assignedCoordinates p batch (g/l.block)).1 warp)
        (ends (laneOf l g)),
        after.pos = j+1 ∧ ((X.tr g).take after.pos).countP isTcColl = 4 ∧
        Nonempty (OpeningScoreBeforeBias l X g (stageOf warp) after.ready) := by
  dsimp only
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  let stage := stageOf warp
  let thread := warpLane l g
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let F := fun lane => openingScoreReturnedFacts p l (thread lane) batch tile warp
  obtain ⟨returned,hReturned⟩ :=
    openingScoreReturnedWarpOfSelected hp hMax hg hw hb hLo hHi hCuQ hUsedK cur hAck hScore
  have hKeep (lane : Nat) (hl : lane < 32) (pair : Nat × Value) (hm : pair ∈ F lane) :
      firstScoreKeeps pair.1 := by
    have hAudit : ((F lane).map Prod.fst).all
        (fun r => decide ((r < 2881 ∨ 3011 ≤ r) ∧ (r < 7303 ∨ 7367 ≤ r))) = true := rfl
    change (pair.1 < 2881 ∨ 3011 ≤ pair.1) ∧ (pair.1 < 7303 ∨ 7367 ≤ pair.1)
    exact of_decide_eq_true (List.all_eq_true.mp hAudit pair.1 (List.mem_map_of_mem hm))
  have hAddr0 (lane : Nat) (hl : lane < 32) :
      (2788,b32 (scoreAddress l (thread lane) stage 0)) ∈ F lane := by
    simp [F,openingScoreReturnedFacts,firstGeometryAckFacts,stage]
  have hAddr2 (lane : Nat) (hl : lane < 32) :
      (2789,b32 (scoreAddress l (thread lane) stage 2)) ∈ F lane := by
    simp [F,openingScoreReturnedFacts,singleVisitGeometryCarry,stage]
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨entered,hEntered⟩ := openingBiasPollCursorOfScoreWarp
    hp hMax hGuard hLayout hg stage returned
    (fun lane hl => by obtain ⟨_,_,_,h⟩ := hReturned lane hl; exact h)
    hKeep hAddr0 hAddr2 (fun q lane hl _ _ he => by
      obtain ⟨_, hFirst, _, _⟩ := hReturned lane hl
      exact hBytes.observed q (Step.sameWarp_lane hBlock hg hl).1 hFirst he)
  let lane := laneOf l g
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hEq : warpLane l g lane = g := Step.warpLane_of_sameWarp hSelf
  let c := entered lane hLane
  let G := openingScoreReturnedFacts p l g batch tile warp
  let ready : OpeningLaneCursor l X g 3498 G (ends lane) :=
    ⟨c.pos,c.before,c.ready,c.positive,by simpa only [hEq] using c.bounded,
      by simpa only [hEq] using c.released,by simpa only [hEq] using c.recorded,
      by simpa only [hEq] using c.continuation,by simpa only [hEq] using c.localSteps,
      by simpa only [F,G,hEq] using c.checkpoint⟩
  have hBase : (2771,b32 (waitLoc l g stage 2).addr) ∈ G := by
    simp [G,openingScoreReturnedFacts,singleVisitGeometryCarry,stage,warp]
  have hParity : (2770,b32 0) ∈ G := by simp [G,openingScoreReturnedFacts]
  have hFresh : ∀ pair ∈ G, pair.1 ≠ 9752 := by
    intro pair hm hReg
    have hNo : 9752 ∉ G.map Prod.fst := of_decide_eq_true rfl
    exact hNo (hReg ▸ List.mem_map_of_mem hm)
  obtain ⟨scoreWait,hFirst,hAfter,_⟩ := hReturned lane hLane
  have hTileLoaded : OpeningScoreTileLoaded l X stage g (scoreWait+1) ready.ready := by
    simpa only [hAfter,hEq] using (hEntered lane hLane).2.2
  have hFirst' : Thread.Scores.FirstScoreAcquire l X (g,scoreWait) stage := hEq ▸ hFirst
  choose values hLength hRead hPack using hTileLoaded
  let extra := scorePairFacts values
  have hExtra : Holds ready.ready.regs extra := holdsScorePairs hPack
  let start := ready.weaken ((holds_append _ G extra).mpr ⟨ready.checkpoint.2.2.2.2,hExtra⟩)
  have hExtraFresh (pair : Nat × Value) (hMem : pair ∈ extra) : pair.1 ≠ 9752 := by
    obtain ⟨q,_,hm⟩ := List.mem_flatMap.mp hMem
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    have hq := q.isLt
    change firstScorePairReg q k ≠ 9752
    unfold firstScorePairReg
    have hK := List.mem_range.mp hk
    omega
  have hFresh' : ∀ pair ∈ G ++ extra, pair.1 ≠ 9752 := by
    intro pair hMem
    exact (List.mem_append.mp hMem).elim (hFresh pair) (hExtraFresh pair)
  obtain ⟨wait,hWait,after,hPos,hCount⟩ := openingBiasAcquireOfCursorWithTcCount hp hMax hg hw
    stage rfl start
    (List.mem_append_left _ hBase) (List.mem_append_left _ hParity) hFresh' hBias
  have hFrame := (holds_append _ G extra).mp after.checkpoint.2.2.2.2
  let final := after.weaken hFrame.1
  have hStartCount : ((X.tr g).take start.pos).countP isTcColl = 4 := by
    change ((X.tr g).take (entered lane hLane).pos).countP isTcColl = 4
    simpa only [hEq] using (hEntered lane hLane).2.1
  refine ⟨wait,hWait,final,hPos,hCount.trans hStartCount,⟨⟨scoreWait,hFirst',values,?_,?_⟩⟩⟩
  · exact fun q => ⟨hLength q,hRead q⟩
  · intro q k hk
    exact holds_mem hFrame.2 (List.mem_flatMap.mpr
      ⟨q,by simp,List.mem_map_of_mem (List.mem_range.mpr hk)⟩)

end

/-- The lane's actual continuation immediately after its first Bias acquire. -/
structure OpeningBiasLane (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) (wait : Nat) where
  warp : Fin 8
  selectedStage : stageOf warp = stage
  ending : Option TState
  cursor : OpeningLaneCursor l X g 3501
    (openingScoreReturnedFacts p l g batch (assignedCoordinates p batch (g/l.block)).1 warp) ending
  position : cursor.pos = wait+1
  tensorCount : ((X.tr g).take cursor.pos).countP isTcColl = 4
  scores : OpeningScoreBeforeBias l X g stage cursor.ready

end PTX.Kernels.TmlFa4Fwd.Softmax
