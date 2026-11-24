-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasAffineNumerics
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Epilogue

/-- The initial mask geometry and probability addresses carried with the actual scores. -/
def openingMaskGeometry (p : Params) (l : Launch) (g batch : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  let tile := (assignedCoordinates p batch (g/l.block)).1
  [(1229,b32 (Mma.trips p batch tile-1)),(1224,b32 (p.kLength batch)),
    (3219,b32 (g%l.block)),(2868,b32 (128*(2*tile+stage.val))),
    (1223,maskSigned (-(p.qLength batch : Int)))]

/-- Each actual lane, including a padded row, reaches the mask with all four score
quarters live and the real P addresses for its stage. -/
theorem OpeningAffineLane.maskCursorWithFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch wait : Nat} {stage : Fin 2}
    (lane : OpeningAffineLane p l X g batch stage wait) :
    let entry := lane.entry
    let warp := entry.arrival.loaded.opening.warp
    let raw := firstBiasLogit (abiFloat p.invScaleBits)
      (firstBiasRegisterValue (openingBiasColumns p l g batch stage))
      (firstQkRegisterValue lane.dot)
    ∃ u, At u 3863 (openingMaskGeometry p l g batch stage) ∧
      Holds u.regs (firstAddressFacts l g stage) ∧
      firstMaskInputs u raw ∧ u.regs 7132 = some (b32 p.scaleLog2Bits) ∧
      u.regs 5127 = some (b32 (3+warp.val)) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) entry.before u ∧
      (∀ r, r ∉ firstBiasEntryWritten →
        r ∉ [3088,3089,7895,7896,7897] ++ (biasBodyItems false).flatMap BiasAffineItem.writes →
        r ∉ firstAddressWrites → u.regs r = entry.arrival.loaded.cursor.ready.regs r) := by
  let entry := lane.entry
  let loaded := entry.arrival.loaded
  let warp := loaded.opening.warp
  let tile := (assignedCoordinates p batch (g/l.block)).1
  have hStage : stageOf warp = stage := loaded.opening.selectedStage
  have hTail : Holds lane.ready.regs (tailFrame l warp) := by
    refine ⟨?_,?_,trivial⟩
    · exact (lane.frame 1062 (by decide +kernel)).trans
        ((entry.frame 1062 (by decide)).trans (holds_mem loaded.cursor.checkpoint.2.2.2.2
          (by simp [openingScoreReturnedFacts,singleVisitGeometryCarry,
            biasFenceFacts,biasKeep,warp])))
    · exact (lane.frame 2535 (by decide +kernel)).trans
        ((entry.frame 2535 (by decide)).trans (holds_mem loaded.cursor.checkpoint.2.2.2.2
          (by simp [openingScoreReturnedFacts,singleVisitGeometryCarry,biasFenceFacts,biasKeep])))
  obtain ⟨u,hRun,hu⟩ := (firstPAddressSegment hp g warp).apply (lane.reached.mono hTail)
  have hKeep := firstPAddressFrame (l := l) (g := g) lane.reached.1.ge
    (by rw [lane.reached.1]) hRun
  have hCarry (r : Nat) (hEntry : r ∉ firstBiasEntryWritten)
      (hFma : r ∉ [3088,3089,7895,7896,7897] ++ (biasBodyItems false).flatMap BiasAffineItem.writes)
      (hAddr : r ∉ firstAddressWrites) : u.regs r = loaded.cursor.ready.regs r :=
    (hKeep r hAddr).trans ((lane.frame r hFma).trans (entry.frame r hEntry))
  have hFacts {x : Nat × Value} (hx : x ∈ openingScoreReturnedFacts p l g batch tile warp) :=
    holds_mem loaded.cursor.checkpoint.2.2.2.2 hx
  have hGeometry : Holds u.regs (openingMaskGeometry p l g batch stage) := by
    refine ⟨?_,?_,?_,?_,?_,trivial⟩
    · exact (hCarry 1229 (by decide) (by decide +kernel) (by decide)).trans
        (hFacts (x := (1229,b32 (Mma.trips p batch tile-1))) (by
        simp [openingScoreReturnedFacts]))
    · exact (hCarry 1224 (by decide) (by decide +kernel) (by decide)).trans
        (hFacts (x := (1224,b32 (p.kLength batch))) (by
        simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts]))
    · exact holds_mem hu.2.2.2.2 (by simp [firstAddressFacts])
    · exact (hCarry 2868 (by decide) (by decide +kernel) (by decide)).trans
        (hFacts (x := (2868,b32 (128*(2*tile+stage.val)))) (by
        simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,hStage]))
    · exact (hCarry 1223 (by decide) (by decide +kernel) (by decide)).trans
        (hFacts (x := (1223,maskSigned (-(p.qLength batch : Int)))) (by
        simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts]))
  have hAddress := hu.2.2.2.2
  rw [hStage] at hAddress
  refine ⟨u,hu.mono hGeometry,hAddress,?_,?_,?_,
    entry.localSteps.trans (lane.localSteps.trans (run_rtg hRun)),hCarry⟩
  · intro group pair hj
    have hGroup := group.isLt
    refine (hKeep _ ?_).trans (lane.logits group pair hj)
    unfold firstMaskPairRegs firstAddressWrites
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.mem_map,List.mem_range,not_or]
    omega
  · exact (hKeep 7132 (by decide)).trans
      ((lane.frame 7132 (by decide +kernel)).trans entry.checkpoint.2.2.2.2.2.1)
  · exact (hCarry 5127 (by decide) (by decide +kernel) (by decide)).trans
      (hFacts (x := (5127,b32 (3+warp.val)))
        (by simp [openingScoreReturnedFacts,singleVisitGeometryCarry]))

theorem OpeningAffineLane.maskCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch wait : Nat} {stage : Fin 2}
    (lane : OpeningAffineLane p l X g batch stage wait) :
    let entry := lane.entry
    let warp := entry.arrival.loaded.opening.warp
    let raw := firstBiasLogit (abiFloat p.invScaleBits)
      (firstBiasRegisterValue (openingBiasColumns p l g batch stage))
      (firstQkRegisterValue lane.dot)
    ∃ u, At u 3863 (openingMaskGeometry p l g batch stage) ∧
      Holds u.regs (firstAddressFacts l g stage) ∧
      firstMaskInputs u raw ∧ u.regs 7132 = some (b32 p.scaleLog2Bits) ∧
      u.regs 5127 = some (b32 (3+warp.val)) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) entry.before u := by
  obtain ⟨u,hu,hAddr,hRaw,hScale,hBar,hPath,_⟩ := lane.maskCursorWithFrame hp
  exact ⟨u,hu,hAddr,hRaw,hScale,hBar,hPath⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
