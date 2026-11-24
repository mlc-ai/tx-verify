-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- Put the preserved tile facts and both computed address tables under the loop counter. -/
def correctionRescaleFrame (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  rescaleStageAddresses l (warpLane l g lane) 0 ++
    rescaleStageAddresses l (warpLane l g lane) 1 ++ correctionBeforeRescale p l g batch lane

theorem correctionRescaleFrame_ready {p : Params} {l : Launch} {g batch : Nat}
    (hBlocks : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1) :
    correctionRescaleSetupFacts p l g batch =
      rescaleLoopFacts (correctionRescaleFrame p l g batch)
        (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1) := by
  funext lane
  unfold correctionRescaleSetupFacts
  rw [ite_eq_right (by omega)]
  rfl

theorem correctionRescaleFrame_next (p : Params) (l : Launch) (g batch lane : Nat) :
    ∀ r ∈ (correctionRescaleFrame p l g batch lane).map Prod.fst, r ≠ 7278 ∧ r ≠ 735 := by
  have hCheck : ((correctionRescaleFrame p l g batch lane).map Prod.fst).all
      (fun r => decide (r ≠ 7278 ∧ r ≠ 735)) = true := rfl
  exact fun r h => of_decide_eq_true (List.all_eq_true.mp hCheck r h)

private theorem frameIn (p : Params) (l : Launch) (g batch blocks lane : Nat)
    {rv : Nat × Value} (h : rv ∈ correctionBeforeRescale p l g batch lane) :
    rv ∈ rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane :=
  List.mem_cons_of_mem _ (List.mem_append.mpr (.inr h))

private theorem correctionFrame_control (p : Params) (l : Launch) (g batch blocks lane : Nat)
    (stage : Fin 2) :
    ∀ r ∈ (rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane).map Prod.fst,
      r ≠ statsReg stage .alpha ∧ r ≠ rescalePredReg stage ∧
      r ≠ rescaleVoteReg stage ∧ r ≠ maskZeroReg stage := by
  have hCheck : ((rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane).map
      Prod.fst).all (fun r => decide (r ≠ statsReg stage .alpha ∧ r ≠ rescalePredReg stage ∧
        r ≠ rescaleVoteReg stage ∧ r ≠ maskZeroReg stage)) = true := by
    fin_cases stage <;> rfl
  exact fun r h => of_decide_eq_true (List.all_eq_true.mp hCheck r h)

private theorem correctionFrame_signals (p : Params) (l : Launch) (g batch blocks lane : Nat)
    (stage : Fin 2) :
    ∀ r ∈ (rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane).map Prod.fst,
      r ≠ rescaleCountReg stage ∧ r ≠ rescaleSignalDst stage ∧
      r ≠ rescaleSignalDst stage + 1 := by
  have hCheck : ((rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane).map
      Prod.fst).all (fun r => decide (r ≠ rescaleCountReg stage ∧ r ≠ rescaleSignalDst stage ∧
        r ≠ rescaleSignalDst stage + 1)) = true := by
    fin_cases stage <;> rfl
  exact fun r h => of_decide_eq_true (List.all_eq_true.mp hCheck r h)

private theorem correctionFrame_data (p : Params) (l : Launch) (g batch blocks lane : Nat)
    (stage : Fin 2) (chunk : Fin 8) :
    ∀ r ∈ (rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane).map Prod.fst,
      r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r := by
  unfold rescaleLocalKeeps
  have hCheck : ((rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane).map
      Prod.fst).all (fun r => decide (r ∉ rescaleDataRegs stage chunk ∧
        (∀ q ∈ rescalePacks stage chunk, q.1 ≠ r) ∧
        (∀ q ∈ rescaleMuls stage chunk, q.1 ≠ r) ∧
        (∀ q ∈ rescaleUnpacks stage chunk, q.2.1 ≠ r ∧ q.2.2 ≠ r))) = true := by
    fin_cases stage <;> fin_cases chunk <;> rfl
  exact fun r h => of_decide_eq_true (List.all_eq_true.mp hCheck r h)

/-- The concrete entry frame supplies all of the preserved registers for either rescale stage. -/
theorem correctionRescaleFrame_visit (p : Params) (l : Launch) (g batch blocks lane : Nat)
    (stage : Fin 2) :
    RescaleVisitFrame l (warpLane l g lane) stage
      (rescaleLoopFacts (correctionRescaleFrame p l g batch) blocks lane) := by
  have hIn {rv : Nat × Value} (hm : rv ∈ correctionBeforeRescale p l g batch lane) :=
    frameIn p l g batch blocks lane hm
  refine ⟨hIn ?_, hIn ?_, ?_, hIn ?_, hIn ?_, ?_, ?_, ?_⟩
  · fin_cases stage <;> simp [correctionBeforeRescale, tileSetupFrame, correctionTileGeometryFacts,
      statsBarrierReg]
  · simp [correctionBeforeRescale, tileSetupFrame, correctionTileGeometryFacts]
  · intro rv hm
    apply List.mem_cons_of_mem
    refine List.mem_append.mpr (.inl (List.mem_append.mpr ?_))
    fin_cases stage
    · exact .inl hm
    · exact .inr hm
  · fin_cases stage <;> simp [correctionBeforeRescale, tileSetupFrame, correctionActiveTileFacts,
      correctionTileFrame, afterCreditFacts, creditFacts, outputCreditReg, creditLoc]
  · fin_cases stage <;> simp [correctionBeforeRescale, tileSetupFrame, correctionTileGeometryFacts,
      correctionActiveTileFacts, correctionTileFrame, afterCreditFacts, creditFacts, entryFacts,
      Prologue.nonzeroBarrierFacts, rescaleReuseReg, rescaleReuseLoc]
  · exact fun rv hm => correctionFrame_control p l g batch blocks lane stage _
      (List.mem_map_of_mem hm)
  · exact correctionFrame_data p l g batch blocks lane stage
  · exact fun rv hm => correctionFrame_signals p l g batch blocks lane stage _
      (List.mem_map_of_mem hm)

end
end PTX.Kernels.TmlFa4Fwd.Correction
