-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalLayout
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStage

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- Both stages share the launch and tile layout. The second stage also retains the first
stage's sum, maximum, and initialized phase word. -/
def correctionFinalizeBase (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  finalizeLayoutFacts l (warpLane l g lane) ++
    (7134, b32 p.scaleLog2Bits) :: correctionBeforeRescale p l g batch lane

def correctionFinalStageFacts (p : Params) (l : Launch) (g batch lane : Nat)
    (sum0 max0 : ℝ) (stage : Fin 2) : List (Nat × Value) :=
  let base := correctionFinalizeBase p l g batch lane
  if stage.val = 0 then base else
    (6496, b32 0) :: (739, .pred (decide (sum0 ≠ 0))) :: finalStatsFacts 0 sum0 max0 base

private theorem keysEach {F : List (Nat × Value)} {P : Nat → Prop}
    [DecidablePred P] (h : (F.map Prod.fst).all (fun r => decide (P r)) = true) :
    ∀ rv ∈ F, P rv.1 := fun _ hm => of_decide_eq_true
  (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))

private theorem onKeys {F : List (Nat × Value)} {r : Nat} (hn : r ∉ F.map Prod.fst) :
    ∀ rv ∈ F, rv.1 ≠ r := by
  intro rv hm h
  have hm' := List.mem_map_of_mem (f := Prod.fst) hm
  rw [h] at hm'
  exact hn hm'

private theorem finalizeDataFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (sum0 max0 sum maximum : ℝ) (stage : Fin 2) :
    let F := correctionFinalStageFacts p l g batch lane sum0 max0 stage
    let thread := warpLane l g lane
    let G := outputSignalFacts l thread stage ++ finalStageLoadFacts l stage sum maximum F
    ∀ chunk, ∀ r ∈ G.map Prod.fst,
      r ∉ finalizeDataRegs stage chunk ∧
      (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
      (∀ half : Fin 2, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1)) := by
  intro F thread G chunk r hr
  have h : (G.map Prod.fst).all (fun r => decide (
        r ∉ finalizeDataRegs stage chunk ∧
        (∀ q ∈ finalizePacks stage chunk, q.1 ≠ r) ∧
        (∀ q ∈ finalizeMuls stage chunk, q.1 ≠ r) ∧
        (∀ half : Fin 2, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
        (chunk.val < 4 → r ≠ outputStoreAddrReg stage (finalizeVector chunk 1)))) = true := by
    fin_cases stage <;> fin_cases chunk <;> rfl
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

private theorem finalizeStageSurfaceFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (sum0 max0 sum maximum : ℝ) (stage : Fin 2) :
    let F := correctionFinalStageFacts p l g batch lane sum0 max0 stage
    let thread := warpLane l g lane
    let G := outputSignalFacts l thread stage ++ finalStageLoadFacts l stage sum maximum F
    FinalizeSurfaceRegisters l thread stage (normalizingReciprocal sum) G := by
  intro F thread G
  have hIn {rv : Nat × Value} (hm : rv ∈ F) : rv ∈ G :=
    List.mem_append.mpr (.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))))))
  have hBase {rv : Nat × Value} (hm : rv ∈ correctionFinalizeBase p l g batch lane) : rv ∈ G := by
    apply hIn
    fin_cases stage
    · exact hm
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
  refine ⟨hBase ?_, hBase ?_, hBase ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [thread, correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
      correctionTileGeometryFacts]
  · fin_cases stage <;> simp [thread, correctionFinalizeBase,
      correctionBeforeRescale, tileSetupFrame, correctionTileGeometryFacts, finalizeAddressReg]
  · simp [thread, correctionFinalizeBase, finalizeLayoutFacts, finalizeDeltas]
  · intro chunk hPos hlt
    apply hBase
    fin_cases chunk <;> try (simp at hPos hlt)
    all_goals
      simp [thread, correctionFinalizeBase, finalizeLayoutFacts, finalizeDeltas,
        finalizeEvenDeltaReg, finalizeEvenDelta]
  · exact List.mem_append.mpr (.inr List.mem_cons_self)
  · intro chunk hc
    apply onKeys
    exact of_decide_eq_true (by
      fin_cases stage <;> fin_cases chunk <;> try (simp at hc)
      all_goals rfl)
  · intro chunk hc hlt
    apply onKeys
    exact of_decide_eq_true (by
      fin_cases stage <;> fin_cases chunk <;> try (simp at hc hlt)
      all_goals rfl)
  · exact finalizeDataFrame p l g batch lane sum0 max0 sum maximum stage

/-- The exact concrete correction frame has all operands of either final stage and
does not alias the temporary scalar, Tensor Memory or packed arithmetic destinations. -/
theorem correctionFinalStageFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (sum0 max0 sum maximum : ℝ) (stage : Fin 2) :
    FinalStageFrame l (warpLane l g lane) stage sum maximum
      (correctionFinalStageFacts p l g batch lane sum0 max0 stage) := by
  let thread := warpLane l g lane
  let F := correctionFinalStageFacts p l g batch lane sum0 max0 stage
  have hIn {rv : Nat × Value} (hm : rv ∈ correctionFinalizeBase p l g batch lane) : rv ∈ F := by
    fin_cases stage
    · exact hm
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
  refine ⟨hIn ?_, hIn ?_, hIn ?_, hIn ?_, hIn ?_, ?_, ?_, ?_, ?_, ?_, hIn ?_, ?_, ?_, ?_⟩
  · fin_cases stage <;> simp [correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
      correctionTileGeometryFacts, statsBarrierReg]
  · simp [correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
      correctionTileGeometryFacts]
  · simp [correctionFinalizeBase, finalizeLayoutFacts]
  · fin_cases stage <;> simp [correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
      correctionTileGeometryFacts, correctionActiveTileFacts, correctionTileFrame, afterCreditFacts,
      creditFacts, entryFacts, Prologue.nonzeroBarrierFacts, rescaleReuseLoc, rescaleReuseReg]
  · simp [correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
      correctionActiveTileFacts, correctionTileFrame, afterCreditFacts, creditFacts, entryFacts,
      Prologue.nonzeroBarrierFacts]
  · apply keysEach (F := F) (P := fun r =>
      r ≠ statsReg stage .sum ∧ r ≠ statsReg stage .maximum ∧ r ≠ finalStatsReleaseDst stage ∧
        r ∉ [reciprocalPred stage, reciprocalInput stage, reciprocalReg stage])
    fin_cases stage <;> rfl
  · apply onKeys
    exact of_decide_eq_true (by fin_cases stage <;> rfl)
  · apply keysEach (P := fun r =>
      (∀ free, r ≠ finalizePollPred stage free) ∧ r ≠ finalizeReciprocalPair stage)
    fin_cases stage <;> rfl
  · intro free
    fin_cases stage <;> cases free <;> simp [correctionFinalStageFacts, correctionFinalizeBase,
      finalizeLayoutFacts, correctionBeforeRescale, tileSetupFrame, correctionTileGeometryFacts,
      correctionActiveTileFacts, correctionTileFrame, afterCreditFacts, creditFacts, entryFacts,
      Prologue.nonzeroBarrierFacts, finalStagePollFacts, finalStageReciprocalFacts, finalStatsFacts,
      finalizePollBase, finalizePollLoc, finalPollPrepReg, finalPollPrepWord]
  · intro free
    fin_cases stage <;> cases free <;> simp [correctionFinalStageFacts, correctionFinalizeBase,
      finalizeLayoutFacts, finalStagePollFacts, finalStageReciprocalFacts, finalStatsFacts,
      finalizePollPhase, finalPollPrepReg, finalPollPrepWord]
  · fin_cases stage <;> simp [correctionFinalizeBase, finalizeLayoutFacts]
  · intro rv hm
    apply hIn
    simp only [outputSignalFacts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · fin_cases stage <;> simp [correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
        correctionActiveTileFacts, correctionTileFrame, afterCreditFacts, creditFacts,
        outputCreditReg, creditLoc]
    · fin_cases stage <;> simp [correctionFinalizeBase, correctionBeforeRescale, tileSetupFrame,
        correctionActiveTileFacts, correctionTileFrame, afterCreditFacts, creditFacts, entryFacts,
        Prologue.nonzeroBarrierFacts, outputReadyReg, outputReadyBase]
    · simp [correctionFinalizeBase, finalizeLayoutFacts]
  · exact finalizeStageSurfaceFrame p l g batch lane sum0 max0 sum maximum stage
  · apply keysEach (P := fun r => r ≠ outputCreditDst stage ∧ r ≠ outputCreditDst stage + 1)
    fin_cases stage <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Correction
