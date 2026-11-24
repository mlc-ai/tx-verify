-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainLaterRead
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainPrepare

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- After the later group's down shuffle, the lane computes its tile count and the five
guards for the up scan while retaining the scheduler state. -/
theorem drainLaterPrepared {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) {first base stop cta : Nat}
    (hl : laneOf l g < 32) (hIndex : first + laneOf l g < 2 ^ 31)
    (ht : At t 3046 (drainLaterWords p l g first ++ drainLaterGroup p l g first base stop cta)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧ At u (drainScanPc true 0)
      [(7232, b32 (groupLaneTiles p first (laneOf l g)))] ∧
      (∀ stage : Fin 5, u.regs (drainScanGuardReg true stage) =
        some (.pred (drainScanGuard stage (laneOf l g)))) ∧
      (∀ r ∈ drainPersistent, u.regs r = t.regs r) := by
  let lane := laneOf l g
  let source := (shflSource .down lane 1 31).1
  let active := decide (first + lane < p.batch ∧ lane < 31)
  obtain ⟨hBegin, hFinish, hMono, hLength, hTiles⟩ := drainWordTiles hp first lane
  have hGateAt : At t 3046 [(2422, b32 (drainCuQ p (first + source))),
      (7231, b32 (drainCuQ p (first + lane))), (1212, b32 (first + lane)), (7147, b32 p.batch),
      (319, .pred (decide (lane = 31)))] := by
    apply ht.mono
    simp only [drainLaterWords, drainLaterWordFacts, drainLaterGroup, drainLaterCommon] at ht
    exact ⟨holds_mem ht.2.2.2.2 (by simp [lane, source]),
      holds_mem ht.2.2.2.2 (by simp [lane]), holds_mem ht.2.2.2.2 (by simp [lane]),
      holds_mem ht.2.2.2.2 (by simp), holds_mem ht.2.2.2.2 (by simp [lane]), trivial⟩
  obtain ⟨v, hGate, hv⟩ := drainLaterTileGate l g _ hIndex hp.shape.2.1 hBegin hFinish t hGateAt
  have hSkip : (decide (lane = 31) || decide (p.batch ≤ first + lane)) = !active := by
    have hLane : lane < 32 := hl
    by_cases hL : lane < 31
    · by_cases hB : first + lane < p.batch
      · simp [active, hL, hB, show lane ≠ 31 by omega, show ¬ p.batch ≤ first + lane by omega]
      · simp [active, hL, hB, show p.batch ≤ first + lane by omega]
    · simp [active, show lane = 31 by omega]
  rw [hSkip] at hv
  obtain ⟨w, hTile, hw⟩ := drainLaterLaneTiles l g active hBegin hMono hLength v hv
  have hCountRun := run_comp hGate hTile
  obtain ⟨_, hCountFrame⟩ := drainPrepareRun true ht.1 hCountRun
  have hLaneAt : At w (drainScanPc true 0 - 5) [(1201, b32 lane)] := by
    apply hw.mono
    refine ⟨(hCountFrame 1201 (by decide)).trans (holds_mem ht.2.2.2.2 ?_), trivial⟩
    simp [drainLaterGroup, drainLaterCommon, lane]
  obtain ⟨u, hGuards, hu⟩ := drainScanPrepare true l g hl w hLaneAt
  have hpc := hw.1
  obtain ⟨_, hGuardFrame, _, _⟩ := epilogueLinearRun (F := [325, 326, 327, 328, 329])
    (t := w) (n := 5) (by omega) (by omega) (by
      intro pc hlo hhi
      have hCases : pc = 3061 ∨ pc = 3062 ∨ pc = 3063 ∨ pc = 3064 := by omega
      rcases hCases with rfl | rfl | rfl | rfl
      · exact ⟨_, Flow.code_3061, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3062, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3063, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3064, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hpc]
      exact ⟨_, Flow.code_3065, by simp [writesRegs]⟩) hw.2.1 hw.2.2.1 hGuards
  have hWord : u.regs 7232 = some (b32 (groupLaneTiles p first lane)) := by
    rw [hGuardFrame 7232 (by decide), ← hTiles]
    exact hw.2.2.2.2.1
  obtain ⟨hRun, hFrame⟩ := drainPrepareRun true ht.1 (run_comp hCountRun hGuards)
  refine ⟨_, u, hRun, hu.mono ⟨hWord, trivial⟩, ?_, hFrame⟩
  intro stage
  fin_cases stage <;> exact holds_mem hu.2.2.2.2 (by simp [drainScanGuardReg, drainScanGuard])

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
