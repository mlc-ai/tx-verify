-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvOutputCut
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvProbability
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualKvOperands
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputTmemWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator

@[expose] public section

/-! # Finite PV results at an actual output load guard -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy MmaDataTrace Protocol
open Wg1Mma (pvDest tmemO)
open PvAccumulatorSource (Issue StoreHistory)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An observed PV cell is real using only the causal prefix of its consuming output load. -/
theorem causal_pv_cell {g i consumer cut limit block : Nat} {out : Wg0.D}
    (half : Fin 2) (part : Fin 4) (head : Fin 64) (col : Fin 256)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hCut : PvOutputCut.Cut P L X consumer cut g limit)
    (hOutput : Frame.stateAt (Machine.code P L) X consumer cut = some (some (.wg0 out)))
    (hLane : head.val + 64 * (col.val / 128) = tidOf L consumer)
    (hBlock : block ≤ limit)
    (hi : Issue L X g i block (pvHalfIssue half part))
    (hState : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half part), block⟩))) :
    ∃ x : ℝ, TcMma.Result L Assumptions.all X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (.float .f32 x) := by
  let issue := pvHalfIssue half part
  let cell : TcMma.Cell :=
    ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
  have hPart := part.isLt
  have hHalf := half.isLt
  have hCol := col.isLt
  have hIssue : issue.val % 2 = half.val := by dsimp [issue, pvHalfIssue]; omega
  have hDest : pvDest issue = tmemO + 128 * half.val := by rw [pvDest, hIssue]
  obtain ⟨hDone, hBefore⟩ := hCut.completes hi hState rfl hBlock
  have hCellCol : cell.column < 256 := by
    change tmemO + 128 * half.val + col.val % 128 < 256
    rw [tmemO]
    omega
  have hHistory : StoreHistory P L X (g, i) cell :=
    PvAccumulatorSource.store_history_at_cut hpre hX hs hOutput hCut.cta hLane hCellCol hBefore
  have hSeed : ∃ x, GemmAccumulator L X (g, i) cell (pvAccum block issue) x := by
    by_cases hZero : part.val = 0
    · have hPartZero : part = 0 := Fin.ext hZero
      subst part
      by_cases hb : block = 0
      · subst block
        have hAcc : pvAccum 0 issue = false := PvInitialAccumulator.first_overwrites half
        exact ⟨0, hAcc ▸ .overwrite⟩
      · have hPos : 0 < block := Nat.pos_of_ne_zero hb
        have hAcc : pvAccum block issue = true := by simp [pvAccum, hb]
        obtain ⟨src, hRead, hKind⟩ :=
          PvInitialAccumulator.actual_from_first_issue hpre hX hs hi hState hPos head col hHistory
        rcases hKind with ⟨prior, _, rfl, hPrior, hIssue, _⟩ |
          ⟨lane, index, q, tile, rfl, hStore, _⟩
        · obtain ⟨x, hx⟩ := causal_pv_cell half 3 head col hpre hX hs hCut hOutput hLane
            (show block - 1 ≤ limit by omega) hIssue hPrior
          exact ⟨x, hAcc ▸ .priorMma hRead hx⟩
        · obtain ⟨x, hx⟩ := PvAccumulatorSource.rescale_store_f32 hStore
          exact ⟨x, hAcc ▸ .priorStore hRead hx⟩
    · let oldPart : Fin 4 := ⟨part.val - 1, by omega⟩
      let prev := pvHalfIssue half oldPart
      let middle : Fin 8 := ⟨issue.val - 1, by have := issue.isLt; omega⟩
      have hPrevVal : prev.val + 2 = issue.val := by
        dsimp [prev, oldPart, issue, pvHalfIssue]
        omega
      have hMidVal : middle.val + 1 = issue.val := by dsimp [middle, issue, pvHalfIssue]; omega
      have hParity : prev.val % 2 = issue.val % 2 := by omega
      have hDifferent : middle.val % 2 ≠ prev.val % 2 := by omega
      have hPrevDest : pvDest prev = tmemO + 128 * half.val := by
        simp only [pvDest, hParity, hIssue]
      obtain ⟨j, hJ, hPrevState, hPrev⟩ :=
        PvIssueHistory.pv_issue_before hpre hX hs hi.choose_spec hState prev (by omega)
      obtain ⟨m, hM, _, hMid⟩ :=
        PvIssueHistory.pv_issue_before hpre hX hs hi.choose_spec hState middle (by omega)
      have hJIdx : j + 2 = i := by omega
      have hMIdx : j + 1 = m := by omega
      have hHist : StoreHistory P L X (g, j + 2)
          ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest prev + col.val % 128⟩ := by
        rw [hJIdx, hPrevDest]
        exact hHistory
      have hRead := PvAccumulatorSource.actual_previous_of_adjacent hpre hX hs hPrev
        (by rwa [hMIdx]) (by rwa [hJIdx]) hPrevState (by rwa [hJIdx]) hParity hDifferent
        head col hHist
      rw [hJIdx, hPrevDest] at hRead
      obtain ⟨x, hx⟩ := causal_pv_cell half oldPart head col hpre hX hs hCut hOutput hLane
        hBlock hPrev hPrevState
      have hAcc : pvAccum block issue = true := by
        have hLarge : 2 ≤ issue.val := by dsimp [issue, pvHalfIssue]; omega
        simp [pvAccum, hLarge]
      exact ⟨x, hAcc ▸ .priorMma hRead hx⟩
  obtain ⟨prev, hPrev⟩ := hSeed
  obtain ⟨ops, hObserved⟩ := observed_operands_of_done hX hDone
  let row : Fin 128 := ⟨head.val + 64 * (col.val / 128), by have := head.isLt; omega⟩
  have hProb : PvCausalCut.Cut P L X consumer cut block := by
    have hBig := hCut.probabilities
    exact ⟨hBig.present, by have := hBig.blockLt; omega, by have := hBig.count; omega, hBig.prior⟩
  obtain ⟨weight, hA⟩ :=
    actual_pv_probability_finite hpre hX hs hProb hCut.cta hi hState rfl hObserved row
  have hB := pv_value_operand (d := ⟨.pvMma issue, block⟩) hpre hX hs hState rfl hi hObserved col
  let value := fun (slot feature : Nat) => dequant (Wg2.gatheredByte P L g block slot) feature
  have hPrev' : GemmAccumulator L X (g, i)
      ⟨ctaOf L g, row.val, pvDest issue + col.val % 128⟩ (pvAccum block issue) prev := by
    rw [hDest]
    exact hPrev
  have hVal := pv_chunk_result hX.tma.2.1 hi hObserved head col weight value hA hB hPrev'
  rw [hDest] at hVal
  exact ⟨_, hVal⟩
termination_by 4 * block + part.val
decreasing_by all_goals omega

/-- All registers of the selected PV block have FP32 results at this output guard. -/
theorem causal_pv_lane_results {g cut issuer block : Nat} {out : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hCut : PvOutputCut.Cut P L X g cut issuer block)
    (hOutput : Frame.stateAt (Machine.code P L) X g cut = some (some (.wg0 out))) :
    OutputTmemWords.PvLaneResults P L X g block := by
  intro t src c rank tile reg hCta hLane hState hi _ _
  have hIssuer := hmma t src _ hCta hState (by simp)
  subst t
  let head := OutputTmemReadSource.resultRow L g
  let half := OutputTmemReadSource.tileHalf tile
  let col := OutputTmemReadSource.resultColumn L g tile reg
  have hCell := OutputTmemReadSource.outputCell_eq_pv hpre hLane hCta tile reg
  have hLane' : head.val + 64 * (col.val / 128) = tidOf L g := by
    have hEq := congrArg TcMma.Cell.lane hCell
    rw [OutputTmemReadSource.outputCell_eq hpre hLane tile reg] at hEq
    exact hEq.symm
  rw [hCell]
  exact causal_pv_cell half 3 head col hpre hX hs hCut hOutput hLane' le_rfl hi hState

/-- The two output load guards preserve tracking using this launch's causal prefix. -/
theorem causal_output_wait_never_dismiss {g i : Nat} {d : Wg0.D} {e : Event} {tile : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .rescaleWait tile ∨ d.site = .oWait tile)
    (hPrior : ∀ w, baseCausality L X w (g, i) → ¬ MachineTracking.Dismisses P L X w) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  rcases hSite with hRescale | hOutput
  · refine OutputTmemWords.rescale_wait_never_dismiss hpre hX hs ?_ he hd hRescale
    intro issuer tag hmma hw
    exact causal_pv_lane_results hpre hX hs hmma
      (PvOutputCut.of_rescale_wait hpre hX hs hmma hd hRescale hw hPrior) hd
  · refine OutputTmemWords.final_wait_never_dismiss hpre hX hs ?_ he hd hOutput
    intro issuer tag hmma hw
    exact causal_pv_lane_results hpre hX hs hmma
      (PvOutputCut.of_output_wait hpre hX hs hmma hd hOutput hw hPrior) hd

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
