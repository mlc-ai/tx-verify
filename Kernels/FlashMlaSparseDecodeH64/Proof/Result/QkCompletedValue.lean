-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QkAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkIssueHistory
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # A completed QK issue has actual values even before its commit is issued -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow MmaDataTrace Protocol
open Wg1Mma (tmemP)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem qk_done_before {g j i block : Nat} {earlier issue : Fin 16}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hOld : X.MmaIssue (g, j) tmemP (qkOperands L g block earlier) (qkAccum earlier) [0, 0, 0, 0])
    (hi : X.MmaIssue (g, i) tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hLt : j < i) (hDone : X.async.mmaDone (g, i) = true) :
    X.async.mmaDone (g, j) = true := by
  apply hX.mmaCompletion (g, j) (g, i) _ hDone
  have hg := Frame.lt_of_get hX hOld.choose_spec
  refine ⟨rfl, hLt, ?_, ?_⟩
  · exact ⟨TcMma.sameWarp_self hg,
      .inl (TcMma.baseCausality_of_tc_po hOld.choose_spec rfl hLt (PTX.len_of_get hi.choose_spec)),
      _, _, _, _, _, _, _, _, hOld, hi, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, _, _, _, _, _, _, _, hOld, hi, fun _ _ => rfl, _, _, _,
      qkWriteCell L g block earlier 0 0⟩

/-- A completed QK cell has both its actual accumulator source and its result. -/
theorem qk_completed_cell {g i block : Nat} (issue : Fin 16) (head : Fin 64) (col : Fin 128)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma issue, block⟩)))
    (hDone : X.async.mmaDone (g, i) = true) :
    (∃ prev, GemmAccumulator L X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
      (qkAccum issue) prev) ∧
    ∃ x : ℝ, TcMma.Result L Assumptions.all X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ (.float .f32 x) := by
  let cell : TcMma.Cell := ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
  have hSeed : ∃ x, GemmAccumulator L X (g, i) cell (qkAccum issue) x := by
    by_cases hZero : issue.val = 0
    · have hAcc : qkAccum issue = false := by simp [qkAccum, hZero]
      exact ⟨0, hAcc ▸ .overwrite⟩
    · let prior : Fin 16 := ⟨issue.val - 1, by have := issue.isLt; omega⟩
      have hLt : prior.val < issue.val := by dsimp only [prior]; omega
      have hK : prior.val + 1 < 16 := by dsimp only [prior]; have := issue.isLt; omega
      have hEq : (⟨prior.val + 1, hK⟩ : Fin 16) = issue := Fin.ext (by dsimp [prior]; omega)
      obtain ⟨j, hDist, hPriorState, hPrior⟩ :=
        QkIssueHistory.qk_issue_before hpre hX hs hi.choose_spec hState prior hLt
      have hIdx : j + 1 = i := by dsimp [prior] at hDist; omega
      have hEarlier := qk_done_before hX hPrior hi (by omega) hDone
      obtain ⟨x, hx⟩ :=
        (qk_completed_cell prior head col hpre hX hs hPrior hPriorState hEarlier).2
      have hIso : (⟨prior.val, by omega⟩ : Fin 16) = prior := Fin.ext rfl
      have hPrior' : X.MmaIssue (g, j) tmemP (qkOperands L g block ⟨prior.val, by omega⟩)
          (qkAccum ⟨prior.val, by omega⟩) [0, 0, 0, 0] := by simpa only [hIso] using hPrior
      have hRead := QkAccumulatorSource.previous_of_adjacent (k := prior.val) hK hpre hX hs
        hPrior' (by rwa [hEq, hIdx]) (by rwa [hEq, hIdx]) head col
      have hAcc : qkAccum issue = true := by simp [qkAccum, hZero]
      rw [hIdx] at hRead
      exact ⟨x, hAcc ▸ .priorMma hRead hx⟩
  refine ⟨hSeed, ?_⟩
  obtain ⟨prev, hPrev⟩ := hSeed
  obtain ⟨ops, hObs⟩ := observed_operands_of_done hX hDone
  have hA := qk_query_operand hpre hX hs hi hState rfl hObs head col
  have hB := qk_key_operand hpre hX hs hState rfl hi hObs col
  exact ⟨_, qk_chunk_result hX.tma.2.1 hi hObs head col _ hA hB hPrev⟩
termination_by issue.val
decreasing_by exact hLt

/-- The actual QK accumulator and operands determine the finite result of each completed chunk. -/
theorem qk_completed_value {g i block : Nat} (issue : Fin 16) (head : Fin 64) (col : Fin 128)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma issue, block⟩)))
    (hDone : X.async.mmaDone (g, i) = true) :
    ∃ x : ℝ, TcMma.Result L Assumptions.all X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ (.float .f32 x) :=
  (qk_completed_cell issue head col hpre hX hs hi hState hDone).2

/-- The model's completed-value obligation holds for each actual QK issue. -/
theorem qk_completed_values {g i block : Nat} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma issue, block⟩))) :
    TcMma.CompletedValues L Assumptions.all X (g, i) := by
  intro hDone cell hCell
  obtain ⟨_, _, _, _, row, col, hIssue, hWrite⟩ := hCell
  have hKind := congrArg Event.kind (Option.some.inj (hIssue.choose_spec.symm.trans hi.choose_spec))
  obtain ⟨rfl, rfl, rfl, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hKind)
  have hGeometry := TcMma.writeCell_resultCell hWrite
  have hBound : row < 64 ∧ col < 128 := by
    unfold TcMma.resultCell at hGeometry
    dsimp only at hGeometry
    split at hGeometry
    · rename_i h
      exact ⟨h.2.2.1, h.2.2.2.1⟩
    · cases hGeometry
  let head : Fin 64 := ⟨row, hBound.1⟩
  let channel : Fin 128 := ⟨col, hBound.2⟩
  have hEq := Option.some.inj (hWrite.symm.trans (qkWriteCell L g block issue head channel))
  obtain ⟨x, hx⟩ := qk_completed_value issue head channel hpre hX hs hi hState hDone
  exact ⟨.float .f32 x, hEq ▸ hx⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
