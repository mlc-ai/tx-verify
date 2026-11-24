-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemMmaValues
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Safety.QueryFiniteOperands
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyFiniteOperands
import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheOperandElements
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma PTX.AsyncCopy Thread
open Protocol.LoaderReady
open Mma (initialQkBlock recurringKeyBlock qkStage)

/-- The outstanding BF16 operand obligation is the recorded P input to completed PV. -/
def CompletedPvProbabilitiesAreBf16 (X : Execution) : Prop :=
  ∀ i cell block step d spec acc mask row col (ops : MmaOperands),
    PvInstruction X i block step d spec acc mask → X.async.mmaDone i = true →
    writeCell spec d mask row col = some cell → X.async.mmaOperands i = some ops →
    ∀ k < 16, ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x

/-- The observed Q, K, and V operands already have BF16 sources on every guarded
prefix. The remaining operand values for completed MMA are its packed probabilities. -/
theorem mmaOperandsOfProbabilities {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hProb : CompletedPvProbabilitiesAreBf16 X) :
    CompletedMmaOperandsAreBf16 X := by
  intro ⟨g,index⟩ cell d spec acc mask row col ops hIssue hDone hWrite hOps
  have ⟨hRows,hCols⟩ := resultCell_rowcol (writeCell_resultCell hWrite)
  rcases actualMmaInstruction hX hIssue with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · rw [(hQk.queryOperand hp hX).descriptor] at hRows hCols
    change row < 128 at hRows
    change col < 128 at hCols
    refine ⟨fun k hk => actualQkQueryElement hp hX hFrame hQk hOps hRows hk,?_⟩
    let stage := qkStage block
    intro k hk
    by_cases hInitial : block.val < 2
    · have hBlock : block = initialQkBlock stage := by
        apply Fin.ext
        change block.val = block.val%2
        omega
      have hOpening : QkInstruction X (g,index) (initialQkBlock stage) step d spec acc mask :=
        hBlock ▸ hQk
      exact primingKeyOperandFinite hp hX hFrame stage hOpening hCols hk hOps
    · have hBlock : block = recurringKeyBlock stage := by
        have hB := block.isLt
        apply Fin.ext
        change block.val = block.val%2+2
        omega
      have hRecurring : QkInstruction X (g,index) (recurringKeyBlock stage) step d spec acc mask :=
        hBlock ▸ hQk
      exact recurringKeyOperandElementInPrefix hp hX hFrame stage hRecurring hCols hk hOps
  · obtain ⟨_,_,hDescriptor,_⟩ := hPv.valueOperand hp hX
    rw [hDescriptor] at hCols
    change col < 128 at hCols
    exact ⟨hProb (g,index) cell block step d spec acc mask row col ops hPv hDone hWrite hOps,
      fun k hk => valueOperandElementInPrefix hp hX hFrame hPv hCols hk hOps⟩

end PTX.Kernels.TmlFa4Fwd.Safety
