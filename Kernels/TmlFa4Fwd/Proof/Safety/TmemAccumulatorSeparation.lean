-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadGeometry
public import Lemmas.Tcgen05.MmaFinishTmemA
import Lemmas.Tcgen05.TcMmaResultLayout
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma

/-- All MMA issues use one of the two valid decoded instruction shapes. -/
theorem actualMmaDescriptorValid {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) : Valid s.descriptor := by
  rcases actualMmaInstruction hX hi with ⟨_, _, hQk⟩ | ⟨_, _, hPv⟩
  · rw [(hQk.queryOperand hp hX).descriptor]
    decide
  · obtain ⟨_, _, hDescriptor, _, _⟩ := hPv.valueOperand hp hX
    rw [hDescriptor]
    decide

/-- The MMA that reads a probability cell accumulates in the output tile.
Any MMA sharing its accumulator writes in the upper half of Tensor Memory. -/
theorem mmaATmemApart {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) : ATmemApart X := by
  intro j d s acc mask hi index cell byte ha w dw sw accw maskw row col hw hs hWrite
  obtain ⟨stage, hRead, _, hCol⟩ := mmaAProbabilityTile hp hX ⟨_, _, _, _, _, _, hi, ha⟩
  have hLow : cell.column < 256 := by
    rw [probabilityColumn_range] at hCol
    exact hCol.trans_le (scoreColumn_range stage)
  obtain ⟨block, _, d', s', a', mask', _, _, _, hv, _⟩ := hRead
  obtain ⟨rfl, rfl, _, _⟩ := mmaIssue_params (show X.MmaIssue j d' s' a' mask' from
    ⟨_, hv.decoded⟩) hi
  have hDst := hv.outputDestination hp hX
  rcases actualMmaInstruction hX hw with ⟨k, _, hQk⟩ | ⟨k, _, hPv⟩
  · have hScore := hQk.scoreDestination hp hX
    have hRange := score_output_apart (qkStage k) (pvSite block).stage
    have hEq := hs.1
    omega
  · obtain ⟨_, _, hDescriptor, _, _⟩ := hPv.valueOperand hp hX
    have hCell := writeCell_resultCell hWrite
    have hWriteDest := hPv.outputDestination hp hX
    unfold resultCell at hCell
    rw [hDescriptor, hWriteDest] at hCell
    dsimp only at hCell
    split at hCell
    · have hFull : pvDescriptor.m = 128 * pvDescriptor.group.size := rfl
      simp only [hFull, ↓reduceIte, Option.some.injEq] at hCell
      have hLimit := outputColumn_range (pvSite k).stage
      rw [Nat.mod_eq_of_lt (show outputColumn (pvSite k).stage < 2 ^ 16 by omega)] at hCell
      subst cell
      simp only [outputColumn] at hLow
      omega
    · cases hCell

end PTX.Kernels.TmlFa4Fwd.Safety
