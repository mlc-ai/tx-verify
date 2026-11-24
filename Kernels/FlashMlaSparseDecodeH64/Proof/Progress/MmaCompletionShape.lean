-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MmaShapes
public import Lemmas.Step.MmaDrainTmemA
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Tcgen05.TcMmaResultLayout

public section

/-! # The layouts of MMA operands and results used in completion steps -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow TcMma Wg1Mma MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem result_coordinates {s : OperandSpec} {d row col : Nat} {cell : Cell}
    (h : resultCell s d row col = some cell) : row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold resultCell at h
  dsimp only at h
  split at h
  · rename_i hValid
    exact ⟨hValid.2.2.1, hValid.2.2.2.1⟩
  · cases h

/-- Every actual MMA writes an injective layout with two datapath lanes per head. -/
theorem mma_layout_injective (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    LayoutInjective X := by
  intro i d s acc mask hi row col row' col' cell h h'
  have h1 := writeCell_resultCell h
  have h2 := writeCell_resultCell h'
  have ⟨hr, hc⟩ := result_coordinates h1
  have ⟨hr', hc'⟩ := result_coordinates h2
  obtain ⟨g, i⟩ := i
  rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
    ⟨block, k, rfl, rfl, _, _⟩ | ⟨block, k, rfl, rfl, _, _⟩
  · rw [qkResultCell L g block k ⟨row, hr⟩ ⟨col, hc⟩] at h1
    rw [qkResultCell L g block k ⟨row', hr'⟩ ⟨col', hc'⟩] at h2
    obtain ⟨_, hlane, hcol⟩ := Cell.mk.inj (Option.some.inj (h1.trans h2.symm))
    dsimp only at hlane hcol
    change row < 64 at hr
    change row' < 64 at hr'
    omega
  · rw [pvResultCell L g block k ⟨row, hr⟩ ⟨col, hc⟩] at h1
    rw [pvResultCell L g block k ⟨row', hr'⟩ ⟨col', hc'⟩] at h2
    obtain ⟨_, hlane, hcol⟩ := Cell.mk.inj (Option.some.inj (h1.trans h2.symm))
    dsimp only at hlane hcol
    change row < 64 at hr
    change row' < 64 at hr'
    omega

/-- QK reads the query columns, below its accumulator. PV reads both operands from shared. -/
theorem mma_tmem_a_apart (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ATmemApart X := by
  intro j d s acc mask hj index cell pos ha w d' s' acc' mask' row col hw hSame hWrite
  obtain ⟨g, j⟩ := j
  rcases (MmaAccessWindow.mma_spec hpre hX hs ht hj).2 with
    ⟨block, issue, rfl, rfl, _, _⟩ | ⟨block, issue, _, rfl, _, _⟩
  · have hBound := TcMma.aCell_index_lt ha
    norm_num [qkOperands, qkDescriptor, Operand.bytes, Operand.rows, Kind.k, Kind.width] at hBound
    obtain ⟨r, k, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hBound
    rw [qkQueryByte L g block issue r k b] at ha
    have hRead := congrArg (fun p : Cell × Nat => p.1.column) (Option.some.inj ha)
    change qkACol issue + k.val / 2 = cell.column at hRead
    have hACol : cell.column < tmemP := by
      simp only [qkACol, tmemQ, tmemP] at hRead ⊢
      have := issue.isLt
      have := k.isLt
      omega
    have hResult := writeCell_resultCell hWrite
    have ⟨hr, hc⟩ := result_coordinates hResult
    have hDest : d' = tmemP := hSame.1
    obtain ⟨g', j'⟩ := w
    rcases (MmaAccessWindow.mma_spec hpre hX hs ht hw).2 with
      ⟨block', issue', rfl, rfl, _, _⟩ | ⟨block', issue', rfl, rfl, _, _⟩
    · rw [qkResultCell L g' block' issue' ⟨row, hr⟩ ⟨col, hc⟩] at hResult
      cases hResult
      exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) hACol
    · rw [pvResultCell L g' block' issue' ⟨row, hr⟩ ⟨col, hc⟩, hDest] at hResult
      cases hResult
      exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) hACol
  · simp [TcMma.aCell, pvOperands] at ha

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
