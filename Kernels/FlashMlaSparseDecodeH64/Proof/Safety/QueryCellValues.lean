-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QueryCopyPayload
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQueryValues
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCellWriters
import Lemmas.Tcgen05.TcMmaAReadUnique

@[expose] public section

/-! # Tensor Memory A reads have their actual copied query values -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Protocol Result MmaDataTrace Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000

/-- Every Tensor Memory A read has a unique query-copy writer and its value. -/
theorem mma_a_unique_source (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {cell : TcMma.Cell} (hRead : X.MmaACell i cell) :
    ∃ src value, TcMma.ReadSource L X .a src i cell ∧
      TcMma.Wrote L Assumptions.all X src cell value ∧
      (∀ other, TcMma.TmemWrite L X other cell → other = src) := by
  obtain ⟨g, j⟩ := i
  obtain ⟨d, s, acc, mask, index, b, hi, hCell⟩ := hRead
  rcases MmaAccessWindow.mma_spec hpre hX hs ht hi with ⟨rfl,
    ⟨block, issue, rfl, rfl, rfl, hState⟩ | ⟨block, issue, rfl, rfl, rfl, hState⟩⟩
  · have hBound := TcMma.aCell_index_lt hCell
    norm_num [qkOperands, qkDescriptor, TcMma.Operand.bytes, TcMma.Operand.rows,
      TcMma.Kind.k, TcMma.Kind.width] at hBound
    obtain ⟨row, k, byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hBound
    have hMatch := (Prod.mk.inj (Option.some.inj
      (hCell.symm.trans (qkQueryByte L g block issue row k byte)))).1
    obtain ⟨i, e, q, u, he, hq, hSite, hFire, hCopy, hDone, hSource⟩ :=
      QueryOperandLifetime.query_copy_read_source hpre hX hs hi hState rfl
    obtain ⟨ops, hOps⟩ := observed_operands_of_done hX hDone
    have hv := query_copy_payload hpre hX hs he hq hSite hFire hOps row
    let w : Fin 8 := ⟨k.val / 2, by have := k.isLt; omega⟩
    obtain ⟨v, hValue⟩ := exists_query_copy_cell_value hCopy hOps hv w
    rw [hMatch]
    exact ⟨(g, i), v, hSource row k, .inr (.inr (.inl hValue)),
      fun _ hw => QueryCellWriters.unique_writer hpre hX hs he hq hSite row k hw⟩
  · simp [TcMma.aCell, pvOperands] at hCell

/-- The only Tensor Memory A reads are QK reads of query-copy words. -/
theorem mma_a_source (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {cell : TcMma.Cell} (hRead : X.MmaACell i cell) :
    ∃ src value, TcMma.ReadSource L X .a src i cell ∧
      TcMma.Wrote L Assumptions.all X src cell value := by
  obtain ⟨src, v, hread, hvalue, _⟩ := mma_a_unique_source hpre hX hs ht hRead
  exact ⟨src, v, hread, hvalue⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
