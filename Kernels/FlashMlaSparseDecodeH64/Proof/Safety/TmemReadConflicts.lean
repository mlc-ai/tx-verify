-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MmaAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.QueryCellValues
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmResults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

/-! # Tensor-memory read conflicts, including in-flight MMA instructions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem accumulator_order {reader writer : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue reader d s acc mask)
    (hw : TcMma.WriteBefore L X reader writer) : TcMma.ReadBefore L X .acc reader writer := by
  rcases hw with h | h | h
  · rcases h with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · obtain ⟨_, _, _, _, hs⟩ := (TcMma.storeDoneBefore_iff.mp h).1
    cases congrArg Event.kind (Option.some.inj (hi.choose_spec.symm.trans hs))
  · obtain ⟨_, _, _, _, _, hc, _, _⟩ := h.2.2
    cases congrArg Event.kind (Option.some.inj (hi.choose_spec.symm.trans hc.choose_spec))

private theorem acc_conflict_ordered
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hWrites : TcMma.WritesSafe L X)
    {reader writer : EvId} {cell : TcMma.Cell} (hr : X.MmaReadCell reader cell)
    (hw : TcMma.TmemWrite L X writer cell) :
    reader = writer ∨ TcMma.WriteBefore L X writer reader ∨
      TcMma.ReadBefore L X .acc reader writer := by
  obtain ⟨g, i⟩ := reader
  obtain ⟨d, s, mask, row, col, hi, hcell⟩ := hr
  rcases MmaAccessWindow.mma_spec hpre hX hs ht hi with ⟨rfl,
    ⟨block, issue, rfl, rfl, _, _⟩ | ⟨block, issue, rfl, rfl, _, _⟩⟩
  all_goals
    have hc := writeCell_zeroMask rfl rfl (result_indices hcell).1
      (TcMma.resultCell_bounds hcell).1 hcell
    have hresult := hWrites (g, i) writer cell (.inl ⟨_, _, _, _, _, _, hi, hc⟩) hw
    rcases hresult with h | h | h
    · exact .inl h
    · exact .inr (.inr (accumulator_order hi h))
    · exact .inr (.inl h)

/-- All represented competing TMEM reads and writes are ordered, even before completion. -/
theorem no_tmem_reads_unsafe
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ TcMma.ReadsUnsafe L X := by
  intro hunsafe
  apply hunsafe
  have hWrites : TcMma.WritesSafe L X := Classical.not_not.mp (no_tmem_writes_unsafe hpre hX hs ht)
  apply TcMma.readsSafe_iff.mpr
  refine ⟨fun _ _ _ hr hw => acc_conflict_ordered hpre hX hs ht hWrites hr hw, ?_, ?_⟩
  · intro reader writer cell hr hw
    obtain ⟨src, _, hsource, _, hunique⟩ := mma_a_unique_source hpre hX hs ht hr
    exact .inr (.inl (hunique writer hw ▸ hsource.2.2.1))
  · rintro ⟨g, i⟩ _ _ ⟨s, hi, _⟩ _
    exact (Wg0ScoreSources.no_shift_issue hpre hX hs ht (g := g) (i := i) (s := s) hi).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
