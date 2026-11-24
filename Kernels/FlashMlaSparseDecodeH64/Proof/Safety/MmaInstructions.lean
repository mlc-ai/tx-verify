-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MmaShapes
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvCompletedValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QkCompletedValue

@[expose] public section

/-! # Every issued Tensor Core instruction meets the instruction safety checks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

/-- Valid shapes, completed values, copy encodings and collector usage cover all actual issues. -/
theorem no_mma_instruction_unsafe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ TcMma.InstructionUnsafe L Assumptions.all X := by
  intro hUnsafe
  refine hUnsafe ⟨?_, fun _ _ hi => copy_issue_shape hpre hX hs ht hi,
    collector_safe hpre hX hs ht⟩
  rintro ⟨g, i⟩ d s acc mask hi
  refine ⟨mma_issue_shape hpre hX hs ht hi, ?_⟩
  rcases MmaAccessWindow.mma_spec hpre hX hs ht hi with ⟨rfl,
    ⟨block, issue, rfl, rfl, rfl, hState⟩ | ⟨block, issue, rfl, rfl, rfl, hState⟩⟩
  · exact Result.qk_completed_values hpre hX hs hi hState
  · exact Result.pv_completed_values hpre hX hs ht hi hState

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
