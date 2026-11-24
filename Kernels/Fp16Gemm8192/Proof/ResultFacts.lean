-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.TcLoadFacts
public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryAccess
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.TaskCover
public import Kernels.Fp16Gemm8192.Proof.Result.Writes
public import Kernels.Fp16Gemm8192.Proof.Result.Final

@[expose] public section

/-! # The write structure of `ResultGoal`

In a complete execution every byte of `D` has exactly one writer, a consumer's TMA store slot
(`output_writes_of`): from the thread facts (`threadFacts`), the CLC responses (`readerValues`,
`allResponsesAgree`), the global writes (`Safety.Memory.global_writes`), the tiles' coverage
(`ClcRing.outputCover`, without undefined behaviour by `no_ub`) and their distinct slots
(`ClcRing.outputUnique`). With the values those slots write (`OutputValues`), the final memory is
the specified output (`result_goal_of`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof
noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every output byte has exactly one writer** in a complete execution. -/
theorem output_writes_of (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hd : Complete L X) : OutputWrites P L X := by
  have ht := threadFacts hpre hX
  have hrw := Region.responseWriters hpre hX ht
  have hv := ClcRing.readerValues hpre hX ht hrw
  have hag := ClcRing.allResponsesAgree hpre hX ht hrw
  exact Result.output_writes hX hd (ClcRing.outputCover hpre hX ht hv hag hd (no_ub hpre hX))
    (ClcRing.outputUnique hpre hX ht hv) (Safety.Memory.global_writes hpre hX ht)

/-- **`ResultGoal` from the output values**: a complete execution whose TMA store slots write their
elements' dot products leaves the specified output. -/
theorem result_goal_of (hpre : Pre P L mem0)
    (hval : ∀ X, Consistent L kernel Prod mem0 X → Complete L X → OutputValues P L X) :
    ResultGoal kernel Prod L mem0 (Post P mem0) := fun X _ hX hd hf =>
  Result.post_of (Safety.Memory.global_writes hpre hX (threadFacts hpre hX))
    (output_writes_of hpre hX hd) (hval X hX hd) hf

end
end PTX.Kernels.Fp16Gemm8192.Proof
