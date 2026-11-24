-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.NcReadOnly
import Lemmas.Flow.WarpUniform

public section

/-! # Guard, linear-copy and assumption safety checks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000 in
private theorem no_uniform_guards : kernel.noUniformGuards = true := by
  decide +kernel

/-- No frozen instruction compares a guard or a branch index between lanes. -/
theorem no_warpDivergent : ¬ WarpDivergent L kernel Assumptions.all X :=
  not_warpDivergent no_uniform_guards

/-- The linear-copy checks of TMA safety hold on every consistent execution. -/
theorem no_linear_copy_faults (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ CpAsyncOverlap X ∧ ¬ MaskedRangeUnalloc mem0 X :=
  ⟨not_cpAsyncOverlap_of_none (fun _ _ h => (GlobalWrites.no_copy hX h).elim),
   not_maskedRangeUnalloc_of_none (fun _ _ _ h => (GlobalWrites.no_copy hX h).elim)⟩

/-- All assumption-level safety checks hold, including the non-coherent input read footprints. -/
theorem no_assumption_ub (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ ∃ a ∈ Assumptions.all, a.ub L mem0 X := by
  rintro ⟨a, hm, hub⟩
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ncReadOnly_safe hpre hs hX ht hub | exact hub

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
