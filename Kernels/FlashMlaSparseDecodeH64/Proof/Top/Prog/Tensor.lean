-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Guard
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Lemmas.Quiet.Progress.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorSrc

@[expose] public section

/-! # Progress class: the tensor loads

An issued tensor load steps (`Sched.tensor_stepsQ`) when its sources are fixed
(`TensorSources`): every load is routed with a valid nonempty descriptor (`tensorLoadForm`, a
scan of the code), and each global byte of its box is an initialized byte of the query or of a
cache that no write covers (`load_source`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The tensor loads' sources are fixed** in a consistent followed execution. -/
theorem Prog.tensorSources (hp : Pre P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    TensorSources L m X := by
  intro i a s hi
  obtain ⟨hr, hv, hb⟩ := tensorLoadForm hX hi
  refine ⟨hr, hv, hb, fun _ _ hs => ?_⟩
  obtain ⟨⟨v, hv'⟩, hw⟩ := load_source hp hX hFw hnu hi hs
  exact ⟨v, hv', hw⟩

/-- **An open tensor-load obligation steps.** -/
theorem Prog.tensor (hp : Pre P L m) : Prog.AsyncSteps P L m [.tensor] := by
  intro hs X hmax hFw o ho hob
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  exact Sched.tensor_stepsQ wfQuiet_all hmax
    (Prog.tensorSources hp hmax.1 hFw (Sched.safe_noUb (hs.2 X hmax.1))) hob

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
