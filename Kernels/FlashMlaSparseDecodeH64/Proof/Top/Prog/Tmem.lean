-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Lemmas.Quiet.Progress.TmemOne

@[expose] public section

/-! # Progress class: the Tensor Memory's release

Warp 0 of each CTA makes every paired Tensor Memory operation, in group 1 (`Safe.tmemOne`, the
`cta_group::1` facts of safety), so the library's `Sched.tmem_one_stepsQ` steps an open `.tmem`
obligation: the launch's cluster grid is valid (`Pre.launchValid`), safety excludes
ERR-ALIGNED-MISMATCH, and the assumptions' constraints survive the quiet extension
(`wfQuiet_all`). Inputs: `Top.Inputs` (`tmemStartup`, `tmemWg0`, through `Safe.tmemOne`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **An open Tensor Memory obligation steps.** -/
theorem Prog.tmem (hp : Pre P L m) (hIn : Top.Inputs P L m) :
    Prog.AsyncSteps P L m [.tmem] := by
  intro hs X hmax hFw o ho hob
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  exact Sched.tmem_one_stepsQ wfQuiet_all hmax (Safe.tmemOne hp hIn hmax.1 hFw).toTmem1Ops
    hp.launchValid.1 (fun h => hs.2 X hmax.1 (by simp [Unsafe, h])) hob

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
