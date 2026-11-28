-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Bound
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.Output
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Lemmas.Kernel.Goals
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Assembly
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safety
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemRest

@[expose] public section

/-! # The kernel is correct, from the precondition

The four goals of `Correct` (`correct_of`, `Lemmas/Kernel/Goals.lean`):

* safety: `safe` (`Top/Safety.lean`), one file per class of `Unsafe` (`Top/Safe/<Class>.lean`);
* progress: `progress` (`Top/Assembly.lean`), given safety (`Top/Prog/`);
* bound: `Bound.terminates` (`Top/Bound.lean`);
* result: the four conjuncts of the Spec's `Post` for a complete execution, the output values and
  the frame (`Top/Result/Output.lean`) and the log-sum-exp values (`Top/Result/Lse.lean`).

`correct` takes `Pre` alone: no premise is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The kernel is correct**, from the precondition. -/
theorem correct (hp : Pre P L mem0) :
    Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  correct_of (safe hp) (progress hp) (Bound.terminates hp (follow_of hp))
    fun X mf hX hC hF => by
      have hFw := follow_of hp X hX
      obtain ⟨hO, hFrame⟩ := Res.output hp (Safe.w0TraceValid hp) hX hFw
        (Safe.noUb hp hX hFw) hC hF
      obtain ⟨hL, hE⟩ := Res.lse hp (Safe.w0TraceValid hp) hX hFw
        (Safe.noUb hp hX hFw) hC hF
      exact ⟨hO, hL, hE, hFrame⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
