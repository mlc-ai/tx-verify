-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Kernel.Goals
import Kernels.TmlFa4Fwd.Proof.Bound.Assembly
import Kernels.TmlFa4Fwd.Proof.Top.Assembly
import Kernels.TmlFa4Fwd.Proof.Top.Result.Lse
import Kernels.TmlFa4Fwd.Proof.Top.Result.Output
import Kernels.TmlFa4Fwd.Proof.Top.Safety

@[expose] public section

/-! # The kernel is correct

`correct2`: the four goals of `Correct` from the tree, for every launch that satisfies `Pre`:

* safety: `Top.safe` (`Top/Safety.lean`), one file per class of `Unsafe` (`Top/Safe/<Class>.lean`);
* progress: `Top.progress` (`Top/Assembly.lean`), the ranked descent given safety, one file per
  progress class (`Top/Prog/<Class>.lean`);
* bound: `Bound.terminates` (`Bound/Assembly.lean`);
* result: the stored output and log-sum-exp values of a complete execution
  (`Top/Result/Output.lean`, `Top/Result/Lse.lean`); `Values.post_of_values` turns them into `Post`.

`Pre` is its only hypothesis (`Tools/premise_count.py`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX

variable {p : Params} {l : Launch} {m : Mem0}

/-- **The kernel is correct**: every class of `Unsafe`, the progress, the termination and the stored
values are proved for every launch that satisfies `Pre`. -/
theorem correct2 (hp : Pre p l m) : Correct kernel Assumptions.all l m (Post p m) :=
  correct_of (safe hp) (progress hp) (Bound.terminates hp) fun _ _ hX hDone hFinal =>
    Values.post_of_values hp hX (launchFollow hp hX) hDone hFinal (Res.output hp hX hDone)
      (Res.lse hp hX hDone)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
