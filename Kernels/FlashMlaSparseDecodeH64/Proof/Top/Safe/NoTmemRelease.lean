-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
import Lemmas.Kernel.Safety.TmemAlloc

@[expose] public section

/-! # ERR-TMEM-NOT-RELEASED: Tensor Memory is released

The safety class of Core's `Unsafe` this file owns (`Tmem.Pair.ReleaseUnsafe`), by the library's
`cta_group::1` protocol (`Frame.tmem1_safe`) from the facts of warp 0 (`Safe.tmemOne`): once
every lane has exited, warp 0 has made its three operations, and the deallocation of its
allocation leaves the allocator empty. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-TMEM-NOT-RELEASED**: Tensor Memory is released. -/
theorem Safe.noTmemRelease (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ Tmem.Pair.ReleaseUnsafe L X :=
  (Frame.tmem1_safe hX (Safe.tmemOne hp hIn hX hFw)).2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
