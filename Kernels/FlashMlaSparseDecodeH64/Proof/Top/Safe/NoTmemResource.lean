-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Lemmas.Tmem.Tmem1Protocol
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.AllocRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Lemmas.Kernel.Safety.TmemAlloc

@[expose] public section

/-! # ERR-TMEM-RESOURCE: Tensor Memory allocations are valid

The safety class of Core's `Unsafe` this file owns (`Tmem.Pair.ResourceUnsafe`), by the library's
`cta_group::1` protocol (`Frame.tmem1_safe`, `Lemmas/Tmem/Tmem1Protocol.lean`): warp 0 of each
CTA makes every paired Tensor Memory operation, in group 1, its `n`-th of shape `n` (allocation
of 512 columns, relinquishment, deallocation of 512), the deallocation frees column 0, and a lane
of warp 0 exits after its three (`Safe.tmemOne`). Which operations there are and where is the
rows' (`tmem_res`); the counts and the deallocation's request are the roles' exports
(`startup_tmemShape` through `tmemOps_warp0`, `wg0_deallocOps`, `wg0_exitOps`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The `cta_group::1` facts of warp 0**, from the rows and the inputs. -/
theorem Safe.tmemOne (hp : Pre P L mem0) (_hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    Tmem.One.Tmem1Facts L X 0 := by
  have hR := tmem_rows hp hX hFw
  refine { toTmem1Ops := tmemOps_warp0 hp hX hFw, dealloc := ?_, exit := ?_ }
  · intro g k pc grp dst a n hg he
    obtain ⟨rfl, ⟨-, -, h | h⟩ | ⟨hA, -⟩⟩ := tmem_res hR hg he rfl
    · cases h
    · cases h
    · obtain ⟨-, h, -⟩ := wg0_deallocOps hp hX hFw he hA rfl
      cases h
      rfl
  · intro g k pc hg hgw he
    exact wg0_exitOps hp hX hFw he ((warp0_iff hp).2 hgw)

/-- **ERR-TMEM-RESOURCE**: Tensor Memory allocations are valid. -/
theorem Safe.noTmemResource (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ Tmem.Pair.ResourceUnsafe L X :=
  (Frame.tmem1_safe hX (Safe.tmemOne hp hIn hX hFw)).1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
