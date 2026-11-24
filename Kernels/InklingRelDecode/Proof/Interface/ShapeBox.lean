-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeLoaderPage
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Safety.Tensor
public import Kernels.InklingRelDecode.Proof.Thread.ShapeCopyEvent
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Safety.Tensor
public import Kernels.InklingRelDecode.Proof.Thread.ShapeCopyEvent
public import Kernels.InklingRelDecode.Proof.Result.MmaCopy

@[expose] public section

/-!
# Every tensor copy's box is inside the map

`Safety.BoxInBounds`. A K/V copy of a block that exists has the origin
`(kvh · head_cols + 128 isV + 64 hh, page · page_rows + kvh · head_rows)`, and a box at that origin
is inside the map (`Result.Mma.kv_noOob` with `Pre.kvCols`, `Pre.slabInside`): `kvbox_noOob`.

The loader's copies have that origin by `loader_copy_page` and `Result.Mma.loader_copy_spec`. The
prologue's copies have it by `ptc_kvspec`, given `ProCopyPage`: at a copy site of block `i / 4`
the block exists and the loaded block-table word of the copy's slab is its page (an open row of
"thread-layer gaps": the prologue's block-table load addresses and the guards that skip an absent
block).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The prologue's copies copy pages that exist.** At a prologue state at copy site `i` of the
thread's CTA, the block `i / 4` is below `num_iters` and the loaded block-table word of the copy's
slab is the page of the slab. -/
def ProCopyPage (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : ProA.D} {i : Nat}, St Q L X g k = some (some (.d (.pro d))) → i < 12 →
    d.site = ProA.ptcSite i →
    i / 4 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      ProA.btW d.dt (2 * (i / 4) + i % 4 / 2) =
        Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + i / 4 * Q.splits) + i % 4 / 2)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
