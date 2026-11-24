-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords

@[expose] public section

/-!
# `Out.Inputs.mmaWords` from the two reads-from facts

`Result.Mma.MmaWords` (the MMA warp's loop bound is the split's `num_iters`, its Tensor Memory base
is column 0) from the thread layer's `Interface.mma_iters_loop` and `Interface.mma_tm`, which take
the two reads-from facts of the words as premises (`BaseWordRead`: a four-byte read of the base word
returns the 32-bit zero, `SO.BaseWordZero`; `NumWordRead`: a four-byte read of the `num_iters` word
returns the 32-bit `num_iters` of the reading thread's CTA). Another session proves those two.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Out.Inputs.mmaWords`**, given the reads-from facts of the base word and of the `num_iters`
word. -/
theorem mmaWords_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : Interface.ThreadFacts Q L mem0 X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X) : MmaWords Q L X where
  iters := fun _ h hs => Interface.mma_iters_loop hpre hX hf hb hn h hs
  tm := fun h => Interface.mma_tm hpre hX hf hb hn h

end
end PTX.Kernels.InklingRelDecode.Proof.Rs
