-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RegionSlice
public import Lemmas.Flow.SegJump
public import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Base

/-! # Frame regions on a code slice; an unconditional branch as a piece

`regionB_of_S`: the frame check of a range of tml-fa4's code (pcs 4352–4397, ending at a
`bar.arrive`, which write no register `0`) decided on the slice `(code.drop lo).take …` in one pass.
`seg_jmp`: the unconditional `bra.uni 517` at pc 519 as one step that keeps the facts. -/

namespace PTX.Tests.RegionSlice
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd

example : regionB Decoded.kernel 4352 4397 [0] = true :=
  regionB_of_S (by decide +kernel)

example (L : Launch) (g : Nat) (F : List (Nat × Value)) :
    Seg Decoded.kernel Assumptions.all L g 1 519 F 517 F :=
  seg_jmp Flow.code_519
    (fun t _ a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (Proof2.Epilogue.segFree (by decide))

end PTX.Tests.RegionSlice
