-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmFloat

@[expose] public section

/-! # The softmax region's setup between the barrier and the first bias load

The straight-line code of pcs 576 to 679, cut into pieces at pcs where every live register is
valued by the table, each piece from the table's facts at its first pc to the table's facts at its
last. The pieces compose by `Seg.comp` into `seg_setupA`, from the state after the second
`barrier.sync 1` (pc 575) to the first preload (pc 680).

The pieces of the bias row pointer (pcs 602 to 615) are single instructions: each stage is a
residue, kept folded (`p258 …`) so that the products of the chain stay atoms of `omega`, and
the bound of the stage it reads is given as a hypothesis. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-- The thread's row, its token, the row-valid mask and the half of the row (pcs 576 to 586). -/
theorem seg_576 (d : D) (hT : g % L.block < 128) (hq : d.e.qlen < 2 ^ 31) :
    Seg kernel asms L g 11 576 (factsAt L g 576 d) 587 (factsAt L g 587 d) := by
  intro t h
  sm_seg h

/-- The halves, the head and the group's registers (pcs 587 to 597). -/
theorem seg_587 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 11 587 (factsAt L g 587 d) 598 (factsAt L g 598 d) := by
  intro t h
  sm_seg h

/-- The token and the constant `1.0` (pcs 598 and 599). -/
theorem seg_598 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 2 598 (factsAt L g 598 d) 600 (factsAt L g 600 d) := by
  intro t h
  sm_seg h

/-- `%rd258 = %r342 * %r66` (`mul.wide.s32`). -/
theorem seg_602 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 602 (factsAt L g 602 d) 603 (factsAt L g 603 d) := by
  intro t h
  sm_seg h [sxw, p258]

/-- `%rd259 = %rd258 << 1`. -/
theorem seg_603 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 603 (factsAt L g 603 d) 604 (factsAt L g 604 d) := by
  intro t h
  sm_seg h [p259]

/-- `%rd260 = %rd71 + %rd259`. -/
theorem seg_604 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 604 (factsAt L g 604 d) 605 (factsAt L g 605 d) := by
  intro t h
  sm_seg h [p260]

/-- `%r345 = %r36 * 1280`. -/
theorem seg_605 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 605 (factsAt L g 605 d) 606 (factsAt L g 606 d) := by
  intro t h
  sm_seg h [r345]

/-- `%rd261 = %r345 * 2 + %rd260` (`mad.wide.u32`). -/
theorem seg_606 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 606 (factsAt L g 606 d) 607 (factsAt L g 607 d) := by
  have := p260_lt d.e (g % L.block)
  have := r345_lt d.e (g % L.block)
  intro t h
  sm_seg h [p261, reduceCtorEq]

/-- `%r346 = 1280 - %r24`. -/
theorem seg_607 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 607 (factsAt L g 607 d) 608 (factsAt L g 608 d) := by
  intro t h
  sm_seg h [r346]

/-- `%rd262 = %r346 * 2 + %rd261` (`mad.wide.s32`). -/
theorem seg_608 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 608 (factsAt L g 608 d) 609 (factsAt L g 609 d) := by
  intro t h
  sm_seg h [sxw, p262]

/-- `%rd8 = %r337` (`cvt.u64.u32`). -/
theorem seg_609 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 609 (factsAt L g 609 d) 610 (factsAt L g 610 d) := by
  intro t h
  sm_seg h

/-- `%rd9 = %r337 * 2 + %rd262` (`mad.wide.u32`): the bias row pointer. -/
theorem seg_610 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 610 (factsAt L g 610 d) 611 (factsAt L g 611 d) := by
  intro t h
  sm_seg h [p9, reduceCtorEq]

/-- The preload's mask `%p85 = (num_iters > 0) ∧ row_valid ∧ (n_first ≥ n_bias)` (pcs 611 to
614). -/
theorem seg_611 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) :
    Seg kernel asms L g 4 611 (factsAt L g 611 d) 615 (factsAt L g 615 d) := by
  have := hok.split
  have := hok.nbias
  have := hok.r25
  have := hok.qlen
  intro t h
  sm_seg h [act0]

/-- `%rd193 = %r1451 * 2 + %rd9`, the first bias pointer (`mad.wide.s32`). -/
theorem seg_615 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 1 615 (factsAt L g 615 d) 616 (factsAt L g 616 d) := by
  have := p9_lt d.e (g % L.block)
  have := key_lt d.n
  intro t h
  sm_seg h [Nat.reduceMul, ofInt_two, madwide_s32, ptrAt, sxw_two, sxw]

/-- The first 19 bias pointers (`%rd194 …`, pcs 616 to 634). -/
theorem seg_616 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 19 616 (factsAt L g 616 d) 635 (factsAt L g 635 d) := by
  intro t h
  sm_seg h

/-- Bias pointers 20 to 44 (pcs 635 to 659). -/
theorem seg_635 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 25 635 (factsAt L g 635 d) 660 (factsAt L g 660 d) := by
  intro t h
  sm_seg h

/-- Bias pointers 45 to 63 (pcs 660 to 678). -/
theorem seg_660 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 19 660 (factsAt L g 660 d) 679 (factsAt L g 679 d) := by
  intro t h
  sm_seg h

/-- The first preload's destination holds the zero half-word (pc 679). -/
theorem seg_679 (d : D) (hT : g % L.block < 128) (hcw : d.cw = 0) :
    Seg kernel asms L g 1 679 (factsAt L g 679 d) 680 (factsAt L g 680 d) := by
  intro t h
  sm_seg h [hcw, D.wd]

/-- **The setup before the preloads**: from the state after the barrier (pc 575) to the first
preload (pc 680), at a state with no preloaded word. -/
theorem seg_setupA (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hcw : d.cw = 0) :
    Seg kernel asms L g 104 576 (factsAt L g 576 d) 680 (factsAt L g 680 d) := by
  have h0 := seg_576 d hT hok.qlen
  have h1 := h0.comp (seg_587 d hT)
  have h2 := h1.comp (seg_598 d hT)
  have h3 := h2.comp (seg_600 d hok)
  have h4 := h3.comp (seg_601 d hok)
  have h5 := h4.comp (seg_602 d hT)
  have h6 := h5.comp (seg_603 d hT)
  have h7 := h6.comp (seg_604 d hT)
  have h8 := h7.comp (seg_605 d hT)
  have h9 := h8.comp (seg_606 d hT)
  have h10 := h9.comp (seg_607 d hT)
  have h11 := h10.comp (seg_608 d hT)
  have h12 := h11.comp (seg_609 d hT)
  have h13 := h12.comp (seg_610 d hT)
  have h14 := h13.comp (seg_611 d hT hok)
  have h15 := h14.comp (seg_615 d hT)
  have h16 := h15.comp (seg_616 d hT)
  have h17 := h16.comp (seg_635 d hT)
  have h18 := h17.comp (seg_660 d hT)
  have h19 := h18.comp (seg_679 d hT hcw)
  exact Seg.of_len h19 rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
