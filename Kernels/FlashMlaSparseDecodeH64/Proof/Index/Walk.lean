-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.WalkHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWalk
public import Mathlib.Tactic.FinCases
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The index warp's walks inside its loops

The local code between a loop's events, as control segments cut at the branches: the main loop's
head (`walk_top`, pcs 2426–2445), the end of a main block (`walk_endA`, pcs 2477–2494), the main
loop's entry after the first pair (`walk_entry`, pcs 2404–2425), and the same for the extra loop
(`walk_xtop`, `walk_endB`, `walk_xentry`). Each ends at the event its transition names; the
branch outcomes are split first, so a target is a literal site. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-! ### The main loop -/

theorem walk_topW (c : IxCtl) (h : scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1) = true) :
    SegU kernel Assumptions.all L g 2426 (factsFrom (ixLive 2426) (ixVal P L g c)) 2446
      (ixFacts P L g { c with cnt := addi c.cnt 1 } .wA) := by
  ix_br 2428 19 (scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1)) { c with cnt := addi c.cnt 1 }
    Flow.code_2428
  rw [h]
  exact SegU.comp (b := 2432) (G := factsFrom (ixLive 2432) (ixVal P L g
    { c with cnt := addi c.cnt 1 })) (by ix_seg) (ixu_head _)

theorem walk_topP (c : IxCtl) (h : scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1) = false) :
    SegU kernel Assumptions.all L g 2426 (factsFrom (ixLive 2426) (ixVal P L g c)) 2429
      (ixFacts P L g { c with cnt := addi c.cnt 1 } .pf) := by
  ix_br 2428 19 (scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1)) { c with cnt := addi c.cnt 1 }
    Flow.code_2428
  rw [h]; ix_seg

/-- **The main loop's head.** -/
theorem walk_top (c : IxCtl) :
    SegU kernel Assumptions.all L g 2426 (factsFrom (ixLive 2426) (ixVal P L g c))
      (mainTop c).1.pc (ixFacts P L g (mainTop c).2 (mainTop c).1) := by
  cases h : scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1)
  · rw [show mainTop c = (.pf, { c with cnt := addi c.cnt 1 }) by
      unfold mainTop; dsimp only; rw [h]; rfl]
    exact walk_topP c h
  · rw [show mainTop c = (.wA, { c with cnt := addi c.cnt 1 }) by
      unfold mainTop; dsimp only; rw [h]; rfl]
    exact walk_topW c h

/-- The control words after a block: parity, slot and the main loop's counter. -/
abbrev endA (c : IxCtl) : IxCtl :=
  { c with
    par := ixParNext c.par c.slot, slot := c.slot + 1, neg := addi c.neg 1,
    wpos := addi c.wpos 64, aptr := addi64 c.aptr 256, m0 := c.n0, m1 := c.n1 }

/-- The ring's parity and slot after a block. The code `selp`s on the slot's test, which
`seg_ctl` evaluates at a checkpoint only on a literal: the stretch splits on slot and parity. -/
abbrev ring (c : IxCtl) : IxCtl :=
  { c with par := ixParNext c.par c.slot, slot := c.slot + 1 }

/-- The ring's update up to its parity's `selp` (pcs 2477–2480): the parity's test as a fact. -/
theorem ringA (c : IxCtl) :
    SegU kernel Assumptions.all L g 2477 (ixFacts P L g c .arrA) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c)) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  fin_cases slot <;> cases par <;> ix_seg

/-- The parity's `selp` on its test and the slot's advance (pcs 2481–2487). -/
theorem ringA2 (c : IxCtl) :
    SegU kernel Assumptions.all L g 2481
      ((30, .pred (ixParNext c.par c.slot)) :: factsFrom ((ixLive 2481).erase 30) (ixVal P L g c))
      2488 (factsFrom (ixLive 2488) (ixVal P L g (ring c))) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  dsimp only [ring]
  generalize ixParNext par slot = y
  fin_cases slot <;> cases y <;> ix_seg

/-- The extra loop's ring update up to the parity's `selp` (pcs 2566–2569). -/
theorem ringB (c : IxCtl) :
    SegU kernel Assumptions.all L g 2566 (ixFacts P L g c .arrB) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c)) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  fin_cases slot <;> cases par <;> ix_seg

/-- The extra loop's parity `selp` and slot advance (pcs 2570–2576). -/
theorem ringB2 (c : IxCtl) :
    SegU kernel Assumptions.all L g 2570
      ((45, .pred (ixParNext c.par c.slot)) :: factsFrom ((ixLive 2570).erase 45) (ixVal P L g c))
      2577 (factsFrom (ixLive 2577) (ixVal P L g (ring c))) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  dsimp only [ring]
  generalize ixParNext par slot = y
  fin_cases slot <;> cases y <;> ix_seg

/-- The end of a main block up to its back-edge (pcs 2477–2493). -/
theorem walk_endA0 (c : IxCtl) :
    SegU kernel Assumptions.all L g 2477 (ixFacts P L g c .arrA) 2494
      (factsFrom (ixLive 2494) (ixVal P L g (endA c))) := by
  refine SegU.comp (b := 2488) (G := factsFrom (ixLive 2488) (ixVal P L g (ring c)))
    (SegU.comp (ringA c) (ringA2 c)) (by ix_seg)

/-- **The end of a main block**: the next block's head, or past the main loop. -/
theorem walk_endA (c : IxCtl) :
    SegU kernel Assumptions.all L g 2477 (ixFacts P L g c .arrA)
      (mainEnd c).1.pc (ixFacts P L g (mainEnd c).2 (mainEnd c).1) := by
  refine SegU.comp (walk_endA0 c) ?_
  refine SegU.pick (r := 31) (x := .pred (scmpi .ne .b (addi c.neg 1) 0))
    (mem_factsFrom_eq (show 31 ∈ ixLive 2494 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_2494 bra_rule noSegments.segFreePc) ?_
  cases h : scmpi .ne .b (addi c.neg 1) 0
  · rw [show mainEnd c = ixMainDone (endA c) by
      unfold mainEnd; dsimp only; rw [h]; rfl]
    exact SegU.comp (b := 2495) (G := factsFrom (ixLive 2495) (ixVal P L g (endA c)))
      (by ix_seg) (ixw_done _)
  · rw [show mainEnd c = mainTop (endA c) by
      unfold mainEnd; dsimp only; rw [h]; rfl]
    exact SegU.comp (b := 2426) (G := factsFrom (ixLive 2426) (ixVal P L g (endA c)))
      (by ix_seg) (walk_top _)

/-- The main loop's entry words. -/
abbrev entryA (P : Params) (L : Launch) (g : Nat) (c : IxCtl) : IxCtl :=
  { c with
    neg := neg32 (ixNmin c.l0 c.l1), par := false, cnt := i32 0, slot := 0, wpos := ixPos0 L g,
    aptr := ixAp0 P L g, n0 := c.m0, n1 := c.m1 }

/-- After the first pair, into the main loop (pcs 2404–2425). -/
theorem walk_entryM (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = false) :
    SegU kernel Assumptions.all L g 2404
      ((2974, w32 y0) :: (2973, w32 y1) :: ixFacts P L g c .pre) 2426
      (factsFrom (ixLive 2426) (ixVal P L g (entryA P L g { c with m0 := y0, m1 := y1 }))) := by
  ix_br 2409 18 (scmpi .lt .s (ixNmin c.l0 c.l1) 1)
    { c with m0 := y0, m1 := y1, slot := 0, par := false } Flow.code_2409
  rw [h]; ix_seg

/-- After the first pair, past the main loop (pcs 2404–2409). -/
theorem walk_entryD (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = true) :
    SegU kernel Assumptions.all L g 2404
      ((2974, w32 y0) :: (2973, w32 y1) :: ixFacts P L g c .pre) 2495
      (factsFrom (ixLive 2495)
        (ixVal P L g { c with m0 := y0, m1 := y1, slot := 0, par := false })) := by
  ix_br 2409 18 (scmpi .lt .s (ixNmin c.l0 c.l1) 1)
    { c with m0 := y0, m1 := y1, slot := 0, par := false } Flow.code_2409
  rw [h]; ix_seg

/-- **After the first pair.** -/
theorem walk_entry (c : IxCtl) (y0 y1 : BitVec 64) :
    SegU kernel Assumptions.all L g 2404
      ((2974, w32 y0) :: (2973, w32 y1) :: ixFacts P L g c .pre)
      (afterPre P L g { c with m0 := y0, m1 := y1 }).1.pc
      (ixFacts P L g (afterPre P L g { c with m0 := y0, m1 := y1 }).2
        (afterPre P L g { c with m0 := y0, m1 := y1 }).1) := by
  cases h : scmpi .lt .s (ixNmin c.l0 c.l1) 1
  · rw [show afterPre P L g { c with m0 := y0, m1 := y1 } =
      mainTop (entryA P L g { c with m0 := y0, m1 := y1 }) by
      unfold afterPre mainEntry; rw [h]; rfl]
    exact SegU.comp (walk_entryM c y0 y1 h) (walk_top _)
  · rw [show afterPre P L g { c with m0 := y0, m1 := y1 } =
      ixMainDone { c with m0 := y0, m1 := y1, slot := 0, par := false } by
      unfold afterPre ixNoMain; rw [h]; rfl]
    exact SegU.comp (walk_entryD c y0 y1 h) (ixw_done _)

/-! ### The extra loop -/

theorem walk_xtopW (c : IxCtl) (h : scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1) = true) :
    SegU kernel Assumptions.all L g 2512 (factsFrom (ixLive 2512) (ixVal P L g c)) 2534
      (ixFacts P L g { c with xb := addi c.xb 1 } .wB) := by
  ix_br 2514 34 (scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1)) { c with xb := addi c.xb 1 }
    Flow.code_2514
  rw [h]
  exact SegU.comp (b := 2520) (G := factsFrom (ixLive 2520) (ixVal P L g
    { c with xb := addi c.xb 1 })) (by ix_seg) (ixu_xhead _)

theorem walk_xtopP (c : IxCtl) (h : scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1) = false) :
    SegU kernel Assumptions.all L g 2512 (factsFrom (ixLive 2512) (ixVal P L g c)) 2517
      (ixFacts P L g { c with xb := addi c.xb 1 } .xpf) := by
  ix_br 2514 34 (scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1)) { c with xb := addi c.xb 1 }
    Flow.code_2514
  rw [h]; ix_seg

/-- **The extra loop's head.** -/
theorem walk_xtop (c : IxCtl) :
    SegU kernel Assumptions.all L g 2512 (factsFrom (ixLive 2512) (ixVal P L g c))
      (xTop c).1.pc (ixFacts P L g (xTop c).2 (xTop c).1) := by
  cases h : scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1)
  · rw [show xTop c = (.xpf, { c with xb := addi c.xb 1 }) by
      unfold xTop; dsimp only; rw [h]; rfl]
    exact walk_xtopP c h
  · rw [show xTop c = (.wB, { c with xb := addi c.xb 1 }) by
      unfold xTop; dsimp only; rw [h]; rfl]
    exact walk_xtopW c h

/-- The control words after an extra block. -/
abbrev endB (c : IxCtl) : IxCtl :=
  { c with
    par := ixParNext c.par c.slot, slot := c.slot + 1, xn := addi c.xn 1, xa := addi c.xa 64,
    e0 := c.f0, e1 := c.f1 }

/-- The end of an extra block up to its back-edge (pcs 2566–2581). -/
theorem walk_endB0 (c : IxCtl) :
    SegU kernel Assumptions.all L g 2566 (ixFacts P L g c .arrB) 2582
      (factsFrom (ixLive 2582) (ixVal P L g (endB c))) := by
  refine SegU.comp (b := 2577) (G := factsFrom (ixLive 2577) (ixVal P L g (ring c)))
    (SegU.comp (ringB c) (ringB2 c)) (by ix_seg)

/-- **The end of an extra block**: the next block's head, or named barrier 12. -/
theorem walk_endB (c : IxCtl) :
    SegU kernel Assumptions.all L g 2566 (ixFacts P L g c .arrB)
      (xEnd c).1.pc (ixFacts P L g (xEnd c).2 (xEnd c).1) := by
  refine SegU.comp (walk_endB0 c) ?_
  refine SegU.pick (r := 46) (x := .pred (scmpi .ne .b (addi c.xn 1) 0))
    (mem_factsFrom_eq (show 46 ∈ ixLive 2582 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_2582 bra_rule noSegments.segFreePc) ?_
  cases h : scmpi .ne .b (addi c.xn 1) 0
  · rw [show xEnd c = (.bar, endB c) by
      unfold xEnd; dsimp only; rw [h]; rfl]
    ix_seg
  · rw [show xEnd c = xTop (endB c) by
      unfold xEnd; dsimp only; rw [h]; rfl]
    exact SegU.comp (b := 2512) (G := factsFrom (ixLive 2512) (ixVal P L g (endB c)))
      (by ix_seg) (walk_xtop _)

/-- The extra loop's entry words. -/
abbrev entryB (L : Launch) (g : Nat) (c : IxCtl) : IxCtl :=
  { c with
    xn := sub32 c.xb (ixNblk c.l0 c.l1), xa := ixXa0 L g, f0 := c.e0, f1 := c.e1 }

theorem walk_xentryL (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false) :
    SegU kernel Assumptions.all L g 2502
      ((2982, w32 y0) :: (2981, w32 y1) :: ixFacts P L g c .xpre) 2512
      (factsFrom (ixLive 2512) (ixVal P L g (entryB L g { c with e0 := y0, e1 := y1 }))) := by
  ix_br 2503 33 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := y0, e1 := y1 }
    Flow.code_2503
  rw [h]; ix_seg

theorem walk_xentryB (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = true) :
    SegU kernel Assumptions.all L g 2502
      ((2982, w32 y0) :: (2981, w32 y1) :: ixFacts P L g c .xpre) 2585
      (ixFacts P L g { c with e0 := y0, e1 := y1 } .bar) := by
  ix_br 2503 33 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := y0, e1 := y1 }
    Flow.code_2503
  rw [h]; ix_seg

/-- **After the extra cache's first pair.** -/
theorem walk_xentry (c : IxCtl) (y0 y1 : BitVec 64) :
    SegU kernel Assumptions.all L g 2502
      ((2982, w32 y0) :: (2981, w32 y1) :: ixFacts P L g c .xpre)
      (afterXpre L g { c with e0 := y0, e1 := y1 }).1.pc
      (ixFacts P L g (afterXpre L g { c with e0 := y0, e1 := y1 }).2
        (afterXpre L g { c with e0 := y0, e1 := y1 }).1) := by
  cases h : scmp .ge .s c.xb (ixNblk c.l0 c.l1)
  · rw [show afterXpre L g { c with e0 := y0, e1 := y1 } =
      xTop (entryB L g { c with e0 := y0, e1 := y1 }) by
      unfold afterXpre; rw [h]; rfl]
    exact SegU.comp (walk_xentryL c y0 y1 h) (walk_xtop _)
  · rw [show afterXpre L g { c with e0 := y0, e1 := y1 } =
      (.bar, { c with e0 := y0, e1 := y1 }) by
      unfold afterXpre; rw [h]; rfl]
    exact walk_xentryB c y0 y1 h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
