-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictWalkHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Walk
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The strict walks of the extra loop -/

/-! # The strict walks of the main loop -/

/-! # The strict walks of the main loop -/

/-! # The strict walks of the main loop -/

/-! # The strict index walks after the lengths

`IndexWalk.lean`'s walks (`ixw_*`) as strict segments under `QT ixQt`: from pc 2366 (the lengths
known) to the event `ixLens` names, and from pc 2495 (past the main cache's blocks) to the event
`ixMainDone` names. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- Past the main cache's blocks to the extra cache's first pair (pcs 2495–2500). -/
theorem qw_doneX (hP : Plain L g) (c : IxCtl) (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2495 (factsFrom (ixLive 2495) (ixVal P L g c)) 2501
      (ixFacts P L g { c with e0 := 0, e1 := 0 } .xpre) := by
  ixq_br 2498 32 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := 0, e1 := 0 }
    Flow.code_2498 with h; ixq_seg

/-- Past the main cache's blocks to named barrier 12 (pcs 2495–2503, 2583–2584). -/
theorem qw_doneB (hP : Plain L g) (c : IxCtl) (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2495 (factsFrom (ixLive 2495) (ixVal P L g c)) 2585
      (ixFacts P L g { c with e0 := 0, e1 := 0 } .bar) := by
  ixq_br 2498 32 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := 0, e1 := 0 }
    Flow.code_2498 with h
  ixq_br 2503 33 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := 0, e1 := 0 }
    Flow.code_2503 with h; ixq_seg

/-- **Past the main cache's blocks** (pcs 2495–2503, 2583–2584). -/
theorem qw_done (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2495 (factsFrom (ixLive 2495) (ixVal P L g c))
      (ixMainDone c).1.pc (ixFacts P L g (ixMainDone c).2 (ixMainDone c).1) := by
  cases h : scmp .ge .s c.xb (ixNblk c.l0 c.l1)
  · rw [show ixMainDone c = (.xpre, { c with e0 := 0, e1 := 0 }) by
      unfold ixMainDone; rw [h]; rfl]
    exact qw_doneX hP c h
  · rw [show ixMainDone c = (.bar, { c with e0 := 0, e1 := 0 }) by
      unfold ixMainDone; rw [h]; rfl]
    exact qw_doneB hP c h

/-- The block counts (pcs 2366–2384). -/
theorem qw_counts0 (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2385
      (factsFrom (ixLive 2385) (ixVal P L g { c with xb := ixNmain c.l0 })) := by
  ixq_seg

/-- The index rows' offsets and the tests (pcs 2385–2397). -/
theorem qw_counts1 (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2385
      (factsFrom (ixLive 2385) (ixVal P L g { c with xb := ixNmain c.l0 })) 2398
      (factsFrom (ixLive 2398)
        (ixVal P L g { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 })) := by
  ixq_seg

/-- The block counts' tests (pcs 2366–2398), up to the branch over the first pair. -/
theorem qw_counts (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2398
      (factsFrom (ixLive 2398)
        (ixVal P L g { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 })) :=
  SegQ.comp (qw_counts0 hP c) (qw_counts1 hP c)

/-- The lengths with a main block: on to the first pair. -/
theorem qw_pre (hP : Plain L g) (c : IxCtl) (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2403
      (ixFacts P L g { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 } .pre) := by
  refine SegQ.comp (qw_counts hP c) ?_
  refine SegQ.pick (r := 17) (x := .pred (scmpi .lt .s (ixNmin c.l0 c.l1) 1))
    (mem_factsFrom_eq (show 17 ∈ ixLive 2398 by decide +kernel) rfl) ?_
  ixq_bra Flow.code_2398 with h; ixq_seg

/-- The lengths without a main block: past the main loop (pcs 2398–2409), slot and parity 0. -/
theorem qw_noMain (hP : Plain L g) (c : IxCtl) (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2495
      (factsFrom (ixLive 2495)
        (ixVal P L g
          { c with xb := ixNmain c.l0, m0 := 0, m1 := 0, slot := 0, par := false })) := by
  refine SegQ.comp (qw_counts hP c) ?_
  refine SegQ.pick (r := 17) (x := .pred (scmpi .lt .s (ixNmin c.l0 c.l1) 1))
    (mem_factsFrom_eq (show 17 ∈ ixLive 2398 by decide +kernel) rfl) ?_
  ixq_bra Flow.code_2398 with h
  ixq_br 2409 18 (scmpi .lt .s (ixNmin c.l0 c.l1) 1)
    { c with xb := ixNmain c.l0, m0 := 0, m1 := 0, slot := 0, par := false } Flow.code_2409
    with h; ixq_seg

/-- **After the lengths** (pcs 2366–2409): the first index pair, or past the main loop. -/
theorem qw_lens (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2366 (factsFrom (ixLive 2366) (ixVal P L g c))
      (ixLens c).1.pc (ixFacts P L g (ixLens c).2 (ixLens c).1) := by
  cases h : scmpi .lt .s (ixNmin c.l0 c.l1) 1
  · rw [show ixLens c = (.pre, { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 }) by
      unfold ixLens; dsimp only; rw [h]; rfl]
    exact qw_pre hP c h
  · rw [show ixLens c = ixMainDone
        { c with xb := ixNmain c.l0, m0 := 0, m1 := 0, slot := 0, par := false } by
      unfold ixLens ixNoMain; dsimp only; rw [h]; rfl]
    exact SegQ.comp (qw_noMain hP c h) (qw_done hP _)


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

theorem qk_topW (hP : Plain L g) (c : IxCtl) (h : scmp .ge .s (addi c.cnt 1)
    (ixNmin c.l0 c.l1) = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2426 (factsFrom (ixLive 2426) (ixVal P L g c)) 2446
      (ixFacts P L g { c with cnt := addi c.cnt 1 } .wA) := by
  ixq_br 2428 19 (scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1)) { c with cnt := addi c.cnt 1 }
    Flow.code_2428 with h
  exact SegQ.comp (b := 2432) (G := factsFrom (ixLive 2432) (ixVal P L g
    { c with cnt := addi c.cnt 1 })) (by ixq_seg) (qk_head hP _)

theorem qk_topP (hP : Plain L g) (c : IxCtl) (h : scmp .ge .s (addi c.cnt 1)
    (ixNmin c.l0 c.l1) = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2426 (factsFrom (ixLive 2426) (ixVal P L g c)) 2429
      (ixFacts P L g { c with cnt := addi c.cnt 1 } .pf) := by
  ixq_br 2428 19 (scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1)) { c with cnt := addi c.cnt 1 }
    Flow.code_2428 with h; ixq_seg

/-- **The main loop's head.** -/
theorem qk_top (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2426 (factsFrom (ixLive 2426) (ixVal P L g c))
      (mainTop c).1.pc (ixFacts P L g (mainTop c).2 (mainTop c).1) := by
  cases h : scmp .ge .s (addi c.cnt 1) (ixNmin c.l0 c.l1)
  · rw [show mainTop c = (.pf, { c with cnt := addi c.cnt 1 }) by
      unfold mainTop; dsimp only; rw [h]; rfl]
    exact qk_topP hP c h
  · rw [show mainTop c = (.wA, { c with cnt := addi c.cnt 1 }) by
      unfold mainTop; dsimp only; rw [h]; rfl]
    exact qk_topW hP c h

/-- The ring's update up to its parity's `selp`, for parity `false`. -/
theorem qringA_f (hP : Plain L g) (c : IxCtl) (hp : c.par = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2477 (ixFacts P L g c .arrA) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c)) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  simp only at hp
  subst hp
  fin_cases slot <;> ixq_seg

/-- The ring's update up to its parity's `selp`, for parity `true`. -/
theorem qringA_t (hP : Plain L g) (c : IxCtl) (hp : c.par = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2477 (ixFacts P L g c .arrA) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c)) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  simp only at hp
  subst hp
  fin_cases slot <;> ixq_seg

/-- The ring's update up to its parity's `selp` (the parity's test as a fact). -/
theorem qringA (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2477 (ixFacts P L g c .arrA) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c)) := by
  by_cases hp : c.par = true
  · exact qringA_t hP c hp
  · exact qringA_f hP c (by simpa using hp)

/-- The parity's `selp` and the slot's advance, for the test's value `false`. -/
theorem qringA2_f (hP : Plain L g) (c : IxCtl) (hy : ixParNext c.par c.slot = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c))
      2488 (factsFrom (ixLive 2488) (ixVal P L g (ring c))) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  dsimp only [ring]
  rw [hy]
  fin_cases slot <;> ixq_seg

/-- The parity's `selp` and the slot's advance, for the test's value `true`. -/
theorem qringA2_t (hP : Plain L g) (c : IxCtl) (hy : ixParNext c.par c.slot = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c))
      2488 (factsFrom (ixLive 2488) (ixVal P L g (ring c))) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  dsimp only [ring]
  rw [hy]
  fin_cases slot <;> ixq_seg

/-- The parity's `selp` on its test and the slot's advance. -/
theorem qringA2 (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2481
      ((30, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2481).erase 30) (ixVal P L g c))
      2488 (factsFrom (ixLive 2488) (ixVal P L g (ring c))) := by
  by_cases hy : ixParNext c.par c.slot = true
  · exact qringA2_t hP c hy
  · exact qringA2_f hP c (by simpa using hy)


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- The ring's update up to its parity's `selp`, for parity `false`. -/
theorem qringB_f (hP : Plain L g) (c : IxCtl) (hp : c.par = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2566 (ixFacts P L g c .arrB) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c)) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  simp only at hp
  subst hp
  fin_cases slot <;> ixq_seg

/-- The ring's update up to its parity's `selp`, for parity `true`. -/
theorem qringB_t (hP : Plain L g) (c : IxCtl) (hp : c.par = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2566 (ixFacts P L g c .arrB) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c)) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  simp only at hp
  subst hp
  fin_cases slot <;> ixq_seg

/-- The ring's update up to its parity's `selp` (the parity's test as a fact). -/
theorem qringB (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2566 (ixFacts P L g c .arrB) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c)) := by
  by_cases hp : c.par = true
  · exact qringB_t hP c hp
  · exact qringB_f hP c (by simpa using hp)

/-- The parity's `selp` and the slot's advance, for the test's value `false`. -/
theorem qringB2_f (hP : Plain L g) (c : IxCtl) (hy : ixParNext c.par c.slot = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c))
      2577 (factsFrom (ixLive 2577) (ixVal P L g (ring c))) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  dsimp only [ring]
  rw [hy]
  fin_cases slot <;> ixq_seg

/-- The parity's `selp` and the slot's advance, for the test's value `true`. -/
theorem qringB2_t (hP : Plain L g) (c : IxCtl) (hy : ixParNext c.par c.slot = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c))
      2577 (factsFrom (ixLive 2577) (ixVal P L g (ring c))) := by
  obtain ⟨l0, l1, cnt, neg, slot, par, xb, xn, wpos, aptr, xa, m0, m1, n0, n1, e0, e1, f0,
    f1⟩ := c
  dsimp only [ring]
  rw [hy]
  fin_cases slot <;> ixq_seg

/-- The parity's `selp` on its test and the slot's advance. -/
theorem qringB2 (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2570
      ((45, .pred (ixParNext c.par c.slot)) ::
        factsFrom ((ixLive 2570).erase 45) (ixVal P L g c))
      2577 (factsFrom (ixLive 2577) (ixVal P L g (ring c))) := by
  by_cases hy : ixParNext c.par c.slot = true
  · exact qringB2_t hP c hy
  · exact qringB2_f hP c (by simpa using hy)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- The end of a main block up to its back-edge (pcs 2477–2493). -/
theorem qk_endA0 (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2477 (ixFacts P L g c .arrA) 2494
      (factsFrom (ixLive 2494) (ixVal P L g (endA c))) := by
  refine SegQ.comp (b := 2488) (G := factsFrom (ixLive 2488) (ixVal P L g (ring c)))
    (SegQ.comp (qringA hP c) (qringA2 hP c)) (by ixq_seg)

/-- **The end of a main block**: the next block's head, or past the main loop. -/
theorem qk_endA (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2477 (ixFacts P L g c .arrA)
      (mainEnd c).1.pc (ixFacts P L g (mainEnd c).2 (mainEnd c).1) := by
  refine SegQ.comp (qk_endA0 hP c) ?_
  refine SegQ.pick (r := 31) (x := .pred (scmpi .ne .b (addi c.neg 1) 0))
    (mem_factsFrom_eq (show 31 ∈ ixLive 2494 by decide +kernel) rfl) ?_
  cases h : scmpi .ne .b (addi c.neg 1) 0
  · ixq_bra Flow.code_2494 with h
    rw [show mainEnd c = ixMainDone (endA c) by
      unfold mainEnd; dsimp only; rw [h]; rfl]
    exact SegQ.comp (b := 2495) (G := factsFrom (ixLive 2495) (ixVal P L g (endA c)))
      (by ixq_seg) (qw_done hP _)
  · ixq_bra Flow.code_2494 with h
    rw [show mainEnd c = mainTop (endA c) by
      unfold mainEnd; dsimp only; rw [h]; rfl]
    exact SegQ.comp (b := 2426) (G := factsFrom (ixLive 2426) (ixVal P L g (endA c)))
      (by ixq_seg) (qk_top hP _)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

theorem qk_xtopW (hP : Plain L g) (c : IxCtl) (h : scmp .ge .s (addi c.xb 1)
    (ixNblk c.l0 c.l1) = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2512 (factsFrom (ixLive 2512) (ixVal P L g c)) 2534
      (ixFacts P L g { c with xb := addi c.xb 1 } .wB) := by
  ixq_br 2514 34 (scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1)) { c with xb := addi c.xb 1 }
    Flow.code_2514 with h
  exact SegQ.comp (b := 2520) (G := factsFrom (ixLive 2520) (ixVal P L g
    { c with xb := addi c.xb 1 })) (by ixq_seg) (qk_xhead hP _)

theorem qk_xtopP (hP : Plain L g) (c : IxCtl) (h : scmp .ge .s (addi c.xb 1)
    (ixNblk c.l0 c.l1) = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2512 (factsFrom (ixLive 2512) (ixVal P L g c)) 2517
      (ixFacts P L g { c with xb := addi c.xb 1 } .xpf) := by
  ixq_br 2514 34 (scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1)) { c with xb := addi c.xb 1 }
    Flow.code_2514 with h; ixq_seg

/-- **The extra loop's head.** -/
theorem qk_xtop (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2512 (factsFrom (ixLive 2512) (ixVal P L g c))
      (xTop c).1.pc (ixFacts P L g (xTop c).2 (xTop c).1) := by
  cases h : scmp .ge .s (addi c.xb 1) (ixNblk c.l0 c.l1)
  · rw [show xTop c = (.xpf, { c with xb := addi c.xb 1 }) by
      unfold xTop; dsimp only; rw [h]; rfl]
    exact qk_xtopP hP c h
  · rw [show xTop c = (.wB, { c with xb := addi c.xb 1 }) by
      unfold xTop; dsimp only; rw [h]; rfl]
    exact qk_xtopW hP c h

/-- The end of an extra block up to its back-edge (pcs 2566–2581). -/
theorem qk_endB0 (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2566 (ixFacts P L g c .arrB) 2582
      (factsFrom (ixLive 2582) (ixVal P L g (endB c))) := by
  refine SegQ.comp (b := 2577) (G := factsFrom (ixLive 2577) (ixVal P L g (ring c)))
    (SegQ.comp (qringB hP c) (qringB2 hP c)) (by ixq_seg)

/-- **The end of an extra block**: the next block's head, or named barrier 12. -/
theorem qk_endB (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2566 (ixFacts P L g c .arrB)
      (xEnd c).1.pc (ixFacts P L g (xEnd c).2 (xEnd c).1) := by
  refine SegQ.comp (qk_endB0 hP c) ?_
  refine SegQ.pick (r := 46) (x := .pred (scmpi .ne .b (addi c.xn 1) 0))
    (mem_factsFrom_eq (show 46 ∈ ixLive 2582 by decide +kernel) rfl) ?_
  cases h : scmpi .ne .b (addi c.xn 1) 0
  · ixq_bra Flow.code_2582 with h
    rw [show xEnd c = (.bar, endB c) by
      unfold xEnd; dsimp only; rw [h]; rfl]
    ixq_seg
  · ixq_bra Flow.code_2582 with h
    rw [show xEnd c = xTop (endB c) by
      unfold xEnd; dsimp only; rw [h]; rfl]
    exact SegQ.comp (b := 2512) (G := factsFrom (ixLive 2512) (ixVal P L g (endB c)))
      (by ixq_seg) (qk_xtop hP _)

/-- **The extra loop's entry words.** The fall-through of the test at pc 2503 gives the extra
page size's nonzero tag (`hz`). -/
theorem qk_xentryL (hP : Plain L g) (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false)
    (hz : (pw P.extraPage).toNat % 2 ^ 32 ≠ 0) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2502
      ((2982, w32 y0) :: (2981, w32 y1) :: ixFacts P L g c .xpre) 2512
      (factsFrom (ixLive 2512) (ixVal P L g (entryB L g { c with e0 := y0, e1 := y1 }))) := by
  refine SegQ.comp (b := 2503)
    (G := factsFrom (ixLive 2503) (ixVal P L g { c with e0 := y0, e1 := y1 })) (by ixq_seg) ?_
  refine SegQ.pick (r := 33) (x := .pred (scmp .ge .s c.xb (ixNblk c.l0 c.l1)))
    (mem_factsFrom_eq (show 33 ∈ ixLive 2503 by decide +kernel) rfl) ?_
  rw [h]
  have hm : (502, Value.bits 32 (pw P.extraPage)) ∈
      factsFrom (ixLive 2503) (ixVal P L g { c with e0 := y0, e1 := y1 }) :=
    mem_factsFrom_eq (show 502 ∈ ixLive 2503 by decide +kernel) rfl
  refine SegQ.comp (SegQ.branchEx (ex := [(502, .nz 32)]) false Flow.code_2503 bra_rule
    noSegments.segFreePc (fun t ht => typed_nz_of_fact hm hz ht) (by decide +kernel)) ?_
  ixq_seg

theorem qk_xentryB (hP : Plain L g) (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2502
      ((2982, w32 y0) :: (2981, w32 y1) :: ixFacts P L g c .xpre) 2585
      (ixFacts P L g { c with e0 := y0, e1 := y1 } .bar) := by
  ixq_br 2503 33 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := y0, e1 := y1 }
    Flow.code_2503 with h; ixq_seg

/-- **After the extra cache's first pair.** -/
theorem qk_xentry (hP : Plain L g) (c : IxCtl) (y0 y1 : BitVec 64)
    (hz : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false → (pw P.extraPage).toNat % 2 ^ 32 ≠ 0) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2502
      ((2982, w32 y0) :: (2981, w32 y1) :: ixFacts P L g c .xpre)
      (afterXpre L g { c with e0 := y0, e1 := y1 }).1.pc
      (ixFacts P L g (afterXpre L g { c with e0 := y0, e1 := y1 }).2
        (afterXpre L g { c with e0 := y0, e1 := y1 }).1) := by
  cases h : scmp .ge .s c.xb (ixNblk c.l0 c.l1)
  · rw [show afterXpre L g { c with e0 := y0, e1 := y1 } =
      xTop (entryB L g { c with e0 := y0, e1 := y1 }) by
      unfold afterXpre; rw [h]; rfl]
    exact SegQ.comp (qk_xentryL hP c y0 y1 h (hz h)) (qk_xtop hP _)
  · rw [show afterXpre L g { c with e0 := y0, e1 := y1 } =
      (.bar, { c with e0 := y0, e1 := y1 }) by
      unfold afterXpre; rw [h]; rfl]
    exact qk_xentryB hP c y0 y1 h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
