-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.BranchU
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The index warp's walks after its lengths

`ixw_lens`: from pc 2366 (the lengths in `%r2968`, `%r2969`) the code's tests on the block counts
lead to the event `ixLens` names; `ixw_done`: from pc 2495 (past the main cache's blocks) to the
event `ixMainDone` names. Both are control segments (`ctl_seg`) cut at the branches, whose
predicates the table states. The index warp's length loads (`Index/`) and warpgroup 1's head
(`Wg1/`, for null length pointers) end with them. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

set_option hygiene false in
/-- A control segment of the index warp between two tables' facts. -/
macro "ix_seg" : tactic => `(tactic| (
  try dsimp only [ixFacts, IxSite.pc, Bool.false_eq_true, ↓reduceIte]
  ctl_seg))

set_option hygiene false in
/-- Cut the segment at the branch at `pc` (code lemma `cb`) on predicate `p` of value `x`, the
facts there the table's for the words `c`. -/
macro "ix_br " pc:term:max p:term:max x:term:max c:term:max cb:term:max : tactic => `(tactic| (
  refine SegU.comp (b := $pc) (G := factsFrom (ixLive $pc) (ixVal P L g $c)) (by ix_seg) ?_
  refine SegU.pick (r := $p) (x := .pred $x)
    (mem_factsFrom_eq (show $p ∈ ixLive $pc by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ $cb bra_rule noSegments.segFreePc) ?_))

/-- Past the main cache's blocks to the extra cache's first pair (pcs 2495–2500). -/
theorem ixw_doneX (c : IxCtl) (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false) :
    SegU kernel Assumptions.all L g 2495 (factsFrom (ixLive 2495) (ixVal P L g c)) 2501
      (ixFacts P L g { c with e0 := 0, e1 := 0 } .xpre) := by
  ix_br 2498 32 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := 0, e1 := 0 }
    Flow.code_2498
  rw [h]; ix_seg

/-- Past the main cache's blocks to named barrier 12 (pcs 2495–2503, 2583–2584). -/
theorem ixw_doneB (c : IxCtl) (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = true) :
    SegU kernel Assumptions.all L g 2495 (factsFrom (ixLive 2495) (ixVal P L g c)) 2585
      (ixFacts P L g { c with e0 := 0, e1 := 0 } .bar) := by
  ix_br 2498 32 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := 0, e1 := 0 }
    Flow.code_2498
  rw [h]
  ix_br 2503 33 (scmp .ge .s c.xb (ixNblk c.l0 c.l1)) { c with e0 := 0, e1 := 0 }
    Flow.code_2503
  rw [h]; ix_seg

/-- **Past the main cache's blocks** (pcs 2495–2503, 2583–2584). -/
theorem ixw_done (c : IxCtl) :
    SegU kernel Assumptions.all L g 2495 (factsFrom (ixLive 2495) (ixVal P L g c))
      (ixMainDone c).1.pc (ixFacts P L g (ixMainDone c).2 (ixMainDone c).1) := by
  cases h : scmp .ge .s c.xb (ixNblk c.l0 c.l1)
  · rw [show ixMainDone c = (.xpre, { c with e0 := 0, e1 := 0 }) by
      unfold ixMainDone; rw [h]; rfl]
    exact ixw_doneX c h
  · rw [show ixMainDone c = (.bar, { c with e0 := 0, e1 := 0 }) by
      unfold ixMainDone; rw [h]; rfl]
    exact ixw_doneB c h

/-- The block counts (pcs 2366–2384). -/
theorem ixw_counts0 (c : IxCtl) :
    SegU kernel Assumptions.all L g 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2385
      (factsFrom (ixLive 2385) (ixVal P L g { c with xb := ixNmain c.l0 })) := by
  ix_seg

/-- The index rows' offsets and the tests (pcs 2385–2397). -/
theorem ixw_counts1 (c : IxCtl) :
    SegU kernel Assumptions.all L g 2385
      (factsFrom (ixLive 2385) (ixVal P L g { c with xb := ixNmain c.l0 })) 2398
      (factsFrom (ixLive 2398) (ixVal P L g { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 })) := by
  ix_seg

/-- The block counts' tests (pcs 2366–2398), up to the branch over the first pair. -/
theorem ixw_counts (c : IxCtl) :
    SegU kernel Assumptions.all L g 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2398
      (factsFrom (ixLive 2398) (ixVal P L g { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 })) :=
  SegU.comp (ixw_counts0 c) (ixw_counts1 c)

/-- The lengths with a main block: on to the first pair. -/
theorem ixw_pre (c : IxCtl) (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = false) :
    SegU kernel Assumptions.all L g 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2403
      (ixFacts P L g { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 } .pre) := by
  refine SegU.comp (ixw_counts c) ?_
  refine SegU.pick (r := 17) (x := .pred (scmpi .lt .s (ixNmin c.l0 c.l1) 1))
    (mem_factsFrom_eq (show 17 ∈ ixLive 2398 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_2398 bra_rule noSegments.segFreePc) ?_
  rw [h]; ix_seg

/-- The lengths without a main block: past the main loop (pcs 2398–2409), slot and parity 0. -/
theorem ixw_noMain (c : IxCtl) (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = true) :
    SegU kernel Assumptions.all L g 2366 (factsFrom (ixLive 2366) (ixVal P L g c)) 2495
      (factsFrom (ixLive 2495)
        (ixVal P L g
          { c with xb := ixNmain c.l0, m0 := 0, m1 := 0, slot := 0, par := false })) := by
  refine SegU.comp (ixw_counts c) ?_
  refine SegU.pick (r := 17) (x := .pred (scmpi .lt .s (ixNmin c.l0 c.l1) 1))
    (mem_factsFrom_eq (show 17 ∈ ixLive 2398 by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ Flow.code_2398 bra_rule noSegments.segFreePc) ?_
  rw [h]
  ix_br 2409 18 (scmpi .lt .s (ixNmin c.l0 c.l1) 1)
    { c with xb := ixNmain c.l0, m0 := 0, m1 := 0, slot := 0, par := false } Flow.code_2409
  rw [h]; ix_seg

/-- **After the lengths** (pcs 2366–2409): the first index pair, or past the main loop. -/
theorem ixw_lens (c : IxCtl) :
    SegU kernel Assumptions.all L g 2366 (factsFrom (ixLive 2366) (ixVal P L g c))
      (ixLens c).1.pc (ixFacts P L g (ixLens c).2 (ixLens c).1) := by
  cases h : scmpi .lt .s (ixNmin c.l0 c.l1) 1
  · rw [show ixLens c = (.pre, { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 }) by
      unfold ixLens; dsimp only; rw [h]; rfl]
    exact ixw_pre c h
  · rw [show ixLens c = ixMainDone
        { c with xb := ixNmain c.l0, m0 := 0, m1 := 0, slot := 0, par := false } by
      unfold ixLens ixNoMain; dsimp only; rw [h]; rfl]
    exact SegU.comp (ixw_noMain c h) (ixw_done _)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
