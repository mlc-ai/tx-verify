-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictWalkC
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The strict walks of the main loop -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000


variable {P : Params} {L : Launch} {g : Nat}

/-- After the first pair, into the main loop (pcs 2404–2425). -/
theorem qk_entryM (hP : Plain L g) (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = false) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2404
      ((2974, w32 y0) :: (2973, w32 y1) :: ixFacts P L g c .pre) 2426
      (factsFrom (ixLive 2426) (ixVal P L g (entryA P L g { c with m0 := y0, m1 := y1 }))) := by
  ixq_br 2409 18 (scmpi .lt .s (ixNmin c.l0 c.l1) 1)
    { c with m0 := y0, m1 := y1, slot := 0, par := false } Flow.code_2409 with h
  refine SegQ.comp (b := 2420)
    (G := factsFrom (ixLive 2420) (ixVal P L g
      { c with
        m0 := y0, m1 := y1, slot := 0, par := false, aptr := ixAp0 P L g, wpos := ixPos0 L g }))
    (by ixq_seg) ?_
  ixq_seg

/-- After the first pair, past the main loop (pcs 2404–2409). -/
theorem qk_entryD (hP : Plain L g) (c : IxCtl) (y0 y1 : BitVec 64)
    (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = true) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2404
      ((2974, w32 y0) :: (2973, w32 y1) :: ixFacts P L g c .pre) 2495
      (factsFrom (ixLive 2495)
        (ixVal P L g { c with m0 := y0, m1 := y1, slot := 0, par := false })) := by
  ixq_br 2409 18 (scmpi .lt .s (ixNmin c.l0 c.l1) 1)
    { c with m0 := y0, m1 := y1, slot := 0, par := false } Flow.code_2409 with h
  ixq_seg

/-- **After the first pair.** -/
theorem qk_entry (hP : Plain L g) (c : IxCtl) (y0 y1 : BitVec 64) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2404
      ((2974, w32 y0) :: (2973, w32 y1) :: ixFacts P L g c .pre)
      (afterPre P L g { c with m0 := y0, m1 := y1 }).1.pc
      (ixFacts P L g (afterPre P L g { c with m0 := y0, m1 := y1 }).2
        (afterPre P L g { c with m0 := y0, m1 := y1 }).1) := by
  cases h : scmpi .lt .s (ixNmin c.l0 c.l1) 1
  · rw [show afterPre P L g { c with m0 := y0, m1 := y1 } =
      mainTop (entryA P L g { c with m0 := y0, m1 := y1 }) by
      unfold afterPre mainEntry; rw [h]; rfl]
    exact SegQ.comp (qk_entryM hP c y0 y1 h) (qk_top hP _)
  · rw [show afterPre P L g { c with m0 := y0, m1 := y1 } =
      ixMainDone { c with m0 := y0, m1 := y1, slot := 0, par := false } by
      unfold afterPre ixNoMain; rw [h]; rfl]
    exact SegQ.comp (qk_entryD hP c y0 y1 h) (qw_done hP _)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
