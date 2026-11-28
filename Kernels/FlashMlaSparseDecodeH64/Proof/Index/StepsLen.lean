-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The index warp's obligations at its length loads and first index pairs

The length loads (`lenA`, `lenB`) continue with the recorded word: the second length's load when
its pointer is set, else the block counts' tests (`ixw_lens`). The first pairs of the two caches
(`pre`, `xpre`) continue on any payload into the loops' entries (`walk_entry`, `walk_xentry`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- After the first length `x` (pcs 2361–2365). -/
theorem lenA_seg (c : IxCtl) (x : BitVec 64) :
    SegU kernel Assumptions.all L g 2361 ((2968, .bits 32 x) :: ixFacts P L g c .lenA)
      (ixAfterA P { c with l0 := x }).1.pc
      (ixFacts P L g (ixAfterA P { c with l0 := x }).2 (ixAfterA P { c with l0 := x }).1) := by
  cases hz : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
  · rw [show ixAfterA P { c with l0 := x } = (.lenB, { c with l0 := x }) by
      unfold ixAfterA; rw [hz]; rfl]
    ix_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) { c with l0 := x } Flow.code_2362
    rw [hz]; ix_seg
  · rw [show ixAfterA P { c with l0 := x } = ixLens { c with l0 := x } by
      unfold ixAfterA; rw [hz]; rfl]
    ix_br 2362 16 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) { c with l0 := x } Flow.code_2362
    rw [hz]
    exact SegU.comp (b := 2366) (G := factsFrom (ixLive 2366) (ixVal P L g { c with l0 := x }))
      (by ix_seg) (ixw_lens _)

/-- A register the second length does not change. -/
theorem val_l1 (c : IxCtl) (x : BitVec 64) {r : Nat} (hr : r ∈
    [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 2968, 3011,
      3012]) :
    ixVal P L g c r = ixVal P L g { c with l1 := x } r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [ixVal, ixVals, ixLoop, ixSetup, List.lookup, List.cons_append, List.nil_append]
     try rfl)

/-- The facts after the second length are the table's with the loaded word (stated per register:
the unifier would evaluate the two tables). -/
theorem lenB_facts (c : IxCtl) (x : BitVec 64) (R : Nat → Option Value)
    (hR : Holds R ((2969, .bits 32 x) :: ixFacts P L g c .lenB)) :
    Holds R (factsFrom (ixLive 2366) (ixVal P L g { c with l1 := x })) := by
  refine holds_of_pointwise fun r hr => ?_
  rw [show ixLive 2366 =
    [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 2968, 2969,
      3011, 3012] by decide +kernel] at hr
  by_cases h69 : r = 2969
  · subst h69; exact holds_mem hR List.mem_cons_self
  · have hm : r ∈
        [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 2968,
          3011, 3012] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    rw [← val_l1 c x hm]
    refine holds_mem hR (List.mem_cons_of_mem _ (mem_factsFrom ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel

/-- After the second length `x` (pcs 2366 on). -/
theorem lenB_seg (c : IxCtl) (x : BitVec 64) :
    SegU kernel Assumptions.all L g 2366 ((2969, .bits 32 x) :: ixFacts P L g c .lenB)
      (ixLens { c with l1 := x }).1.pc
      (ixFacts P L g (ixLens { c with l1 := x }).2 (ixLens { c with l1 := x }).1) :=
  SegU.comp (SegU.of_seg (Seg.weaken_end (Seg.refl 2366 _) (lenB_facts c x))) (ixw_lens _)

theorem stepAt_lenA (d : D) (hs : d.site = .lenA) : (code P L g).StepAtU d := by
  ix_site
  refine Code.step_loadNcU (C := code P L g) (f := fun x => ofC (ixAfterA P { c with l0 := x }))
    Flow.code_2360 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
    (not_mem_factsFrom (live := ixLive 2360) (by decide +kernel)) (fun x => ?_)
  exact ⟨rfl, rfl, inv_ofC _, lenA_seg c x⟩

theorem stepAt_lenB (d : D) (hs : d.site = .lenB) : (code P L g).StepAtU d := by
  ix_site
  exact Code.step_loadNcU (C := code P L g) (f := fun x => ofC (ixLens { c with l1 := x }))
    Flow.code_2365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
    (not_mem_factsFrom (live := ixLive 2365) (by decide +kernel))
    (fun x => ⟨rfl, rfl, inv_ofC _, lenB_seg c x⟩)

theorem stepAt_pre (d : D) (hs : d.site = .pre) : (code P L g).StepAtU d := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact pairAt (nf := fun y0 y1 => ofC (afterPre P L g { c with m0 := y0, m1 := y1 }))
    (pc := 2403) (r0 := 2974) (r1 := 2973) rfl rfl rfl Flow.code_2403 rfl rfl rfl rfl rfl rfl
    rfl rfl (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun y => walk_entry c (D.w0 ⟨_, el, ac, c⟩) y)

theorem stepAt_xpre (d : D) (hs : d.site = .xpre) : (code P L g).StepAtU d := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact pairAt (nf := fun y0 y1 => ofC (afterXpre L g { c with e0 := y0, e1 := y1 }))
    (pc := 2501) (r0 := 2982) (r1 := 2981) rfl rfl rfl Flow.code_2501 rfl rfl rfl rfl rfl rfl
    rfl rfl (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun y => walk_xentry c (D.w0 ⟨_, el, ac, c⟩) y)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
