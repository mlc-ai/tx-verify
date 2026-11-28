-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StepsExtra
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictStepsMain
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Every state of the index warp steps strictly

`Index.stepQ`: the strict obligation under the tag invariant (`Code.StepForQ (QT ixQt) (IxWf P)`)
of every state of the index machine that satisfies `IxInv`, by its site. -/

/-! # The index warp's strict steps: the extra loop and the end

`stepQ_xpre` .. `stepQ_exit`: the strict obligations of the extra cache's first pair (whose
`div.u32` by the page size is defined: `ix_hz`), the extra loop's wait, shuffles, stores,
arrival, and the barrier and the return, as the `stepAt_*` of `Index/StepsExtra.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepQ_xpre (hp : Pre P L m) (hP : Plain L g) (d : D) (hs : d.site = .xpre)
    (hi : IxInv P d) (e : Event) : (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  have hz := ix_hz hp hs hi
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  intro t u ins hat hinv hc hq hw hf
  exact pairQ (nf := fun y0 y1 => ofC (afterXpre L g { c with e0 := y0, e1 := y1 }))
    (pc := 2501) (r0 := 2982) (r1 := 2981) rfl rfl rfl Flow.code_2501 rfl rfl rfl rfl rfl rfl
    rfl rfl (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl)
    (by decide +kernel) (fun y => qk_xentry hP c (D.w0 ⟨_, el, ac, c⟩) y hz) e ins hat hinv hc hq
    hw hf

theorem stepQ_xpf (hP : Plain L g) (d : D) (hs : d.site = .xpf) (hi : IxInv P d) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  refine pairQ (nf := fun y0 y1 => ofC (.wB, { c with f0 := y0, f1 := y1 })) (pc := 2517)
    (r0 := 2984) (r1 := 2983) rfl rfl rfl Flow.code_2517 rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl) (by decide +kernel)
    (fun y => ?_) e
  exact SegQ.comp (b := 2520)
    (G := factsFrom (ixLive 2520)
      (ixVal P L g { c with f0 := D.w0 ⟨_, el, ac, c⟩, f1 := y })) (by ixq_seg) (qk_xhead hP _)

theorem stepQ_wB (hP : Plain L g) (d : D) (hs : d.site = .wB) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  exact pollQ (s := .sB1) (pc := 2534) rfl Flow.code_2534 Flow.code_2535 Flow.code_2536
    (by decide +kernel) rfl (fun m q ok sc' => by cases ok <;> rfl) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qk_xval hP c) e

theorem stepQ_sB1 (hP : Plain L g) (d : D) (hs : d.site = .sB1) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.shflRecvQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.sB1, 0, ac, c⟩) (dn := fun y => ⟨.sB2, 0, ac, { c with rv1 := .bits 32 y }⟩)
    Flow.code_2553
    (not_mem_factsFrom (live := ixLive 2553) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2553) (by decide +kernel)) (by decide)
    (fun e he => he.shfl) (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2553 _ = _; decide +kernel)
    (fun _ _ => by ixq_seg) e ins hat hinv hc hq hw hf

theorem stepQ_sB2 (hP : Plain L g) (d : D) (hs : d.site = .sB2) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.shflRecvQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.sB2, 0, ac, c⟩) (dn := fun y => ⟨.stB, 0, ac, { c with rv2 := .bits 32 y }⟩)
    Flow.code_2556
    (not_mem_factsFrom (live := ixLive 2556) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2556) (by decide +kernel)) (by decide)
    (fun e he => he.shfl) (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2556 _ = _; decide +kernel)
    (fun _ _ => by ixq_seg) e ins hat hinv hc hq hw hf

/-- After the coordinate pair: the validity byte or the arrival, by the lane's test. -/
theorem qstB_seg (hP : Plain L g) (c : IxCtl) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2561 (ixFacts P L g c .stB)
      (afterSt L g .bB .arrB).pc (ixFacts P L g c (afterSt L g .bB .arrB)) := by
  cases hk : ixSkipB L g
  · rw [show afterSt L g .bB .arrB = .bB by unfold afterSt; rw [hk]; rfl]
    ixq_br 2561 35 (ixSkipB L g) c Flow.code_2561 with hk
    ixq_seg
  · rw [show afterSt L g .bB .arrB = .arrB by unfold afterSt; rw [hk]; rfl]
    ixq_br 2561 35 (ixSkipB L g) c Flow.code_2561 with hk
    ixq_seg

theorem stepQ_stB (hP : Plain L g) (d : D) (hs : d.site = .stB) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact stQ (n := ofC (afterSt L g .bB .arrB, c)) (pc := 2560) rfl rfl rfl Flow.code_2560
    rfl rfl (fun _ => rfl) rfl (by unfold afterSt; split <;> rfl) (by decide +kernel)
    (qstB_seg hP c) e

theorem stepQ_bB (hP : Plain L g) (d : D) (hs : d.site = .bB) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.scalarStoreQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.bB, 0, ac, c⟩) (dn := ⟨.arrB, 0, ac, c⟩) Flow.code_2563 rfl rfl (fun _ => rfl)
    rfl rfl rfl rfl (IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2563 _ = _; decide +kernel) (by ixq_seg) e
    ins hat hinv hc hq hw hf

theorem stepQ_arrB (hP : Plain L g) (d : D) (hs : d.site = .arrB) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.advanceQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.arrB, 0, ac, c⟩) (dn := ofC (xEnd c)) Flow.code_2565
    (fun hf => Code.fires_arrive_next hf) (fun _ => rfl) rfl rfl rfl rfl
    (IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2565 _ = _; decide +kernel) (qk_endB hP c) e
    ins hat hinv hc hq hw hf

/-- The return's table is among the barrier's live registers. -/
theorem qk_toExit (c : IxCtl) {a : Nat} (h : ∀ r ∈ ixLive 3611, r ∈ ixLive a) :
    SegQ kernel Assumptions.all L g (QT ixQt) 3611 (factsFrom (ixLive a) (ixVal P L g c))
      3611 (factsFrom (ixLive 3611) (ixVal P L g c)) :=
  segq_weaken fun R hR => holds_of_pointwise fun r hr => by
    rw [holds_mem hR (mem_factsFrom (h r hr))]

theorem stepQ_bar (d : D) (hs : d.site = .bar) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  ixq_site
  intro t u ins hat hinv hc hq hw hf
  refine Code.advanceQ (C := code P L g) (qt := ixQt) (ex := []) (Wf := IxWf P)
    (d := ⟨.bar, 0, ac, c⟩) (dn := ⟨.exit, 0, ac, c⟩) Flow.code_2585
    (fun hf => fires_barSyncN_next hf) (fun _ => rfl) rfl rfl rfl rfl
    (IxSite.elems_pos _) (fun _ _ => typed_nil)
    (by show Code.afterWrites ixQt 2585 _ = _; decide +kernel) ?_ e ins hat hinv hc hq hw hf
  exact SegQ.comp (SegQ.jmp Flow.code_2586 (fun t _ => bra_rule t) noSegments.segFreePc
    (by show tagsIn (ixQt 3611) (ixQt 2586) = true; decide +kernel))
    (qk_toExit c (a := 2585) (by decide +kernel))

/-- The return ends the thread: no step reaches a state. -/
theorem stepQ_exit (d : D) (hs : d.site = .exit) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  have hp : (code P L g).pc d = 3611 := by show d.site.pc = 3611; rw [hs]; rfl
  intro t u ins _ _ hc _ _ hf
  rw [hp, Flow.code_3611] at hc
  obtain rfl := Option.some.inj hc
  simp [eventTmpl, Fires] at hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **Every state of the index warp that satisfies the invariant steps strictly.** -/
theorem stepQ (hp : Pre P L m) (d : D) (hi : IxInv P d) (e : Event) :
    (code P L g).StepForQ (QT ixQt) (IxWf P) d e := by
  have hP : Plain L g := Plain.mk'
  intro t u ins hat hinv hc hq hw hf
  cases hs : d.site
  · exact stepQ_lenA (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_lenB (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_pre (P := P) hP d hs hi e ins hat hinv hc hq hw hf
  · exact stepQ_pf (P := P) hP d hs hi e ins hat hinv hc hq hw hf
  · exact stepQ_wA (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_sA1 (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_sA2 (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_stA (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_bA (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_arrA (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_xpre (P := P) hp hP d hs hi e ins hat hinv hc hq hw hf
  · exact stepQ_xpf (P := P) hP d hs hi e ins hat hinv hc hq hw hf
  · exact stepQ_wB (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_sB1 (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_sB2 (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_stB (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_bB (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_arrB (P := P) hP d hs e ins hat hinv hc hq hw hf
  · exact stepQ_bar (P := P) d hs e ins hat hinv hc hq hw hf
  · exact stepQ_exit (P := P) d hs e ins hat hinv hc hq hw hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
