-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.WalkVal
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The index warp's obligations in its extra loop and at its end

The extra cache's blocks, the same sites as the main loop's (`xpf`, `wB`, `sB1`, `sB2`, `stB`,
`bB`, `arrB`), then named barrier 12 (`bar`) and the return (`exit`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

theorem stepAt_xpf (d : D) (hs : d.site = .xpf) : (code P L g).StepAtU d := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  refine pairAt (nf := fun y0 y1 => ofC (.wB, { c with f0 := y0, f1 := y1 })) (pc := 2517)
    (r0 := 2984) (r1 := 2983) rfl rfl rfl Flow.code_2517 rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl) fun y => ?_
  exact SegU.comp (b := 2520)
    (G := factsFrom (ixLive 2520)
      (ixVal P L g { c with f0 := D.w0 ⟨_, el, ac, c⟩, f1 := y })) (by ix_seg)
    (ixu_xhead _)

theorem stepAt_wB (d : D) (hs : d.site = .wB) : (code P L g).StepAtU d := by
  ix_site
  exact pollAt (s := .sB1) (pc := 2534) rfl Flow.code_2534 Flow.code_2535 Flow.code_2536
    (by decide +kernel) rfl (fun m q ok sc' => by cases ok <;> rfl)
    (ixu_xval c)

theorem stepAt_sB1 (d : D) (hs : d.site = .sB1) : (code P L g).StepAtU d := by
  ix_site
  refine Code.step_shflU (C := code P L g)
    (nv := fun r _ => some (some ⟨.sB2, 0, ac, { c with rv1 := r }⟩)) Flow.code_2553
    (not_mem_factsFrom (live := ixLive 2553) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2553) (by decide +kernel)) (by decide)
    (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ _ => by simp) (fun recv ok d' h => ?_)
  obtain rfl := Option.some.inj (Option.some.inj h)
  refine ⟨rfl, rfl, IxSite.elems_pos _, ?_⟩
  refine SegU.or_rv_left (pc := 2554) Flow.code_2554 (v := recv)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom_eq (show 644 ∈ ixLive 2553 by decide +kernel) rfl)))
    (by ix_hd) ix_hL (h := ?_)
  ix_seg

theorem stepAt_sB2 (d : D) (hs : d.site = .sB2) : (code P L g).StepAtU d := by
  ix_site
  refine Code.step_shflU (C := code P L g)
    (nv := fun r _ => some (some ⟨.stB, 0, ac, { c with rv2 := r }⟩)) Flow.code_2556
    (not_mem_factsFrom (live := ixLive 2556) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2556) (by decide +kernel)) (by decide)
    (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ _ => by simp) (fun recv ok d' h => ?_)
  obtain rfl := Option.some.inj (Option.some.inj h)
  refine ⟨rfl, rfl, IxSite.elems_pos _, ?_⟩
  refine SegU.or_rv_right (pc := 2557) Flow.code_2557 (v := recv)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom_eq (show 647 ∈ ixLive 2556 by decide +kernel) rfl)))
    (by ix_hd) ix_hL (h := ?_)
  ix_seg

/-- After the coordinate pair: the validity byte or the arrival, by the lane's test. -/
theorem stB_seg (c : IxCtl) :
    SegU kernel Assumptions.all L g 2561 (ixFacts P L g c .stB)
      (afterSt L g .bB .arrB).pc (ixFacts P L g c (afterSt L g .bB .arrB)) := by
  cases hk : ixSkipB L g
  · rw [show afterSt L g .bB .arrB = .bB by unfold afterSt; rw [hk]; rfl]
    ix_br 2561 35 (ixSkipB L g) c Flow.code_2561
    rw [hk]; ix_seg
  · rw [show afterSt L g .bB .arrB = .arrB by unfold afterSt; rw [hk]; rfl]
    ix_br 2561 35 (ixSkipB L g) c Flow.code_2561
    rw [hk]; ix_seg

theorem stepAt_stB (d : D) (hs : d.site = .stB) : (code P L g).StepAtU d := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact stAt (n := ofC (afterSt L g .bB .arrB, c)) (pc := 2560) rfl rfl rfl Flow.code_2560
    rfl rfl rfl (fun _ => rfl) rfl (by unfold afterSt; split <;> rfl) (stB_seg c)

theorem stepAt_bB (d : D) (hs : d.site = .bB) : (code P L g).StepAtU d := by
  ix_site
  exact Code.scalarStoreU (C := code P L g) (dn := ⟨.arrB, 0, ac, c⟩) Flow.code_2563 rfl rfl rfl
    (fun _ => rfl) rfl rfl rfl rfl (IxSite.elems_pos _) (by ix_seg)

theorem stepAt_arrB (d : D) (hs : d.site = .arrB) : (code P L g).StepAtU d := by
  ix_site
  ix_adv Flow.code_2565 to (ofC (xEnd c)) by exact Code.fires_arrive_next hf
  exact walk_endB c

theorem stepAt_bar (d : D) (hs : d.site = .bar) : (code P L g).StepAtU d := by
  ix_site
  ix_adv Flow.code_2585 to ⟨.exit, 0, ac, c⟩ by exact fires_barSyncN_next hf
  exact SegU.comp (SegU.of_seg (seg_jmp Flow.code_2586 (fun t _ => bra_rule t)
    noSegments.segFreePc)) (by ix_seg)

/-- The return ends the thread: no step reaches a state. -/
theorem stepAt_exit (d : D) (hs : d.site = .exit) : (code P L g).StepAtU d := by
  have hp : (code P L g).pc d = 3611 := by show d.site.pc = 3611; rw [hs]; rfl
  refine ⟨fun _ => ⟨⟨none, .ret⟩, by rw [hp]; exact Flow.code_3611, rfl, trivial⟩,
    fun ins _ _ hc hf => ?_⟩
  rw [hp, Flow.code_3611] at hc
  obtain rfl := Option.some.inj hc
  simp [eventTmpl, Fires] at hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
