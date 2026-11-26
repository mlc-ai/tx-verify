-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.WalkVal
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The index warp's obligations in its main loop

Per block of the main cache: the next pair's load (`pf`, any payload), the wait on the slot's
`valid_coord_free` (`wA`), the two data shuffles (`sA1`, `sA2`), the coordinate pair's store
(`stA`), the validity byte (`bA`) and the arrival on `valid_coord_ready` (`arrA`), then the
block's end (`walk_endA`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

theorem stepAt_pf (d : D) (hs : d.site = .pf) : (code P L g).StepAtU d := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  refine pairAt (nf := fun y0 y1 => ofC (.wA, { c with n0 := y0, n1 := y1 })) (pc := 2429)
    (r0 := 2976) (r1 := 2975) rfl rfl rfl Flow.code_2429 rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => rfl) fun y => ?_
  exact SegU.comp (b := 2432)
    (G := factsFrom (ixLive 2432)
      (ixVal P L g { c with n0 := D.w0 ⟨_, el, ac, c⟩, n1 := y })) (by ix_seg)
    (ixu_head _)

theorem stepAt_wA (d : D) (hs : d.site = .wA) : (code P L g).StepAtU d := by
  ix_site
  exact pollAt (s := .sA1) (pc := 2446) rfl Flow.code_2446 Flow.code_2447 Flow.code_2448
    (by decide +kernel) rfl (fun m q ok sc' => by cases ok <;> rfl)
    (ixu_val c)

theorem stepAt_sA1 (d : D) (hs : d.site = .sA1) : (code P L g).StepAtU d := by
  ix_site
  refine Code.step_shflU (C := code P L g)
    (nv := fun r _ => some (some ⟨.sA2, 0, ac, { c with rv1 := r }⟩))
    Flow.code_2464
    (not_mem_factsFrom (live := ixLive 2464) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2464) (by decide +kernel)) (by decide)
    (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ _ => by simp) (fun recv ok d' h => ?_)
  obtain rfl := Option.some.inj (Option.some.inj h)
  refine ⟨rfl, rfl, IxSite.elems_pos _, ?_⟩
  refine SegU.or_rv_left (pc := 2465) Flow.code_2465 (v := recv)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom_eq (show 605 ∈ ixLive 2464 by decide +kernel) rfl)))
    (by ix_hd) ix_hL (h := ?_)
  ix_seg

theorem stepAt_sA2 (d : D) (hs : d.site = .sA2) : (code P L g).StepAtU d := by
  ix_site
  refine Code.step_shflU (C := code P L g)
    (nv := fun r _ => some (some ⟨.stA, 0, ac, { c with rv2 := r }⟩)) Flow.code_2467
    (not_mem_factsFrom (live := ixLive 2467) (by decide +kernel))
    (not_mem_factsFrom (live := ixLive 2467) (by decide +kernel)) (by decide)
    (fun _ _ _ _ _ _ => rfl) rfl rfl (fun _ _ => by simp) (fun recv ok d' h => ?_)
  obtain rfl := Option.some.inj (Option.some.inj h)
  refine ⟨rfl, rfl, IxSite.elems_pos _, ?_⟩
  refine SegU.or_rv_right (pc := 2468) Flow.code_2468 (v := recv)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom_eq (show 608 ∈ ixLive 2467 by decide +kernel) rfl)))
    (by ix_hd) ix_hL (h := ?_)
  ix_seg

/-- After the coordinate pair: the validity byte or the arrival, by the lane's test. -/
theorem stA_seg (c : IxCtl) :
    SegU kernel Assumptions.all L g 2472 (ixFacts P L g c .stA)
      (afterSt L g .bA .arrA).pc (ixFacts P L g c (afterSt L g .bA .arrA)) := by
  cases hk : ixSkipB L g
  · rw [show afterSt L g .bA .arrA = .bA by unfold afterSt; rw [hk]; rfl]
    ix_br 2472 20 (ixSkipB L g) c Flow.code_2472
    rw [hk]; ix_seg
  · rw [show afterSt L g .bA .arrA = .arrA by unfold afterSt; rw [hk]; rfl]
    ix_br 2472 20 (ixSkipB L g) c Flow.code_2472
    rw [hk]; ix_seg

theorem stepAt_stA (d : D) (hs : d.site = .stA) : (code P L g).StepAtU d := by
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  exact stAt (n := ofC (afterSt L g .bA .arrA, c)) (pc := 2471) rfl rfl rfl Flow.code_2471
    rfl rfl rfl (fun _ => rfl) rfl (by unfold afterSt; split <;> rfl) (stA_seg c)

theorem stepAt_bA (d : D) (hs : d.site = .bA) : (code P L g).StepAtU d := by
  ix_site
  exact Code.scalarStoreU (C := code P L g) (dn := ⟨.arrA, 0, ac, c⟩) Flow.code_2474 rfl rfl rfl
    (fun _ => rfl) rfl rfl rfl rfl (IxSite.elems_pos _) (by ix_seg)

theorem stepAt_arrA (d : D) (hs : d.site = .arrA) : (code P L g).StepAtU d := by
  ix_site
  ix_adv Flow.code_2476 to (ofC (mainEnd c)) by exact Code.fires_arrive_next hf
  exact walk_endA c

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
