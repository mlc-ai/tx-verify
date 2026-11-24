-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKA
public import Lemmas.Flow.SegJump
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand

@[expose] public section

/-! # A bias round's exponent stretch: the hardware path

From the branch at pc 5815 (the round index at or above `%r301`) to the first P store
(`pst .bias 0`, pc 6508): the hardware path and its jump, the store addresses, the tail's two runs
around the unpack at pc 6380, landing on the first P store's table (`pBData`). The scaled-product
run and the hardware path's run carry the control registers, so nothing is framed across a
branch. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The first P store's state. -/
abbrev pstB0 (v : V) : D := ⟨.pst .bias 0, v, 0, []⟩

/-- No assumption has a local rule at a branch. -/
theorem braFree (pc tgt : Nat) (uni : Bool) : ∀ (t : TState), t.pc = pc →
    ∀ a ∈ Assumptions.all, a.localRule L g t (.bra tgt uni) = none := by
  intro t _ a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem expoB0_facts5_eq (U : Nat → Value) : Gen.expoB0_facts5 U =
    factsFrom ((Gen.expoB0_facts5 fun _ => .pred false).map Prod.fst)
      (lookupD (Gen.expoB0_facts5 U)) := by kernel_rfl

theorem lookup634 (U : Nat → Value) : (Gen.expoB0_facts5 U).lookup 634 = some (U 634) := by
  kernel_rfl

/-- `%p632`, the branch's predicate, in the scaled-product run's end facts. -/
theorem mem634 (v : V) : (634, Value.pred (Epilogue.scmp .lt .u v.bt (r301 p L g v))) ∈
    Gen.expoB0_facts5 (valueOfD p L g (narrB v)) :=
  mem_of_lookup (lookup634 _)

/-- The store addresses (pcs 6299 to 6307). -/
theorem ctlTail (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 6299
    (factsFrom (ctlLive 6299) (valueOfD p L g (narrB v))) 6308
    (factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v))) := by
  have hparams := params hp
  seg_sym using (soft_seg)

theorem expoBA_facts5_eq (U : Nat → Value) : Gen.expoBA_facts5 U =
    factsFrom ((Gen.expoBA_facts5 fun _ => .pred false).map Prod.fst)
      (lookupD (Gen.expoBA_facts5 U)) := by kernel_rfl

/-- The hardware path carries the control registers. -/
theorem ctlA_eq (U : Nat → Value) :
    factsFrom (ctlLive 6299) (lookupD (Gen.expoBA_facts5 (lookupD (Gen.expoB0_facts5 U)))) =
      factsFrom (ctlLive 6299) U := by kernel_rfl

/-- **The hardware path** from the branch at pc 5815 to the first P store. -/
theorem narrB_pathA (hp : Pre p L m) (v : V)
    (hc : Epilogue.scmp .lt .u v.bt (r301 p L g v) = false) :
    ∃ n, Seg kernel Assumptions.all L g n 5815
      (Gen.expoB0_facts5 (valueOfD p L g (narrB v))) 6508 (factsD p L g (pstB0 v)) := by
  have hT := tailA_ok (g := g) hp v
  -- the branch
  have hb : Seg kernel Assumptions.all L g 1 5815 (Gen.expoB0_facts5 (valueOfD p L g (narrB v)))
      5816 (Gen.expoB0_facts5 (valueOfD p L g (narrB v))) :=
    Seg.bra (pick := false) Flow.code_5815 (hc ▸ mem634 v) (braFree _ _ _)
      (Gen.segFree _ (by kernel_rfl))
  refine Seg.comp_ex ⟨1, hb⟩ ?_
  -- the hardware path, 5816 to 5976, and its jump to 6299
  refine Seg.comp_ex ⟨_, (seg_of_segD (Gen.expoBA_run L g (vExpoB p L g v))
    (expoBA_ok (g := g) hp v).1).choose_spec.weaken_start fun R hR => by
      rw [expoBA_facts0_eq]; rw [expoB0_facts5_eq] at hR; exact holds_sub hR (by kernel_rfl)⟩ ?_
  refine Seg.comp_ex ⟨1, seg_jmp (L := L) (g := g)
    (F := Gen.expoBA_facts5 (vExpoB p L g v)) Flow.code_5976 (braFree _ _ _)
    (Gen.segFree _ (by kernel_rfl))⟩ ?_
  have hEnd : Gen.expoBA_facts5 (vExpoB p L g v) =
      factsFrom ((Gen.expoBA_facts5 fun _ => .pred false).map Prod.fst) (vTA p L g v) :=
    expoBA_facts5_eq _
  have hCtl : factsFrom (ctlLive 6299) (vTA p L g v) =
      factsFrom (ctlLive 6299) (valueOfD p L g (narrB v)) := ctlA_eq _
  rw [hEnd]
  -- 6299 to 6308: the store addresses
  have w := seg_frame (lo := 6299) (hi := 6508)
    (H := factsFrom ((Gen.expoBA_facts5 fun _ => .pred false).map Prod.fst) (vTA p L g v))
    (ctlTail (g := g) hp v) (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex (seg_start_ex w fun R hR => by
    refine (holds_append _ _ _).mpr ⟨?_, hR⟩
    rw [← hCtl]
    exact holds_sub hR (by kernel_rfl)) ?_
  -- the tail's first run, 6308 to 6380
  have t0 := seg_frame (lo := 6308) (hi := 6508)
    (H := factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v)))
    (seg_of_segD (Gen.expoBTA0_run L g (vTA p L g v)) hT.1)
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex (seg_start_ex t0 fun R hR => by
    obtain ⟨h2, h1⟩ := (holds_append _ _ _).mp hR
    refine (holds_append _ _ _).mpr ⟨?_, h2⟩
    rw [expoBTA0_facts0_eq]
    exact holds_sub h1 (by kernel_rfl)) ?_
  -- the unpack at 6380
  have hk9 : isPr (kOf tAa3 9556) = true := by decide +kernel
  have u := seg_frame (lo := 6380) (hi := 6508)
    (H := factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v)))
    (seg6380A (L := L) (g := g) (vTA p L g v) (unpack_of_isPr (hT.2.1 9556) hk9))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex u ?_
  -- the tail's second run, 6381 to 6508
  have t1 := seg_frame (lo := 6381) (hi := 6508)
    (H := factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v)))
    (seg_of_segD (Gen.expoBTA1_run L g (nextTA (vTA p L g v))) hT.2.2.1)
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex t1 ⟨0, Seg.refl _ _ |>.weaken_end fun R hR => ?_⟩
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
  have hd : valuesData p L g (pstB0 v) = Gen.expoBTA1_facts4 (nextTA (vTA p L g v)) ++
      (halvesB (tailB p L g v) ++ valuesRun p v ++ valuesBiasM p v) := by
    simp only [valuesData, pBData, tailB, vTailB, hc, Bool.cond_false]
    rfl
  exact land_run (valueOfD_prefix (d := pstB0 v) hd (nodup_of_nodupB (by kernel_rfl)))
    (valueOfD_ctl_eq (ctlK := ctlLive 6308) rfl (by kernel_rfl))
    (live := liveD 6508) (by kernel_rfl) h1 h2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
