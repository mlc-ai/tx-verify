-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKB
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBK8
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE1
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
import Kernels.TmlFa4Fwd.Proof.Softmax.Base

@[expose] public section

/-! # A bias round's exponent stretch: the software path

From the branch at pc 5815 (the round index below `%r301`) to the first P store: the software
path (`expoBB_seg`, its runs carrying the control registers), the store addresses and the tail. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem expoBB8_facts1_eq (U : Nat → Value) : Gen.expoBB8_facts1 U =
    factsFrom ((Gen.expoBB8_facts1 fun _ => .pred false).map Prod.fst)
      (lookupD (Gen.expoBB8_facts1 U)) := by kernel_rfl

/-- The software path carries the control registers. -/
theorem ctlB_eq (U : Nat → Value) :
    factsFrom (ctlLive 6299) (lookupD (Gen.expoBB8_facts1 (vB8 (lookupD (Gen.expoB0_facts5 U))))) =
      factsFrom (ctlLive 6299) U := by kernel_rfl

/-- **The software path** from the branch at pc 5815 to the first P store. -/
theorem narrB_pathB (hp : Pre p L m) (v : V)
    (hc : Epilogue.scmp .lt .u v.bt (r301 p L g v) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 5815
      (Gen.expoB0_facts5 (valueOfD p L g (narrB v))) 6508 (factsD p L g (pstB0 v)) := by
  have hT := tailB_ok (g := g) v (bb8_kinds hp v)
  -- the branch
  have hb : Seg kernel Assumptions.all L g 1 5815 (Gen.expoB0_facts5 (valueOfD p L g (narrB v)))
      5977 (Gen.expoB0_facts5 (valueOfD p L g (narrB v))) :=
    Seg.bra (pick := true) Flow.code_5815 (hc ▸ mem634 v) (braFree _ _ _)
      (Gen.segFree _ (by kernel_rfl))
  refine Seg.comp_ex ⟨1, hb⟩ ?_
  -- the software path, 5977 to 6299 (its runs carry the control registers)
  obtain ⟨_, s⟩ := expoBB_seg (L := L) (g := g) (vExpoB p L g v) (bb0_k0 hp v)
  refine Seg.comp_ex ⟨_, s.weaken_start fun R hR => by
    rw [expoBB0_facts0_eq]; rw [expoB0_facts5_eq] at hR; exact holds_sub hR (by kernel_rfl)⟩ ?_
  have hEnd : Gen.expoBB8_facts1 (vB8 (vExpoB p L g v)) =
      factsFrom ((Gen.expoBB8_facts1 fun _ => .pred false).map Prod.fst) (vTB p L g v) :=
    expoBB8_facts1_eq _
  have hCtl : factsFrom (ctlLive 6299) (vTB p L g v) =
      factsFrom (ctlLive 6299) (valueOfD p L g (narrB v)) := ctlB_eq _
  rw [hEnd]
  -- 6299 to 6308: the store addresses
  have w := seg_frame (lo := 6299) (hi := 6508)
    (H := factsFrom ((Gen.expoBB8_facts1 fun _ => .pred false).map Prod.fst) (vTB p L g v))
    (ctlTail (g := g) hp v) (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex (seg_start_ex w fun R hR => by
    refine (holds_append _ _ _).mpr ⟨?_, hR⟩
    rw [← hCtl]
    exact holds_sub hR (by kernel_rfl)) ?_
  -- the tail's first run, 6308 to 6380
  have t0 := seg_frame (lo := 6308) (hi := 6508)
    (H := factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v)))
    (seg_of_segD (Gen.expoBTB0_run L g (vTB p L g v)) hT.1)
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex (seg_start_ex t0 fun R hR => by
    obtain ⟨h2, h1⟩ := (holds_append _ _ _).mp hR
    refine (holds_append _ _ _).mpr ⟨?_, h2⟩
    rw [expoBTB0_facts0_eq]
    exact holds_sub h1 (by kernel_rfl)) ?_
  -- the unpack at 6380
  have hk9 : isPr (kOf tBa3 9556) = true := by decide +kernel
  have u := seg_frame (lo := 6380) (hi := 6508)
    (H := factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v)))
    (seg6380B (L := L) (g := g) (vTB p L g v) (unpack_of_isPr (hT.2.1 9556) hk9))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex u ?_
  -- the tail's second run, 6381 to 6508
  have t1 := seg_frame (lo := 6381) (hi := 6508)
    (H := factsFrom (ctlLive 6308) (valueOfD p L g (pstB0 v)))
    (seg_of_segD (Gen.expoBTB1_run L g (nextTB (vTB p L g v))) hT.2.2.1)
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex t1 ⟨0, Seg.refl _ _ |>.weaken_end fun R hR => ?_⟩
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
  have hd : valuesData p L g (pstB0 v) = Gen.expoBTB1_facts4 (nextTB (vTB p L g v)) ++
      (halvesB (tailB p L g v) ++ valuesRun p v ++ valuesBiasM p v) := by
    simp only [valuesData, pBData, tailB, vTailB, hc, Bool.cond_true]
    rfl
  exact land_run (valueOfD_prefix (d := pstB0 v) hd (nodup_of_nodupB (by kernel_rfl)))
    (valueOfD_ctl_eq (ctlK := ctlLive 6308) rfl (by kernel_rfl))
    (live := liveD 6508) (by kernel_rfl) h1 h2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
