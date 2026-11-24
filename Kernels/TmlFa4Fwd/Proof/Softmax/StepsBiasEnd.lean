-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasSum
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasMaxValue
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailBranch
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailPlain
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailFinal
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailLoop
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.SegJump

@[expose] public section

/-! # A bias round's closing poll -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

private theorem pwB_after (hp : Pre p L m) (v : V) (b : Bool) (r x : ℝ) (take : Bool)
    (h : scmpi .ne .b (addi v.nb 1) (-1) = take) :
    ∃ n, Seg kernel Assumptions.all L g n 6647
      ((7257, .float .f32 x) :: pwBH p L g v (mxVal (biasTailV v b r x)))
      (if take then 5032 else 6654) (pwBBranch p L g v b r x) := by
  refine Seg.comp_ex (pwB_branch hp v b r x) ⟨1, ?_⟩
  refine Seg.bra Flow.code_6653 ?_ (braFree _ _ _) (Gen.segFree _ (by kernel_rfl))
  exact h ▸ List.mem_cons_self

/-- The closing poll either retries or updates the row statistics and enters its next round. -/
theorem stepAt_pwendB (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt (pwB v) := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_wait (dok := afterBias p L g (pwB v)) (dfail := pwB v)
    Flow.code_6558 (by fact_free) (fun _ _ _ _ => by next_simp [succ, afterRound])
    (fun _ _ _ _ => by next_simp [succ]) rfl rfl ?_ ?_
  · let b := finE (maxB p v)
    let r := (maxB p v).toReal
    let x := rsB p L g v
    have hSeg := Seg.comp_ex
      ⟨1, Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (uni := true)
        (pick := true) (F := (9820, .pred true) :: factsD p L g (pwB v)) Flow.code_6559
        List.mem_cons_self (braFree _ _ _) (Gen.segFree _ (by kernel_rfl))⟩ (pwB_rs hp v)
    rw [← mxVal_maxB v x] at hSeg
    change Code.Lands (codeD p L g) (pwB v) 6559 _ (D.ite (scmpi .ne .b (addi v.nb 1) (-1))
      (D.mk' (.ws .bias) { biasTailV v b r x with bt := addi v.bt (-1) })
      (plainEntry p L g (biasTailV v b r x)))
    by_cases hb : scmpi .ne .b (addi v.nb 1) (-1) = true
    · unfold D.ite
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
      exact ⟨fun _ => Seg.comp_ex hSeg (Seg.comp_ex (pwB_after hp v b r x true hb)
        (pwB_loop v b r x)), rfl, rfl,
        fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
    · unfold D.ite
      rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
      unfold plainEntry D.ite
      rw [show r431 p L g (biasTailV v b r x) = r431 p L g v from r431_eq_of rfl rfl]
      by_cases hc : scmpi .lt .s (r431 p L g v) 1 = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        exact ⟨fun _ => Seg.comp_ex hSeg (Seg.comp_ex
            (pwB_after hp v b r x false (Bool.eq_false_iff.mpr hb)) (pwB_fin hp v b r x hc)),
          rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
        exact ⟨fun _ => Seg.comp_ex hSeg (Seg.comp_ex
            (pwB_after hp v b r x false (Bool.eq_false_iff.mpr hb)) (pwB_plain hp v b r x hc)),
          rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  · refine ⟨fun _ => ?_, rfl, rfl, fun h => h⟩
    have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (uni := true)
      (pick := false) (F := (9820, .pred false) :: factsD p L g (pwB v)) Flow.code_6559
      List.mem_cons_self (braFree _ _ _) (Gen.segFree _ (by kernel_rfl))
    have hj := seg_jmp (K := kernel) (A := Assumptions.all) (L := L) (g := g)
      (F := (9820, .pred false) :: factsD p L g (pwB v)) Flow.code_6560 (braFree _ _ _)
      (Gen.segFree _ (by kernel_rfl))
    exact ⟨2, (hb.comp hj).weaken_end fun R hR => hR.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
