-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasRs2
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE2
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand

@[expose] public section

/-! # The successful bias poll's row-sum segment -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The move of `0` at pc 6562, from any facts it does not touch. -/
theorem mov6562 {F : List (Nat × Value)}
    (hk : freshKeys [(5123, .bits 32 (BitVec.ofNat 64 0))] F = true) :
    ∃ n, Seg kernel Assumptions.all L g n 6562 F 6563
      ((5123, .bits 32 (BitVec.ofNat 64 0)) :: F) :=
  Seg.writes Flow.code_6562 rfl (fun R cf _ => by
    rw [execLocalA_core (fun t _ a ha => by
        simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      (Gen.segFree 6562 (by decide)) rfl]
    rfl) hk

theorem pwB_val (v : V) {r : Nat} (hr : r ∈ (pBData p L g v).map Prod.fst) :
    valueOfD p L g (pwB v) r = lookupD (pBData p L g v) r := by
  obtain ⟨x, hx⟩ := lookup_some hr
  change ((pBData p L g v).lookup r).getD _ = lookupD (pBData p L g v) r
  simp only [lookupD, hx, Option.getD_some]

/-- **The row sum** from the successful poll's branch target to pc 6647. -/
theorem pwB_rs (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 6561
    ((9820, .pred true) :: factsD p L g (pwB v)) 6647
    ((7257, .float .f32 (rsB p L g v)) :: pwBH p L g v (lookupD (valuesBiasM p v) 7256)) := by
  have hfa := SegD.frame (H := pwBH p L g v (lookupD (valuesBiasM p v) 7256)) Gen.rulesFrame
    (Gen.rsumBa_run L g (lookupD (pBData p L g v)))
    rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  have hfb := SegD.frame (H := pwBH p L g v (lookupD (valuesBiasM p v) 7256)) Gen.rulesFrame
    (Gen.rsumBb_run L g (rsumBbStart p L g v))
    rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  refine Seg.comp_ex (seg_of_segD (hfa.weaken_start fun R hR => ?_) (rsumBa_ok (g := g) hp v).1) ?_
  · have hR' := hR.2
    have hval : ∀ r ∈ (pBData p L g v).map Prod.fst, r ∈ liveD (livePc (pwB v)) →
        R r = some (lookupD (pBData p L g v) r) := fun r h1 h2 => by
      rw [← pwB_val v h1]; exact holds_mem hR' (mem_factsFrom h2)
    refine (holds_append _ _ _).mpr ⟨?_, ?_⟩
    · rw [rsumBa_facts0_eq]
      let keys := rsumBaKeys
      refine holds_of_pointwise (live := keys) fun r hr => ?_
      have hk : keys.all (fun r =>
          ((pBData p L g v).map Prod.fst).contains r &&
            (liveD (livePc (pwB v))).contains r) = true := by
        kernel_rfl
      have h := List.all_eq_true.mp hk r hr
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      exact hval r h.1 h.2
    · refine ⟨?_, ?_, ?_⟩
      · rw [← pB_max_lookup p L g v]
        exact hval 7256 (mem_of_contains (by kernel_rfl)) (mem_of_contains (by kernel_rfl))
      · rw [← pB_scale_lookup p L g v]
        exact hval 1230 (mem_of_contains (by kernel_rfl)) (mem_of_contains (by kernel_rfl))
      · refine holds_of_pointwise fun r hr => ?_
        have hc : ctl r = true := by
          have h : ctlBE.all ctl = true := by kernel_rfl
          exact List.all_eq_true.mp h r hr
        rw [← valueOfD_ctl _ hc]
        exact holds_mem hR' (mem_factsFrom (List.contains_iff_mem.mp (List.all_eq_true.mp
          (by kernel_rfl : ctlBE.all ((liveD (livePc (pwB v))).contains ·) =
            true) r hr)))
  refine Seg.comp_ex (mov6562 (by kernel_rfl)) ?_
  refine seg_of_segD (hfb.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_)
    (rsumBb_ok (g := g) hp v).1
  · obtain ⟨h0, h1⟩ := hR
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp h1
    refine (holds_append _ _ _).mpr ⟨?_, h2⟩
    rw [rsumBb_facts0_eq]
    exact holds_lookupD (F := (5123, .bits 32 (BitVec.ofNat 64 0)) ::
      Gen.rsumBa_facts1 (lookupD (pBData p L g v))) ⟨h0, h1⟩ (by kernel_rfl)
  · obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    refine ⟨?_, h2⟩
    have := h1.1
    rw [rsB_float (g := g) hp v] at this
    exact this

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
