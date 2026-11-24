-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainRs2
public import Lemmas.Flow.SegJump

@[expose] public section

/-! # Segment computing the plain round's row sum

The two generated runs and the zero move reach the plain loop decision. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The move of `0` at pc 7467, from any facts it does not touch. -/
theorem mov7467 {F : List (Nat × Value)}
    (hk : freshKeys [(5806, .bits 32 (BitVec.ofNat 64 0))] F = true) :
    ∃ n, Seg kernel Assumptions.all L g n 7467 F 7468
      ((5806, .bits 32 (BitVec.ofNat 64 0)) :: F) :=
  Seg.writes Flow.code_7467 rfl (fun R cf _ => by
    rw [execLocalA_core (fun t _ a ha => by
        simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      (Gen.segFree 7467 (by decide)) rfl]
    rfl) hk

/-- The facts the row sum carries: the round's maximum, `%r170` and the control registers. -/
def ctlPE : List Nat :=
  [441, 1062, 1069, 1215, 2390, 2535, 5127, 6495, 6497, 7133, 7253, 7254, 7258, 7500, 7501, 7502,
   7503, 7506, 8692]

abbrev pwH (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  (7256, maxP p v) :: (1230, negS p) :: factsFrom ctlPE (valueOf p L g ⟨.pwend .plain, v, 0, []⟩)

theorem pP_7256 (v : V) : lookupD (pPData p v) 7256 = maxP p v := by kernel_rfl
theorem pP_1230 (v : V) : lookupD (pPData p v) 1230 = negS p := by kernel_rfl

/-- On the P part's keys the state's values are the table's. -/
theorem pw_val (v : V) {r : Nat} (hr : r ∈ (pPData p v).map Prod.fst) :
    valueOfD p L g ⟨.pwend .plain, v, 0, []⟩ r = lookupD (pPData p v) r := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  have hnd : ((pPData p v).map Prod.fst).Nodup := nodup_of_nodupB (by kernel_rfl)
  rw [valueOfD_prefix (G := pPData p v) (X := []) (by simp; rfl) hnd q hq]
  have := lookup_prefix (X := []) hnd hq
  simp only [List.append_nil] at this
  simp only [lookupD, this, Option.getD_some]

/-- **The row sum** from the successful poll's branch target to pc 7599. -/
theorem pw_rs (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7466
    ((9886, .pred true) :: factsD p L g ⟨.pwend .plain, v, 0, []⟩) 7599
    ((7257, .float .f32 (rsPG p v)) :: pwH p L g v) := by
  have hfa := SegD.frame (H := pwH p L g v) Gen.rulesFrame
    (Gen.rsumPa_run L g (lookupD (pPData p v)))
    rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  have hfb := SegD.frame (H := pwH p L g v) Gen.rulesFrame (Gen.rsumPb_run L g (rbV p v))
    rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  refine Seg.comp_ex (seg_of_segD (hfa.weaken_start fun R hR => ?_) (rsumPa_ok hp v).1) ?_
  · have hR' := hR.2
    have hval : ∀ r ∈ (pPData p v).map Prod.fst, r ∈ liveD (livePc ⟨.pwend .plain, v, 0, []⟩) →
        R r = some (lookupD (pPData p v) r) := fun r h1 h2 => by
      rw [← pw_val v h1]; exact holds_mem hR' (mem_factsFrom h2)
    refine (holds_append _ _ _).mpr ⟨?_, ?_⟩
    · rw [rsumPa_facts0_eq]
      refine holds_of_pointwise fun r hr => ?_
      have hk : ((Gen.rsumPa_facts0 (lookupD (pPData p v))).map Prod.fst).all (fun r =>
          ((pPData p v).map Prod.fst).contains r &&
            (liveD (livePc ⟨.pwend .plain, v, 0, []⟩)).contains r) = true := by
        kernel_rfl
      have h := List.all_eq_true.mp hk r hr
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      exact hval r h.1 h.2
    · refine ⟨?_, ?_, ?_⟩
      · rw [← pP_7256]
        exact hval 7256 (mem_of_contains (by kernel_rfl)) (mem_of_contains (by kernel_rfl))
      · rw [← pP_1230]
        exact hval 1230 (mem_of_contains (by kernel_rfl)) (mem_of_contains (by kernel_rfl))
      · refine holds_of_pointwise fun r hr => ?_
        have hc : ctl r = true := by
          have h : ctlPE.all ctl = true := by kernel_rfl
          exact List.all_eq_true.mp h r hr
        rw [← valueOfD_ctl _ hc]
        exact holds_mem hR' (mem_factsFrom (List.contains_iff_mem.mp (List.all_eq_true.mp
          (by kernel_rfl : ctlPE.all ((liveD (livePc ⟨.pwend .plain, v, 0, []⟩)).contains ·) =
            true) r hr)))
  refine Seg.comp_ex (mov7467 (by kernel_rfl)) ?_
  refine seg_of_segD (hfb.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_)
    (rsumPb_ok hp v).1
  · obtain ⟨h0, h1⟩ := hR
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp h1
    refine (holds_append _ _ _).mpr ⟨?_, h2⟩
    rw [rsumPb_facts0_eq]
    exact holds_lookupD (F := (5806, .bits 32 (BitVec.ofNat 64 0)) ::
      Gen.rsumPa_facts1 (lookupD (pPData p v))) ⟨h0, h1⟩ (by kernel_rfl)
  · obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    refine ⟨?_, h2⟩
    have := h1.1
    rw [rsP_float hp v] at this
    exact this

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
