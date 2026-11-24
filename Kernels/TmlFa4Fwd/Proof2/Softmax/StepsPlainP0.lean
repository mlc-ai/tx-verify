-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainPUnpack

@[expose] public section

/-! # Plain-round probability stores and arrival

The events use the unpack segments to reach the next probability store. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The first P store** of a plain round and the unpacks of the second store's halves. -/
theorem stepAt_pstP_0 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pst .plain 0, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issueAt (dn := D.mk' (.pst .plain 1) v) (by code_lookup)
    (fun hpc hf => fires_tcSt_next (by rw [hpc, Assumptions.all_tcStWaitLd]; rfl) hf)
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  pP_unpack (⟨.pst .plain 0, v, 0, []⟩ : D) (D.mk' (.pst .plain 1) v) Gen.pkPA_run pkPA_facts0_eq
    Gen.pkPA_facts0 Gen.pkPA_items0 pkPA_G pkPA_spec

/-- **The second P store** and the unpacks of the third store's halves. -/
theorem stepAt_pstP_1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pst .plain 1, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issueAt (dn := D.mk' (.pst .plain 2) v) (by code_lookup)
    (fun hpc hf => fires_tcSt_next (by rw [hpc, Assumptions.all_tcStWaitLd]; rfl) hf)
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  pP_unpack (⟨.pst .plain 1, v, 0, []⟩ : D) (D.mk' (.pst .plain 2) v) Gen.pkPB_run pkPB_facts0_eq
    Gen.pkPB_facts0 Gen.pkPB_items0 pkPB_G pkPB_spec

/-- **The arrival between the store waits** and the unpacks of the fourth store's halves. -/
theorem stepAt_parrP (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.parr .plain, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_arrive (dn := D.mk' (.pst .plain 3) v) (by code_lookup) ?_
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro r hr q hq e
    cases hr
    have hk : (liveD (livePc ⟨.parr .plain, v, 0, []⟩)).contains 8850 = false := by kernel_rfl
    simp only [factsD, factsFrom, List.mem_map] at hq
    obtain ⟨r', hr', rfl⟩ := hq
    simp only at e
    subst e
    rw [List.contains_iff_mem.mpr hr'] at hk
    cases hk
  · pP_unpack (⟨.parr .plain, v, 0, []⟩ : D) (D.mk' (.pst .plain 3) v) Gen.pkPC_run pkPC_facts0_eq
      Gen.pkPC_facts0 Gen.pkPC_items0 pkPC_G pkPC_spec

/-- **A plain round's arrival at the correction warps' named barrier**: the exponent stretch, to
the first P store, landing on the P part's table. -/
theorem stepAt_narrP (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.narr .plain, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issue (dn := D.mk' (.pst .plain 0) v) (by code_lookup)
    (fun hf => fires_barArrive_next hf) (fun _ => rfl) rfl rfl
    ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  refine Seg.weaken_end_ex (expoP_seg hp v) fun R hR => ?_
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
  obtain ⟨-, h3⟩ := (holds_append _ _ _).mp h2
  exact land_run (G := expoPE p v) (ctlK := ctlP)
    (Vs := valueOfD p L g ⟨.narr .plain, v, 0, []⟩)
    (valueOfD_prefix (d := ⟨.pst .plain 0, v, 0, []⟩) (pPData_eq p v) (expoPE_nodup p v))
    (valueOfD_ctl_eq (d := ⟨.narr .plain, v, 0, []⟩) (d' := D.mk' (.pst .plain 0) v) rfl
      (by kernel_rfl)) (by kernel_rfl) h1 h3

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
