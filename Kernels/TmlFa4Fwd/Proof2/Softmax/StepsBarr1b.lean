-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBarr1Chain

@[expose] public section

/-! # The first round's bias barrier steps

The bias-slot arrival and the preceding warp-group barrier use the segment in
`StepsBarr1Chain.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (andi scmpi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The steps -/

/-- **The first round's bias-slot arrival** (lane 0 of a warp), and the chain to the named-barrier
arrival. -/
theorem stepAt_barr1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.barr false, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_arrive (dn := D.mk' (.narr .first) v) (by code_lookup) ?_
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro r hr q hq e
    cases hr
    have hk : (liveD (livePc ⟨.barr false, v, 0, []⟩)).contains 7894 = false := by kernel_rfl
    simp only [factsD, factsFrom, List.mem_map] at hq
    obtain ⟨r', hr', rfl⟩ := hq
    simp only at e
    subst e
    rw [List.contains_iff_mem.mpr hr'] at hk
    cases hk
  · exact seg_start_ex (chain1 hp v) fun R hR => holds_sub hR (by kernel_rfl)

/-- **The first round's named barrier**: lane 0 of a warp continues to the bias-slot arrival, the
other lanes branch to the products and run the chain to the named-barrier arrival. -/
theorem stepAt_bsync1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.bsync false, v, 0, []⟩ := by
  have hparams := params hp
  have key : ∀ e, (codeD p L g).next ⟨.bsync false, v, 0, []⟩ e =
      some (some (D.ite (scmpi .ne .b (andi (tidW L g) 31) 0) (D.mk' (.narr .first) v)
        (D.mk' (.barr false) v))) := fun _ => rfl
  have hv : valueOfD p L g ⟨.bsync false, v, 0, []⟩ = valueOfD p L g ⟨.barr false, v, 0, []⟩ :=
    rfl
  have h482 : (482, Value.pred (scmpi .ne .b (andi (tidW L g) 31) 0)) ∈
      factsD p L g ⟨.bsync false, v, 0, []⟩ :=
    mem_factsFrom (List.contains_iff_mem.mp (by kernel_rfl))
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  cases hc : scmpi .ne .b (andi (tidW L g) 31) 0
  · refine Code.step_issue (dn := D.mk' (.barr false) v) (by code_lookup)
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e, hc]; rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
    site_norm
    refine Seg.pred_ex h482 hc ?_
    seg_sym using (soft_seg)
  · refine Code.step_issue (dn := D.mk' (.narr .first) v) (by code_lookup)
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e, hc]; rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
    site_norm
    refine Seg.comp_ex (q := 3591)
      (H := factsFrom (liveD 3591) (valueOfD p L g ⟨.bsync false, v, 0, []⟩)) ?_ ?_
    · refine Seg.pred_ex h482 hc ?_
      seg_sym using (soft_seg)
    · rw [hv]; exact chain1 hp v

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
