-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarrBChain
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's barrier steps

The bias-slot arrival and warp-group rendezvous use the segment in `StepsBarrBChain.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (andi scmpi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A bias round's bias-slot arrival** (lane 0 of a warp), and the chain to the statistics
store. -/
theorem stepAt_barrB (hp : Pre p L m) (v : V) : (codeD p L g).StepAt (barrB v) := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_arrive (dn := D.mk' (.stat false) v) (by code_lookup) ?_
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro r hr q hq e
    cases hr
    have hk : (liveD (livePc (barrB v))).contains 8315 = false := by kernel_rfl
    simp only [factsD, factsFrom, List.mem_map] at hq
    obtain ⟨r', hr', rfl⟩ := hq
    simp only at e
    subst e
    rw [List.contains_iff_mem.mpr hr'] at hk
    cases hk
  · exact seg_start_ex (chainB hp v) fun R hR => holds_sub hR (by kernel_rfl)

/-- **A bias round's named barrier**: lane 0 of a warp continues to the bias-slot arrival, the
other lanes branch to the products and run the chain to the statistics store. -/
theorem stepAt_bsyncB (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.bsync true, v, 0, []⟩ := by
  have hparams := params hp
  have key : ∀ e, (codeD p L g).next ⟨.bsync true, v, 0, []⟩ e =
      some (some (D.ite (scmpi .ne .b (andi (tidW L g) 31) 0) (D.mk' (.stat false) v)
        (D.mk' (.barr true) v))) := fun _ => rfl
  have hv : valueOfD p L g ⟨.bsync true, v, 0, []⟩ = valueOfD p L g (barrB v) := rfl
  have h632 : (632, Value.pred (scmpi .ne .b (andi (tidW L g) 31) 0)) ∈
      factsD p L g ⟨.bsync true, v, 0, []⟩ :=
    mem_factsFrom (List.contains_iff_mem.mp (by kernel_rfl))
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  cases hc : scmpi .ne .b (andi (tidW L g) 31) 0
  · refine Code.step_issue (dn := D.mk' (.barr true) v) (by code_lookup)
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e, hc]; rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
    site_norm
    refine Seg.pred_ex h632 hc ?_
    seg_sym using (soft_seg)
  · refine Code.step_issue (dn := D.mk' (.stat false) v) (by code_lookup)
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e, hc]; rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
    site_norm
    refine Seg.comp_ex (q := 5279)
      (H := factsFrom (liveD 5279) (valueOfD p L g ⟨.bsync true, v, 0, []⟩)) ?_ ?_
    · refine Seg.pred_ex h632 hc ?_
      seg_sym using (soft_seg)
    · rw [hv]; exact chainB hp v

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
