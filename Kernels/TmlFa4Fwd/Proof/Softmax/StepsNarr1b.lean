-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.NegScale
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1
import Lemmas.Flow.RunFrame
import Lemmas.Flow.Step.TcSteps
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The first round's exponent stretch: the step

The step of the first round's narrow state (`stepAt_narr1`) on the generated exponent stretch,
whose kinds `StepsNarr1.lean` checks. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The first round's arrival at the correction warps' named barrier**: the negated scale and
the exponent stretch, to the first P store. -/
theorem stepAt_narr1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.narr .first, v, 0, []⟩ := by
  obtain ⟨s, hS, hs0, h32⟩ := scale_word hp
  have hsc : scl p = s := by simp [scl, hS]
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issue (dn := D.mk' (.pst .first 0) v) (by code_lookup)
    (fun hf => fires_barArrive_next hf) (fun _ => rfl) rfl rfl
    ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  refine Seg.comp_ex (neg_scale hS hs0.ne' h32 (F := factsD p L g ⟨.narr .first, v, 0, []⟩)
    (mem_factsFrom (List.contains_iff_mem.mp (by kernel_rfl : (liveD 4397).contains 7132 = true)))
    (by kernel_rfl)) ?_
  have hrun := Gen.expo1_run L g (vExpo1 p L g v)
  have hfr := SegD.frame (H := factsFrom (ctlLive 4397) (valueOfD p L g ⟨.narr .first, v, 0, []⟩))
    Gen.rulesFrame hrun rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start ?_ |>.weaken_end ?_) (expo1_ok hp v).1
  · intro R hR
    refine (holds_append _ _ _).mpr ⟨?_, holds_sub hR.2 (by kernel_rfl)⟩
    rw [expo1_facts0_eq]
    have hneg : negS p = Value.float .f32 ((-s : ℚ) : ℝ) := by rw [negS, hsc]
    have e : factsFrom ((Gen.expo1_facts0 (vExpo1 p L g v)).map Prod.fst) (vExpo1 p L g v) =
        factsFrom ((Gen.expo1_facts0 (vExpo1 p L g v)).map Prod.fst)
          (Function.update (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) 1230 (negS p)) :=
      List.map_congr_left fun r hr => by rw [vExpo1_eq v hr]
    rw [e]
    refine holds_start (W := valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) (live := liveD 4397)
      ?_ ?_
    · rw [← hneg] at hR
      exact hR
    · kernel_rfl
  · intro R hR
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    exact land_run (valueOfD_prefix (d := ⟨.pst .first 0, v, 0, []⟩) rfl (expoE_nodup p L g v))
      (valueOfD_ctl_eq (ctlK := ctlLive 4397) rfl (by kernel_rfl))
      (live := liveD 4826) (by kernel_rfl) h1 h2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
