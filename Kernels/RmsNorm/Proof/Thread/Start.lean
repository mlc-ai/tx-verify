-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Tmpl

@[expose] public section

/-! # The first site of a thread

From the launch state, local steps reach the warp-index shuffle with the four parameters and the
thread's index and warp index in their registers. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The launch with the kernel's four parameters explicit, so that evaluation reads them. -/
theorem params_eq (hpre : Pre P L mem0) :
    explicitParams L [("rmsnorm_kernel_param_0", P.I), ("rmsnorm_kernel_param_1", P.O),
      ("rmsnorm_kernel_param_2", P.W), ("rmsnorm_kernel_param_3", P.Bt)] = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.hyp.param0, hpre.hyp.param1, hpre.hyp.param2, hpre.hyp.param3])

theorem start (hpre : Pre P L mem0) :
    ∃ t, Relation.ReflTransGen (Tau kernel Prod L g) {} t ∧
      At t Site.shfl0.pc (facts P g { site := .shfl0 }) := by
  have hp := params_eq hpre
  have hb := hpre.hyp.block
  have hbt := hpre.hyp.batch
  have h0 : At ({} : TState) 0 [] := ⟨rfl, rfl, rfl, rfl, trivial⟩
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel Prod
      (explicitParams L [("rmsnorm_kernel_param_0", P.I), ("rmsnorm_kernel_param_1", P.O),
        ("rmsnorm_kernel_param_2", P.W), ("rmsnorm_kernel_param_3", P.Bt)]) g 6 {} = some t ∧
      At t Site.shfl0.pc (facts P g { site := .shfl0 }) := by
    have htid := Launch.oneDim_tidOf hpre.hyp.oneDimLaunch.1 g
    -- `%tid` is the launch's `tidOf g`, which only `Launch.oneDim_tidOf` (with the block size)
    -- reduces to the coordinates: `seg_close` cannot evaluate it on its own.
    seg_fp h0 using
      simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some]
      all_goals first
        | seg_close [explicitParams, withParams, sregValue, hb]
        | (simp only [hp]; rw [htid, hb]; show Value.bits _ _ = _; norm_bits [Dim3.get])
  rw [hp] at hr
  exact ⟨t, run_rtg hr, ht⟩

end
end PTX.Kernels.RmsNorm.Proof
