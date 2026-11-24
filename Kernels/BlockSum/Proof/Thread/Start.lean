-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Thread.Sites
public import Lemmas.Flow.Footprint

@[expose] public section

/-! # The first site of a thread

From the launch state, local steps reach the input load with the input's address, the output
pointer and the thread's coordinates in their registers. -/

namespace PTX.Kernels.BlockSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat}

/-- The launch with the kernel's two parameters explicit, so that evaluation reads them. -/
theorem params_eq (hpre : Pre L A B x mem0) :
    explicitParams L [("block_sum_param_0", A), ("block_sum_param_1", B)] = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.param0, hpre.param1])

theorem start (hpre : Pre L A B x mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel Prod L g) {} t ∧
      At t Site.input.pc (facts A B L g { site := .input }) := by
  have hp := params_eq hpre
  have hg32 : g < 2 ^ 32 := lt_of_lt_of_le hg hpre.threads32
  have hsum : 256 * (g / 256) + g % 256 = g := by simpa [Nat.mul_comm] using Nat.div_add_mod' g 256
  have hb := hpre.block
  have hrA := hpre.rangeA
  have hrB := hpre.rangeB
  have hT : L.threads = L.grid * L.block := rfl
  have h0 : At ({} : TState) 0 [] := ⟨rfl, rfl, rfl, rfl, trivial⟩
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel Prod
      (explicitParams L [("block_sum_param_0", A), ("block_sum_param_1", B)]) g 9 {} = some t ∧
      At t Site.input.pc (facts A B
        (explicitParams L [("block_sum_param_0", A), ("block_sum_param_1", B)]) g
        { site := .input }) := by
    have htid := Launch.oneDim_tidOf hpre.oneDimLaunch.1 g
    have hcta := Launch.oneDim_ctaidOf hpre.oneDimLaunch.1 (g / L.block)
    seg_fp h0 using
      simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some]
      all_goals first
        | seg_close [explicitParams, withParams, sregValue, hb, hsum]
        | (simp only [hp]; rw [htid, hb]; show Value.bits _ _ = _; norm_bits [Dim3.get])
        | (simp only [hp]; rw [hcta, hb]; show Value.bits _ _ = _; norm_bits [Dim3.get])
        | (simp only [hp]; rw [htid, hcta, hb]
           show Value.bits _ _ = _; norm_bits [Dim3.get])
  rw [hp] at hr ht
  exact ⟨t, run_rtg hr, ht⟩

end
end PTX.Kernels.BlockSum.Proof
