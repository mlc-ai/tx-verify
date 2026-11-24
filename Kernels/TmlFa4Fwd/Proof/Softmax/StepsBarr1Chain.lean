-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1Products
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Kinds
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The first bias round from its bias-slot arrival

The segment composes the pieces from pc 3591 to the named-barrier arrival at pc 4397. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (andi scmpi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **From pc 3591 to the first round's named-barrier arrival.** -/
theorem chain1 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 3591
    (factsFrom (liveD 3591) (valueOfD p L g ⟨.barr false, v, 0, []⟩)) 4397
    (factsD p L g ⟨.narr .first, v, 0, []⟩) := by
  have p23 := seg_frame (lo := 3850) (hi := 4397) (H := maskPairs (bpf v) (bps p v))
    (mcnt1 (g := g) hp v)
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  have p34 := seg_frame (lo := 3872) (hi := 4397)
    (H := factsFrom (ctlLive 3872) (vMc p L g v))
    (mask_sel L g (mcnt p L g v) (bps p v) (bpf v))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  have p45 := seg_frame (lo := 4329) (hi := 4397)
    (H := elemsF (mcnt p L g v) (bpf v) (bps p v) ++
      factsFrom (ctlLive 3872) (vMc p L g v))
    (mask_fold' L g (mcnt p L g v) (bps p v) (bpf v))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  have p56 := seg_frame (lo := 4395) (hi := 4397)
    (H := elemsF (mcnt p L g v) (bpf v) (bps p v) ++
      factsFrom (ctlLive 3872) (vMc p L g v))
    (sel_max L g (foldF_lt_top p L g v))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex (chain1_products hp v) ?_
  -- 3850: the mask count's control facts and the products
  refine Seg.comp_ex (seg_start_ex p23 fun R hR => by
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    have hP := prod1_pairs (g := g) hp v R h1
    refine (holds_append _ _ _).mpr ⟨?_, cast (congrArg (Holds R) (by kernel_rfl)) hP.2⟩
    have hk : (ctlLive 3850).all (fun r => r == 7896 || ((ctlLive 3593).contains r &&
        r != 7135 && ctl r && !((valuesP1 p L g).map Prod.fst).contains r)) = true := by
      kernel_rfl
    refine holds_of_pointwise fun r hr => ?_
    have h := List.all_eq_true.mp hk r hr
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
      bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
    rcases h with rfl | ⟨⟨⟨h3593, h7135⟩, hc⟩, hP1⟩
    · rw [valueOfD_ctl _ (by kernel_rfl)]
      exact hP.1
    · rw [valueOf_narr_barr v hc (by simpa using hP1)]
      have := holds_mem h2 (mem_factsFrom h3593)
      rwa [vProd1, Function.update_of_ne h7135] at this) ?_
  -- 3872: the mask selects' start facts
  refine Seg.comp_ex (seg_start_ex p34 fun R hR => by
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    have h0 : R 3235 = some (.bits 32 (mcnt p L g v)) := by
      have := holds_mem h1 (mem_factsFrom (List.contains_iff_mem.mp
        (by kernel_rfl : (ctlLive 3872).contains 3235 = true)))
      rwa [vMc, Function.update_self] at this
    exact (holds_append _ _ _).mpr ⟨⟨h0, h2⟩, h1⟩) ?_
  -- 4329: the fold's start facts
  refine Seg.comp_ex (seg_start_ex p45 fun R hR =>
    (holds_append _ _ _).mpr ⟨((holds_append _ _ _).mp hR).1, hR⟩) ?_
  -- 4395
  refine Seg.comp_ex p56 ?_
  -- 4397: the arrival state's facts
  refine ⟨0, Seg.refl _ _ |>.weaken_end fun R hR => ?_⟩
  exact narr1_land v R hR

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
