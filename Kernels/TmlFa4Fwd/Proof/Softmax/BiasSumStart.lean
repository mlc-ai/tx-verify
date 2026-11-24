-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPB
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasStats
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumKindsA
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumKindsB
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round’s row-sum rescale -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem sumStart_has (hp : Pre p L m) (v : V) {r : Nat}
    (hr : r ∈ rsumBaKeys) (hr1 : r ≠ 1362) (hr2 : r ≠ 7257) :
    (sumK r).Has (lookupD (tailB p L g v) r) := by
  unfold tailB vTailB
  cases Epilogue.scmp .lt .u v.bt (r301 p L g v)
  · refine asSumKind ((tailA_ok (g := g) hp v).2.2.2 r) ?_
    have h := List.all_eq_true.mp sumStartKA r hr
    simpa [hr1, hr2, checkSumKind] using h
  · rw [expoBTA1_eq_B]
    refine asSumKind ((tailB_ok v (bb8_kinds hp v)).2.2.2 r) ?_
    have h := List.all_eq_true.mp sumStartKB r hr
    simpa [hr1, hr2, checkSumKind] using h

/-- The bias round's rescaling factor is a number. -/
theorem facB_fl (v : V) : SK.fl.Has (lookupD (valuesBiasM p v) 1362) := by
  change SK.fl.Has (bif v.mf then
    (if keepB p v = true then .bits 32 (BitVec.ofNat 64 1065353216)
      else .float .f32 (Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldBR p v))))
    else .float .f32 0)
  cases v.mf
  · exact has_float_fl 0
  · show SK.fl.Has (if keepB p v = true then _ else _)
    split
    · exact one_fl
    · exact has_float_fl _

/-- The rescale's start registers have the kinds used by the arithmetic run. -/
theorem pB_sumKind (hp : Pre p L m) (v : V) :
    ∀ q ∈ rsumBaK0, q.2.Has (lookupD (pBData p L g v) q.1) := by
  rintro ⟨r, k⟩ hq
  have he : k = sumK r := mem_kList hq
  subst k
  have hr : r ∈ rsumBaKeys := by
    change (r, sumK r) ∈ rsumBaKeys.map (fun n => (n, sumK n)) at hq
    obtain ⟨n, hn, h⟩ := List.mem_map.mp hq
    cases h
    exact hn
  by_cases hs : r = 7257
  · subst r
    exact Eq.mpr (congrArg (SK.fl.Has) (pB_sum_lookup p L g v)) (has_float_fl _)
  by_cases hf : r = 1362
  · subst r
    exact Eq.mpr (congrArg (SK.fl.Has) (pB_factor_lookup p L g v)) (facB_fl v)
  have hk : rsumBaKeys.all (((tailB p L g v).map Prod.fst).contains ·) = true := by
    unfold tailB
    kernel_rfl
  have hm := List.contains_iff_mem.mp (List.all_eq_true.mp hk r hr)
  obtain ⟨x, hx⟩ := lookup_some hm
  have h := sumStart_has (g := g) hp v hr hf hs
  simp only [pBData, List.append_assoc, lookupD, List.lookup_append, hx, Option.some_or,
    Option.getD_some] at h ⊢
  exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
