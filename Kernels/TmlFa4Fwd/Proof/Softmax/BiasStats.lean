-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Statistics carried across the bias round's exponent stretch -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

private abbrev statsB (W : Nat → Value) : Value × Value × Value × Value :=
  (W 1230, W 1362, W 7256, W 7257)

private theorem nextB0_stats (U : Nat → Value) : statsB (nextB0 U) = statsB U := by
  kernel_rfl

private theorem nextB1_stats (U : Nat → Value) : statsB (nextB1 U) = statsB U := by
  kernel_rfl

private theorem nextB2_stats (U : Nat → Value) : statsB (nextB2 U) = statsB U := by
  kernel_rfl

private theorem nextB3_stats (U : Nat → Value) : statsB (nextB3 U) = statsB U := by
  kernel_rfl

private theorem nextB4_stats (U : Nat → Value) : statsB (nextB4 U) = statsB U := by
  kernel_rfl

private theorem nextB5_stats (U : Nat → Value) : statsB (nextB5 U) = statsB U := by
  kernel_rfl

private theorem nextB6_stats (U : Nat → Value) : statsB (nextB6 U) = statsB U := by
  kernel_rfl

private theorem nextB7_stats (U : Nat → Value) : statsB (nextB7 U) = statsB U := by
  kernel_rfl

private theorem vB8_stats (W : Nat → Value) : statsB (vB8 W) = statsB W := by
  simp only [vB8, vB7, vB6, vB5, vB4, vB3, vB2, vB1,
    nextB7_stats, nextB6_stats, nextB5_stats, nextB4_stats, nextB3_stats, nextB2_stats,
    nextB1_stats, nextB0_stats]

private theorem statsA (W : Nat → Value) :
    statsB (lookupD (Gen.expoBTA1_facts4 (nextTA (lookupD (Gen.expoBA_facts5 W))))) =
      statsB W := by
  kernel_rfl

private theorem statsLastB (W : Nat → Value) :
    statsB (lookupD (Gen.expoBTA1_facts4 (nextTB (lookupD (Gen.expoBB8_facts1 W))))) =
      statsB W := by
  kernel_rfl

private theorem statsB0 (W : Nat → Value) : statsB (lookupD (Gen.expoB0_facts5 W)) =
    statsB W := by kernel_rfl

private theorem statsPData (F : List (Nat × Value)) (U : Nat → Value) :
    statsB (lookupD (Gen.expoBTA1_facts4 U ++ F)) =
      statsB (lookupD (Gen.expoBTA1_facts4 U)) := by kernel_rfl

private theorem statsNarr (p : Params) (L : Launch) (g : Nat) (v : V) :
    statsB (vExpoB p L g v) =
      (negS p, lookupD (valuesBiasM p v) 1362, lookupD (valuesBiasM p v) 7256,
        .float .f32 v.rs) := by
  unfold vExpoB
  rw [statsB0]
  rfl

/-- The bias round's running statistics are preserved through the P part. -/
theorem pB_stats (p : Params) (L : Launch) (g : Nat) (v : V) :
    (lookupD (pBData p L g v) 1230, lookupD (pBData p L g v) 1362,
      lookupD (pBData p L g v) 7256, lookupD (pBData p L g v) 7257) =
      (negS p, lookupD (valuesBiasM p v) 1362, lookupD (valuesBiasM p v) 7256,
        .float .f32 v.rs) := by
  change statsB (lookupD (pBData p L g v)) = _
  unfold pBData tailB
  simp only [List.append_assoc]
  rw [statsPData]
  unfold vTailB
  cases Epilogue.scmp .lt .u v.bt (r301 p L g v)
  · simp only [Bool.cond_false, statsA, statsNarr]
  · simp only [Bool.cond_true, statsLastB, vB8_stats, statsNarr]

theorem pB_scale_lookup (p : Params) (L : Launch) (g : Nat) (v : V) :
    lookupD (pBData p L g v) 1230 = negS p :=
  (Prod.mk.inj (pB_stats p L g v)).1

theorem pB_factor_lookup (p : Params) (L : Launch) (g : Nat) (v : V) :
    lookupD (pBData p L g v) 1362 = lookupD (valuesBiasM p v) 1362 :=
  (Prod.mk.inj (Prod.mk.inj (pB_stats p L g v)).2).1

theorem pB_max_lookup (p : Params) (L : Launch) (g : Nat) (v : V) :
    lookupD (pBData p L g v) 7256 = lookupD (valuesBiasM p v) 7256 :=
  (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (pB_stats p L g v)).2).2).1

theorem pB_sum_lookup (p : Params) (L : Launch) (g : Nat) (v : V) :
    lookupD (pBData p L g v) 7257 = .float .f32 v.rs :=
  (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (pB_stats p L g v)).2).2).2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
