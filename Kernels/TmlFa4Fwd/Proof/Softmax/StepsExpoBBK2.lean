-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the software path's kinds, runs 4 to 8

The software path (pcs 5977 to 6298, the round index below `%r301`): nine generated runs
(`Gen.expoBB0_run` … `expoBB8_run`) between eight software `exp2` instances. The values after an
instance are `nextB<k>` (the instance's outputs, the lane readings `laneY`, written over the run's
end values); `vB<k>` are the start values of run `k` from the start values `W` of run 0. Each run's
condition holds by the kinds (`expoBB<k>_chain`), whose start kinds are the previous run's end
kinds with the instance's two outputs numbers. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[irreducible] def bB4_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB4_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK4) Gen.expoBB4_items0)

theorem expoBB4_kok (V : Nat → Value) :
    (kOk (kOf bK4) Gen.expoBB4_items0 &&
      kNext bK4 Gen.expoBB4_items0 ((Gen.expoBB4_facts1 V).map Prod.fst) bB4_1) = true := by
  unfold bK4
  kernel_rfl

theorem expoBB4_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK4 r).Has (lookupD (Gen.expoBB4_facts0 V1) r)) :
    Gen.expoBB4_cond V1 ∧ ∀ r, (kOf bB4_1 r).Has (lookupD (Gen.expoBB4_facts1 V1) r) := by
  have h2 := expoBB4_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB4_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB4_facts0 V1)) Gen.expoBB4_items0) = Gen.expoBB4_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB4_items0 := by fns_okB Gen.expoBB4_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK4) (L' := bB4_1)
    (G := Gen.expoBB4_facts1 V1) (items := Gen.expoBB4_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 5: the instance's outputs are numbers. -/
def bK5 : List (Nat × Kd) :=
  kList ((Gen.expoBB5_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4692 || r == 4695 then .s .fl else kOf bB4_1 r)

@[irreducible] def bB5_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB5_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK5) Gen.expoBB5_items0)

theorem expoBB5_kok (V : Nat → Value) :
    (kOk (kOf bK5) Gen.expoBB5_items0 &&
      kNext bK5 Gen.expoBB5_items0 ((Gen.expoBB5_facts1 V).map Prod.fst) bB5_1) = true := by
  unfold bK5
  kernel_rfl

theorem expoBB5_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK5 r).Has (lookupD (Gen.expoBB5_facts0 V1) r)) :
    Gen.expoBB5_cond V1 ∧ ∀ r, (kOf bB5_1 r).Has (lookupD (Gen.expoBB5_facts1 V1) r) := by
  have h2 := expoBB5_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB5_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB5_facts0 V1)) Gen.expoBB5_items0) = Gen.expoBB5_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB5_items0 := by fns_okB Gen.expoBB5_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK5) (L' := bB5_1)
    (G := Gen.expoBB5_facts1 V1) (items := Gen.expoBB5_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 6: the instance's outputs are numbers. -/
def bK6 : List (Nat × Kd) :=
  kList ((Gen.expoBB6_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4698 || r == 4701 then .s .fl else kOf bB5_1 r)

@[irreducible] def bB6_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB6_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK6) Gen.expoBB6_items0)

theorem expoBB6_kok (V : Nat → Value) :
    (kOk (kOf bK6) Gen.expoBB6_items0 &&
      kNext bK6 Gen.expoBB6_items0 ((Gen.expoBB6_facts1 V).map Prod.fst) bB6_1) = true := by
  unfold bK6
  kernel_rfl

theorem expoBB6_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK6 r).Has (lookupD (Gen.expoBB6_facts0 V1) r)) :
    Gen.expoBB6_cond V1 ∧ ∀ r, (kOf bB6_1 r).Has (lookupD (Gen.expoBB6_facts1 V1) r) := by
  have h2 := expoBB6_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB6_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB6_facts0 V1)) Gen.expoBB6_items0) = Gen.expoBB6_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB6_items0 := by fns_okB Gen.expoBB6_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK6) (L' := bB6_1)
    (G := Gen.expoBB6_facts1 V1) (items := Gen.expoBB6_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 7: the instance's outputs are numbers. -/
def bK7 : List (Nat × Kd) :=
  kList ((Gen.expoBB7_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4704 || r == 4707 then .s .fl else kOf bB6_1 r)

@[irreducible] def bB7_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB7_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK7) Gen.expoBB7_items0)

theorem expoBB7_kok (V : Nat → Value) :
    (kOk (kOf bK7) Gen.expoBB7_items0 &&
      kNext bK7 Gen.expoBB7_items0 ((Gen.expoBB7_facts1 V).map Prod.fst) bB7_1) = true := by
  unfold bK7
  kernel_rfl

theorem expoBB7_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK7 r).Has (lookupD (Gen.expoBB7_facts0 V1) r)) :
    Gen.expoBB7_cond V1 ∧ ∀ r, (kOf bB7_1 r).Has (lookupD (Gen.expoBB7_facts1 V1) r) := by
  have h2 := expoBB7_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB7_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB7_facts0 V1)) Gen.expoBB7_items0) = Gen.expoBB7_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB7_items0 := by fns_okB Gen.expoBB7_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK7) (L' := bB7_1)
    (G := Gen.expoBB7_facts1 V1) (items := Gen.expoBB7_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 8: the instance's outputs are numbers. -/
def bK8 : List (Nat × Kd) :=
  kList ((Gen.expoBB8_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4710 || r == 7252 then .s .fl else kOf bB7_1 r)

@[irreducible] def bB8_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB8_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK8) Gen.expoBB8_items0)

theorem expoBB8_kok (V : Nat → Value) :
    (kOk (kOf bK8) Gen.expoBB8_items0 &&
      kNext bK8 Gen.expoBB8_items0 ((Gen.expoBB8_facts1 V).map Prod.fst) bB8_1) = true := by
  unfold bK8
  kernel_rfl

theorem expoBB8_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK8 r).Has (lookupD (Gen.expoBB8_facts0 V1) r)) :
    Gen.expoBB8_cond V1 ∧ ∀ r, (kOf bB8_1 r).Has (lookupD (Gen.expoBB8_facts1 V1) r) := by
  have h2 := expoBB8_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB8_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB8_facts0 V1)) Gen.expoBB8_items0) = Gen.expoBB8_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB8_items0 := by fns_okB Gen.expoBB8_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK8) (L' := bB8_1)
    (G := Gen.expoBB8_facts1 V1) (items := Gen.expoBB8_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
