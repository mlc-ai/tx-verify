-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBB
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoB0
public import Kernels.TmlFa4Fwd.Proof.Softmax.SwExpB
import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasExpoVals

@[expose] public section

/-! # The bias round's exponents: the software path's kinds

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

/-- The start kinds of run 0: the scaled-product run's end kinds. -/
def bK0 : List (Nat × Kd) :=
  kList ((Gen.expoBB0_facts0 fun _ => .pred false).map Prod.fst) (kOf eB5)

@[irreducible] def bB0_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB0_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK0) Gen.expoBB0_items0)
@[irreducible] def bB0_2 : List (Nat × Kd) :=
  kList ((Gen.expoBB0_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bB0_1) Gen.expoBB0_items1)
@[irreducible] def bB0_3 : List (Nat × Kd) :=
  kList ((Gen.expoBB0_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bB0_2) Gen.expoBB0_items2)

theorem expoBB0_kok (V : Nat → Value) :
    (kOk (kOf bK0) Gen.expoBB0_items0 &&
      kNext bK0 Gen.expoBB0_items0 ((Gen.expoBB0_facts1 V).map Prod.fst) bB0_1 &&
      kOk (kOf bB0_1) Gen.expoBB0_items1 &&
      kNext bB0_1 Gen.expoBB0_items1 ((Gen.expoBB0_facts2 V).map Prod.fst) bB0_2 &&
      kOk (kOf bB0_2) Gen.expoBB0_items2 &&
      kNext bB0_2 Gen.expoBB0_items2 ((Gen.expoBB0_facts3 V).map Prod.fst) bB0_3) = true := by
  unfold bK0
  kernel_rfl

theorem expoBB0_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK0 r).Has (lookupD (Gen.expoBB0_facts0 V1) r)) :
    Gen.expoBB0_cond V1 ∧ ∀ r, (kOf bB0_3 r).Has (lookupD (Gen.expoBB0_facts3 V1) r) := by
  have h6 := expoBB0_kok V1
  have hn3 := (band_split h6).2
  have h5 := (band_split h6).1
  have hk2 := (band_split h5).2
  have h4 := (band_split h5).1
  have hn2 := (band_split h4).2
  have h3 := (band_split h4).1
  have hk1 := (band_split h3).2
  have h2 := (band_split h3).1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB0_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB0_facts0 V1)) Gen.expoBB0_items0) = Gen.expoBB0_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB0_items0 := by fns_okB Gen.expoBB0_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK0) (L' := bB0_1)
    (G := Gen.expoBB0_facts1 V1) (items := Gen.expoBB0_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoBB0_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB0_facts1 V1)) Gen.expoBB0_items1) = Gen.expoBB0_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoBB0_items1 := by fns_okB Gen.expoBB0_items1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := bB0_1) (L' := bB0_2)
    (G := Gen.expoBB0_facts2 V1) (items := Gen.expoBB0_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoBB0_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB0_facts2 V1)) Gen.expoBB0_items2) = Gen.expoBB0_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoBB0_items2 := by fns_okB Gen.expoBB0_items2
  obtain ⟨c2, k3⟩ := kpiece_lit (L := bB0_2) (L' := bB0_3)
    (G := Gen.expoBB0_facts3 V1) (items := Gen.expoBB0_items2) hG2 hk2 k2 hf2 hn3
  exact ⟨⟨⟨c0, c1⟩, c2⟩, k3⟩

/-- The start kinds of run 1: the instance's outputs are numbers. -/
def bK1 : List (Nat × Kd) :=
  kList ((Gen.expoBB1_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4668 || r == 4671 then .s .fl else kOf bB0_3 r)

@[irreducible] def bB1_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB1_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK1) Gen.expoBB1_items0)

theorem expoBB1_kok (V : Nat → Value) :
    (kOk (kOf bK1) Gen.expoBB1_items0 &&
      kNext bK1 Gen.expoBB1_items0 ((Gen.expoBB1_facts1 V).map Prod.fst) bB1_1) = true := by
  unfold bK1
  kernel_rfl

theorem expoBB1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK1 r).Has (lookupD (Gen.expoBB1_facts0 V1) r)) :
    Gen.expoBB1_cond V1 ∧ ∀ r, (kOf bB1_1 r).Has (lookupD (Gen.expoBB1_facts1 V1) r) := by
  have h2 := expoBB1_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB1_facts0 V1)) Gen.expoBB1_items0) = Gen.expoBB1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB1_items0 := by fns_okB Gen.expoBB1_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK1) (L' := bB1_1)
    (G := Gen.expoBB1_facts1 V1) (items := Gen.expoBB1_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 2: the instance's outputs are numbers. -/
def bK2 : List (Nat × Kd) :=
  kList ((Gen.expoBB2_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4674 || r == 4677 then .s .fl else kOf bB1_1 r)

@[irreducible] def bB2_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB2_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK2) Gen.expoBB2_items0)

theorem expoBB2_kok (V : Nat → Value) :
    (kOk (kOf bK2) Gen.expoBB2_items0 &&
      kNext bK2 Gen.expoBB2_items0 ((Gen.expoBB2_facts1 V).map Prod.fst) bB2_1) = true := by
  unfold bK2
  kernel_rfl

theorem expoBB2_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK2 r).Has (lookupD (Gen.expoBB2_facts0 V1) r)) :
    Gen.expoBB2_cond V1 ∧ ∀ r, (kOf bB2_1 r).Has (lookupD (Gen.expoBB2_facts1 V1) r) := by
  have h2 := expoBB2_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB2_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB2_facts0 V1)) Gen.expoBB2_items0) = Gen.expoBB2_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB2_items0 := by fns_okB Gen.expoBB2_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK2) (L' := bB2_1)
    (G := Gen.expoBB2_facts1 V1) (items := Gen.expoBB2_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 3: the instance's outputs are numbers. -/
def bK3 : List (Nat × Kd) :=
  kList ((Gen.expoBB3_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4680 || r == 4683 then .s .fl else kOf bB2_1 r)

@[irreducible] def bB3_1 : List (Nat × Kd) :=
  kList ((Gen.expoBB3_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf bK3) Gen.expoBB3_items0)

theorem expoBB3_kok (V : Nat → Value) :
    (kOk (kOf bK3) Gen.expoBB3_items0 &&
      kNext bK3 Gen.expoBB3_items0 ((Gen.expoBB3_facts1 V).map Prod.fst) bB3_1) = true := by
  unfold bK3
  kernel_rfl

theorem expoBB3_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf bK3 r).Has (lookupD (Gen.expoBB3_facts0 V1) r)) :
    Gen.expoBB3_cond V1 ∧ ∀ r, (kOf bB3_1 r).Has (lookupD (Gen.expoBB3_facts1 V1) r) := by
  have h2 := expoBB3_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoBB3_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBB3_facts0 V1)) Gen.expoBB3_items0) = Gen.expoBB3_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBB3_items0 := by fns_okB Gen.expoBB3_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := bK3) (L' := bB3_1)
    (G := Gen.expoBB3_facts1 V1) (items := Gen.expoBB3_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The start kinds of run 4: the instance's outputs are numbers. -/
def bK4 : List (Nat × Kd) :=
  kList ((Gen.expoBB4_facts0 fun _ => .pred false).map Prod.fst)
    (fun r => if r == 4686 || r == 4689 then .s .fl else kOf bB3_1 r)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
