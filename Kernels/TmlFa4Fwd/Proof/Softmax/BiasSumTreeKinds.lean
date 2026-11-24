-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasRs
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs2
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round's sum tree -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- Run b's start kinds. -/
def rsumBbK0 : List (Nat × Kd) :=
  kList ((Gen.rsumBb_facts0 fun _ => .pred false).map Prod.fst)
    (Function.update (kOn ((Gen.rsumBa_facts1 fun _ => .pred false).map Prod.fst)
      (kOut (kOf rsumBaK0) Gen.rsumBa_items0)) 5123 (.s .nn))

theorem rsumBb_facts0_eq (V : Nat → Value) :
    Gen.rsumBb_facts0 V = factsFrom ((Gen.rsumBb_facts0 V).map Prod.fst) V := by kernel_rfl
theorem rsumBb_keys (V : Nat → Value) : (Gen.rsumBb_facts0 V).map Prod.fst =
    (Gen.rsumBb_facts0 fun _ => .pred false).map Prod.fst := by kernel_rfl
theorem rsumBa_keys1 (V : Nat → Value) : (Gen.rsumBa_facts1 V).map Prod.fst =
    (Gen.rsumBa_facts1 fun _ => .pred false).map Prod.fst := by kernel_rfl

/-- The row sum's items read no role function. -/
macro "fns_okrsumBb" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.rsumBb_items0, Gen.rsumBb_items1, Gen.rsumBb_items2,
    Gen.rsumBb_items3, and_true, true_and]
  repeat' constructor))

@[irreducible] def rsumBbK1 : List (Nat × Kd) :=
  kList ((Gen.rsumBb_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rsumBbK0) Gen.rsumBb_items0)
@[irreducible] def rsumBbK2 : List (Nat × Kd) :=
  kList ((Gen.rsumBb_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rsumBbK1) Gen.rsumBb_items1)
@[irreducible] def rsumBbK3 : List (Nat × Kd) :=
  kList ((Gen.rsumBb_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rsumBbK2) Gen.rsumBb_items2)
@[irreducible] def rsumBbK4 : List (Nat × Kd) :=
  kList ((Gen.rsumBb_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rsumBbK3) Gen.rsumBb_items3)
theorem rsumBb_kok (V : Nat → Value) :
    (kOk (kOf rsumBbK0) Gen.rsumBb_items0 &&
      kNext rsumBbK0 Gen.rsumBb_items0 ((Gen.rsumBb_facts1 V).map Prod.fst) rsumBbK1 &&
      kOk (kOf rsumBbK1) Gen.rsumBb_items1 &&
      kNext rsumBbK1 Gen.rsumBb_items1 ((Gen.rsumBb_facts2 V).map Prod.fst) rsumBbK2 &&
      kOk (kOf rsumBbK2) Gen.rsumBb_items2 &&
      kNext rsumBbK2 Gen.rsumBb_items2 ((Gen.rsumBb_facts3 V).map Prod.fst) rsumBbK3 &&
      kOk (kOf rsumBbK3) Gen.rsumBb_items3 &&
      kNext rsumBbK3 Gen.rsumBb_items3 ((Gen.rsumBb_facts4 V).map Prod.fst) rsumBbK4) = true := by
  unfold rsumBbK0
  kernel_rfl

theorem rsumBb_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf rsumBbK0 r).Has (lookupD (Gen.rsumBb_facts0 V1) r)) :
    Gen.rsumBb_cond V1 ∧ (∀ r, (kOf rsumBbK3 r).Has (lookupD (Gen.rsumBb_facts3 V1) r)) := by
  have h8 := rsumBb_kok V1
  have hn4 := (band_split h8).2
  have h7 := (band_split h8).1
  have hk3 := (band_split h7).2
  have h6 := (band_split h7).1
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
  have hG0 : factsFrom ((Gen.rsumBb_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumBb_facts0 V1)) Gen.rsumBb_items0) = Gen.rsumBb_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.rsumBb_items0 := by fns_okrsumBb
  obtain ⟨c0, k1⟩ := kpiece_lit (L := rsumBbK0) (L' := rsumBbK1) (G := Gen.rsumBb_facts1 V1)
    (items := Gen.rsumBb_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.rsumBb_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumBb_facts1 V1)) Gen.rsumBb_items1) = Gen.rsumBb_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.rsumBb_items1 := by fns_okrsumBb
  obtain ⟨c1, k2⟩ := kpiece_lit (L := rsumBbK1) (L' := rsumBbK2) (G := Gen.rsumBb_facts2 V1)
    (items := Gen.rsumBb_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.rsumBb_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumBb_facts2 V1)) Gen.rsumBb_items2) = Gen.rsumBb_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.rsumBb_items2 := by fns_okrsumBb
  obtain ⟨c2, k3⟩ := kpiece_lit (L := rsumBbK2) (L' := rsumBbK3) (G := Gen.rsumBb_facts3 V1)
    (items := Gen.rsumBb_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.rsumBb_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumBb_facts3 V1)) Gen.rsumBb_items3) = Gen.rsumBb_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.rsumBb_items3 := by fns_okrsumBb
  obtain ⟨c3, _⟩ := kpiece_lit (L := rsumBbK3) (L' := rsumBbK4) (G := Gen.rsumBb_facts4 V1)
    (items := Gen.rsumBb_items3) hG3 hk3 k3 hf3 hn4
  exact ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, k3⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
