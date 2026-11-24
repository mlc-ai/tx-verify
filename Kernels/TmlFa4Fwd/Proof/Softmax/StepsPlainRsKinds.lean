-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The add tree's kinds in a plain round

The input includes the zero written at pc 7467. The generated add tree has five pieces. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The values run b starts from: run a's end facts with the zero of pc 7467. -/
abbrev rbV (p : Params) (v : V) : Nat → Value :=
  lookupD ((5806, .bits 32 (BitVec.ofNat 64 0)) :: Gen.rsumPa_facts1 (lookupD (pPData p v)))

/-- Run b's start kinds. -/
def rbK : List (Nat × Kd) :=
  kList ((Gen.rsumPb_facts0 fun _ => .pred false).map Prod.fst)
    (Function.update (kOn ((Gen.rsumPa_facts1 fun _ => .pred false).map Prod.fst)
      (kOut (kOf raK) Gen.rsumPa_items0)) 5806 (.s .nn))

theorem rsumPb_facts0_eq (V : Nat → Value) :
    Gen.rsumPb_facts0 V = factsFrom ((Gen.rsumPb_facts0 V).map Prod.fst) V := by kernel_rfl
theorem rsumPb_keys (V : Nat → Value) : (Gen.rsumPb_facts0 V).map Prod.fst =
    (Gen.rsumPb_facts0 fun _ => .pred false).map Prod.fst := by kernel_rfl
theorem rsumPa_keys1 (V : Nat → Value) : (Gen.rsumPa_facts1 V).map Prod.fst =
    (Gen.rsumPa_facts1 fun _ => .pred false).map Prod.fst := by kernel_rfl

theorem zero_nn : SK.nn.Has (.bits 32 (BitVec.ofNat 64 0)) :=
  ⟨⟨rfl, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h; decide)⟩, 0, le_refl _,
    by simpa using readEReal_zero32⟩

/-- The row sum's items read no role function. -/
macro "fns_okrsumPb" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.rsumPb_items0, Gen.rsumPb_items1, Gen.rsumPb_items2,
    Gen.rsumPb_items3, Gen.rsumPb_items4, and_true, true_and]
  repeat' constructor))

@[irreducible] def rbL1 : List (Nat × Kd) :=
  kList ((Gen.rsumPb_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rbK) Gen.rsumPb_items0)
@[irreducible] def rbL2 : List (Nat × Kd) :=
  kList ((Gen.rsumPb_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rbL1) Gen.rsumPb_items1)
@[irreducible] def rbL3 : List (Nat × Kd) :=
  kList ((Gen.rsumPb_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rbL2) Gen.rsumPb_items2)
@[irreducible] def rbL4 : List (Nat × Kd) :=
  kList ((Gen.rsumPb_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rbL3) Gen.rsumPb_items3)
@[irreducible] def rbL5 : List (Nat × Kd) :=
  kList ((Gen.rsumPb_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rbL4) Gen.rsumPb_items4)

theorem rsumPb_kok (V : Nat → Value) :
    (kOk (kOf rbK) Gen.rsumPb_items0 &&
      kNext rbK Gen.rsumPb_items0 ((Gen.rsumPb_facts1 V).map Prod.fst) rbL1 &&
      kOk (kOf rbL1) Gen.rsumPb_items1 &&
      kNext rbL1 Gen.rsumPb_items1 ((Gen.rsumPb_facts2 V).map Prod.fst) rbL2 &&
      kOk (kOf rbL2) Gen.rsumPb_items2 &&
      kNext rbL2 Gen.rsumPb_items2 ((Gen.rsumPb_facts3 V).map Prod.fst) rbL3 &&
      kOk (kOf rbL3) Gen.rsumPb_items3 &&
      kNext rbL3 Gen.rsumPb_items3 ((Gen.rsumPb_facts4 V).map Prod.fst) rbL4 &&
      kOk (kOf rbL4) Gen.rsumPb_items4 &&
      kNext rbL4 Gen.rsumPb_items4 ((Gen.rsumPb_facts5 V).map Prod.fst) rbL5) = true := by
  unfold rbK
  kernel_rfl

theorem rsumPb_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf rbK r).Has (lookupD (Gen.rsumPb_facts0 V1) r)) :
    Gen.rsumPb_cond V1 ∧ (∀ r, (kOf rbL4 r).Has (lookupD (Gen.rsumPb_facts4 V1) r)) ∧
      ∀ r, (kOf rbL5 r).Has (lookupD (Gen.rsumPb_facts5 V1) r) := by
  have h10 := rsumPb_kok V1
  have hn5 := (band_split h10).2
  have h9 := (band_split h10).1
  have hk4 := (band_split h9).2
  have h8 := (band_split h9).1
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
  have hG0 : factsFrom ((Gen.rsumPb_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumPb_facts0 V1)) Gen.rsumPb_items0) = Gen.rsumPb_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.rsumPb_items0 := by fns_okrsumPb
  obtain ⟨c0, k1⟩ := kpiece_lit (L := rbK) (L' := rbL1) (G := Gen.rsumPb_facts1 V1)
    (items := Gen.rsumPb_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.rsumPb_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumPb_facts1 V1)) Gen.rsumPb_items1) = Gen.rsumPb_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.rsumPb_items1 := by fns_okrsumPb
  obtain ⟨c1, k2⟩ := kpiece_lit (L := rbL1) (L' := rbL2) (G := Gen.rsumPb_facts2 V1)
    (items := Gen.rsumPb_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.rsumPb_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumPb_facts2 V1)) Gen.rsumPb_items2) = Gen.rsumPb_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.rsumPb_items2 := by fns_okrsumPb
  obtain ⟨c2, k3⟩ := kpiece_lit (L := rbL2) (L' := rbL3) (G := Gen.rsumPb_facts3 V1)
    (items := Gen.rsumPb_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.rsumPb_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumPb_facts3 V1)) Gen.rsumPb_items3) = Gen.rsumPb_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.rsumPb_items3 := by fns_okrsumPb
  obtain ⟨c3, k4⟩ := kpiece_lit (L := rbL3) (L' := rbL4) (G := Gen.rsumPb_facts4 V1)
    (items := Gen.rsumPb_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.rsumPb_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsumPb_facts4 V1)) Gen.rsumPb_items4) = Gen.rsumPb_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.rsumPb_items4 := by fns_okrsumPb
  obtain ⟨c4, k5⟩ := kpiece_lit (L := rbL4) (L' := rbL5) (G := Gen.rsumPb_facts5 V1)
    (items := Gen.rsumPb_items4) hG4 hk4 k4 hf4 hn5
  exact ⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, k4, k5⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
