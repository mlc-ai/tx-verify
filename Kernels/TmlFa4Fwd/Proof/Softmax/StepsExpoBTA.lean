-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBT
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the tail's kinds after the hardware path -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The tail's first start kinds after path A. -/
def tAK0 : List (Nat × Kd) :=
  kList ((Gen.expoBTA0_facts0 fun _ => .pred false).map Prod.fst) (kOf aB5)

@[irreducible] def tAa1 : List (Nat × Kd) :=
  kList ((Gen.expoBTA0_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAK0) Gen.expoBTA0_items0)
@[irreducible] def tAa2 : List (Nat × Kd) :=
  kList ((Gen.expoBTA0_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAa1) Gen.expoBTA0_items1)
@[irreducible] def tAa3 : List (Nat × Kd) :=
  kList ((Gen.expoBTA0_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAa2) Gen.expoBTA0_items2)

theorem expoBTA0_kok (V : Nat → Value) :
    (kOk (kOf tAK0) Gen.expoBTA0_items0 &&
      kNext tAK0 Gen.expoBTA0_items0 ((Gen.expoBTA0_facts1 V).map Prod.fst) tAa1 &&
      kOk (kOf tAa1) Gen.expoBTA0_items1 &&
      kNext tAa1 Gen.expoBTA0_items1 ((Gen.expoBTA0_facts2 V).map Prod.fst) tAa2 &&
      kOk (kOf tAa2) Gen.expoBTA0_items2 &&
      kNext tAa2 Gen.expoBTA0_items2 ((Gen.expoBTA0_facts3 V).map Prod.fst) tAa3) = true := by
  unfold tAK0
  kernel_rfl

theorem expoBTA0_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf tAK0 r).Has (lookupD (Gen.expoBTA0_facts0 V1) r)) :
    Gen.expoBTA0_cond V1 ∧ ∀ r, (kOf tAa3 r).Has (lookupD (Gen.expoBTA0_facts3 V1) r) := by
  have h6 := expoBTA0_kok V1
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
  have hG0 : factsFrom ((Gen.expoBTA0_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA0_facts0 V1)) Gen.expoBTA0_items0) = Gen.expoBTA0_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBTA0_items0 := by fns_okB Gen.expoBTA0_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := tAK0) (L' := tAa1)
    (G := Gen.expoBTA0_facts1 V1) (items := Gen.expoBTA0_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoBTA0_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA0_facts1 V1)) Gen.expoBTA0_items1) = Gen.expoBTA0_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoBTA0_items1 := by fns_okB Gen.expoBTA0_items1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := tAa1) (L' := tAa2)
    (G := Gen.expoBTA0_facts2 V1) (items := Gen.expoBTA0_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoBTA0_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA0_facts2 V1)) Gen.expoBTA0_items2) = Gen.expoBTA0_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoBTA0_items2 := by fns_okB Gen.expoBTA0_items2
  obtain ⟨c2, k3⟩ := kpiece_lit (L := tAa2) (L' := tAa3)
    (G := Gen.expoBTA0_facts3 V1) (items := Gen.expoBTA0_items2) hG2 hk2 k2 hf2 hn3
  exact ⟨⟨⟨c0, c1⟩, c2⟩, k3⟩

/-- The tail's second start kinds after path A: the unpacked low half has the kind of the path's
register `4667`. -/
def tAK1 : List (Nat × Kd) :=
  kList tAKeys1 (fun r => if r == 4905 then kOf tAa3 4667 else kOf tAa3 r)

@[irreducible] def tAb1 : List (Nat × Kd) :=
  kList ((Gen.expoBTA1_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAK1) Gen.expoBTA1_items0)
@[irreducible] def tAb2 : List (Nat × Kd) :=
  kList ((Gen.expoBTA1_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAb1) Gen.expoBTA1_items1)
@[irreducible] def tAb3 : List (Nat × Kd) :=
  kList ((Gen.expoBTA1_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAb2) Gen.expoBTA1_items2)
@[irreducible] def tAb4 : List (Nat × Kd) :=
  kList ((Gen.expoBTA1_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tAb3) Gen.expoBTA1_items3)

theorem expoBTA1_kok (V : Nat → Value) :
    (kOk (kOf tAK1) Gen.expoBTA1_items0 &&
      kNext tAK1 Gen.expoBTA1_items0 ((Gen.expoBTA1_facts1 V).map Prod.fst) tAb1 &&
      kOk (kOf tAb1) Gen.expoBTA1_items1 &&
      kNext tAb1 Gen.expoBTA1_items1 ((Gen.expoBTA1_facts2 V).map Prod.fst) tAb2 &&
      kOk (kOf tAb2) Gen.expoBTA1_items2 &&
      kNext tAb2 Gen.expoBTA1_items2 ((Gen.expoBTA1_facts3 V).map Prod.fst) tAb3 &&
      kOk (kOf tAb3) Gen.expoBTA1_items3 &&
      kNext tAb3 Gen.expoBTA1_items3 ((Gen.expoBTA1_facts4 V).map Prod.fst) tAb4) = true := by
  unfold tAK1
  kernel_rfl

theorem expoBTA1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf tAK1 r).Has (lookupD (Gen.expoBTA1_facts0 V1) r)) :
    Gen.expoBTA1_cond V1 ∧ ∀ r, (kOf tAb4 r).Has (lookupD (Gen.expoBTA1_facts4 V1) r) := by
  have h8 := expoBTA1_kok V1
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
  have hG0 : factsFrom ((Gen.expoBTA1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA1_facts0 V1)) Gen.expoBTA1_items0) = Gen.expoBTA1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBTA1_items0 := by fns_okB Gen.expoBTA1_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := tAK1) (L' := tAb1)
    (G := Gen.expoBTA1_facts1 V1) (items := Gen.expoBTA1_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoBTA1_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA1_facts1 V1)) Gen.expoBTA1_items1) = Gen.expoBTA1_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoBTA1_items1 := by fns_okB Gen.expoBTA1_items1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := tAb1) (L' := tAb2)
    (G := Gen.expoBTA1_facts2 V1) (items := Gen.expoBTA1_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoBTA1_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA1_facts2 V1)) Gen.expoBTA1_items2) = Gen.expoBTA1_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoBTA1_items2 := by fns_okB Gen.expoBTA1_items2
  obtain ⟨c2, k3⟩ := kpiece_lit (L := tAb2) (L' := tAb3)
    (G := Gen.expoBTA1_facts3 V1) (items := Gen.expoBTA1_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.expoBTA1_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTA1_facts3 V1)) Gen.expoBTA1_items3) = Gen.expoBTA1_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.expoBTA1_items3 := by fns_okB Gen.expoBTA1_items3
  obtain ⟨c3, k4⟩ := kpiece_lit (L := tAb3) (L' := tAb4)
    (G := Gen.expoBTA1_facts4 V1) (items := Gen.expoBTA1_items3) hG3 hk3 k3 hf3 hn4
  exact ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, k4⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
