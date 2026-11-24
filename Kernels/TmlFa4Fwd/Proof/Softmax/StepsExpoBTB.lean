-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK2
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBT
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the tail's kinds after the software path -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The tail's first start kinds after path B. -/
def tBK0 : List (Nat × Kd) :=
  kList ((Gen.expoBTB0_facts0 fun _ => .pred false).map Prod.fst) (kOf bB8_1)

@[irreducible] def tBa1 : List (Nat × Kd) :=
  kList ((Gen.expoBTB0_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBK0) Gen.expoBTB0_items0)
@[irreducible] def tBa2 : List (Nat × Kd) :=
  kList ((Gen.expoBTB0_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBa1) Gen.expoBTB0_items1)
@[irreducible] def tBa3 : List (Nat × Kd) :=
  kList ((Gen.expoBTB0_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBa2) Gen.expoBTB0_items2)

theorem expoBTB0_kok (V : Nat → Value) :
    (kOk (kOf tBK0) Gen.expoBTB0_items0 &&
      kNext tBK0 Gen.expoBTB0_items0 ((Gen.expoBTB0_facts1 V).map Prod.fst) tBa1 &&
      kOk (kOf tBa1) Gen.expoBTB0_items1 &&
      kNext tBa1 Gen.expoBTB0_items1 ((Gen.expoBTB0_facts2 V).map Prod.fst) tBa2 &&
      kOk (kOf tBa2) Gen.expoBTB0_items2 &&
      kNext tBa2 Gen.expoBTB0_items2 ((Gen.expoBTB0_facts3 V).map Prod.fst) tBa3) = true := by
  unfold tBK0
  kernel_rfl

theorem expoBTB0_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf tBK0 r).Has (lookupD (Gen.expoBTB0_facts0 V1) r)) :
    Gen.expoBTB0_cond V1 ∧ ∀ r, (kOf tBa3 r).Has (lookupD (Gen.expoBTB0_facts3 V1) r) := by
  have h6 := expoBTB0_kok V1
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
  have hG0 : factsFrom ((Gen.expoBTB0_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB0_facts0 V1)) Gen.expoBTB0_items0) = Gen.expoBTB0_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBTB0_items0 := by fns_okB Gen.expoBTB0_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := tBK0) (L' := tBa1)
    (G := Gen.expoBTB0_facts1 V1) (items := Gen.expoBTB0_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoBTB0_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB0_facts1 V1)) Gen.expoBTB0_items1) = Gen.expoBTB0_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoBTB0_items1 := by fns_okB Gen.expoBTB0_items1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := tBa1) (L' := tBa2)
    (G := Gen.expoBTB0_facts2 V1) (items := Gen.expoBTB0_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoBTB0_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB0_facts2 V1)) Gen.expoBTB0_items2) = Gen.expoBTB0_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoBTB0_items2 := by fns_okB Gen.expoBTB0_items2
  obtain ⟨c2, k3⟩ := kpiece_lit (L := tBa2) (L' := tBa3)
    (G := Gen.expoBTB0_facts3 V1) (items := Gen.expoBTB0_items2) hG2 hk2 k2 hf2 hn3
  exact ⟨⟨⟨c0, c1⟩, c2⟩, k3⟩

/-- The tail's second start kinds after path B: the unpacked low half has the kind of the path's
register `4710`. -/
def tBK1 : List (Nat × Kd) :=
  kList tBKeys1 (fun r => if r == 4905 then kOf tBa3 4710 else kOf tBa3 r)

@[irreducible] def tBb1 : List (Nat × Kd) :=
  kList ((Gen.expoBTB1_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBK1) Gen.expoBTB1_items0)
@[irreducible] def tBb2 : List (Nat × Kd) :=
  kList ((Gen.expoBTB1_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBb1) Gen.expoBTB1_items1)
@[irreducible] def tBb3 : List (Nat × Kd) :=
  kList ((Gen.expoBTB1_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBb2) Gen.expoBTB1_items2)
@[irreducible] def tBb4 : List (Nat × Kd) :=
  kList ((Gen.expoBTB1_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf tBb3) Gen.expoBTB1_items3)

theorem expoBTB1_kok (V : Nat → Value) :
    (kOk (kOf tBK1) Gen.expoBTB1_items0 &&
      kNext tBK1 Gen.expoBTB1_items0 ((Gen.expoBTB1_facts1 V).map Prod.fst) tBb1 &&
      kOk (kOf tBb1) Gen.expoBTB1_items1 &&
      kNext tBb1 Gen.expoBTB1_items1 ((Gen.expoBTB1_facts2 V).map Prod.fst) tBb2 &&
      kOk (kOf tBb2) Gen.expoBTB1_items2 &&
      kNext tBb2 Gen.expoBTB1_items2 ((Gen.expoBTB1_facts3 V).map Prod.fst) tBb3 &&
      kOk (kOf tBb3) Gen.expoBTB1_items3 &&
      kNext tBb3 Gen.expoBTB1_items3 ((Gen.expoBTB1_facts4 V).map Prod.fst) tBb4) = true := by
  unfold tBK1
  kernel_rfl

theorem expoBTB1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf tBK1 r).Has (lookupD (Gen.expoBTB1_facts0 V1) r)) :
    Gen.expoBTB1_cond V1 ∧ ∀ r, (kOf tBb4 r).Has (lookupD (Gen.expoBTB1_facts4 V1) r) := by
  have h8 := expoBTB1_kok V1
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
  have hG0 : factsFrom ((Gen.expoBTB1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB1_facts0 V1)) Gen.expoBTB1_items0) = Gen.expoBTB1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBTB1_items0 := by fns_okB Gen.expoBTB1_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := tBK1) (L' := tBb1)
    (G := Gen.expoBTB1_facts1 V1) (items := Gen.expoBTB1_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoBTB1_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB1_facts1 V1)) Gen.expoBTB1_items1) = Gen.expoBTB1_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoBTB1_items1 := by fns_okB Gen.expoBTB1_items1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := tBb1) (L' := tBb2)
    (G := Gen.expoBTB1_facts2 V1) (items := Gen.expoBTB1_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoBTB1_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB1_facts2 V1)) Gen.expoBTB1_items2) = Gen.expoBTB1_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoBTB1_items2 := by fns_okB Gen.expoBTB1_items2
  obtain ⟨c2, k3⟩ := kpiece_lit (L := tBb2) (L' := tBb3)
    (G := Gen.expoBTB1_facts3 V1) (items := Gen.expoBTB1_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.expoBTB1_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBTB1_facts3 V1)) Gen.expoBTB1_items3) = Gen.expoBTB1_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.expoBTB1_items3 := by fns_okB Gen.expoBTB1_items3
  obtain ⟨c3, k4⟩ := kpiece_lit (L := tBb3) (L' := tBb4)
    (G := Gen.expoBTB1_facts4 V1) (items := Gen.expoBTB1_items3) hG3 hk3 k3 hf3 hn4
  exact ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, k4⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
