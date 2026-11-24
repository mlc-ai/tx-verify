-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBA
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoB0
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the hardware path

The run `Gen.expoBA_run` (pcs 5816 to 5975, the round index at or above `%r301`): the hardware
`ex2` of the 128 exponents and their packs, from the scaled-product run's end. Its condition holds
by the kinds after that run (`expoBA_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The role readings of a run's items meet their specifications. -/
syntax "fns_okB " term : tactic
macro_rules
  | `(tactic| fns_okB $items) => `(tactic| (
      simp only [kFns, XItem.FnOk, $items:term, and_true, true_and]
      repeat' first | exact maxE_maxSpec | exact Gen.widenE_spec | exact Gen.packE_spec |
        constructor))

theorem mem_kList {keys : List Nat} {K : Nat → Kd} {p : Nat × Kd} (h : p ∈ kList keys K) :
    p.2 = K p.1 := by
  simp only [kList, List.mem_filterMap] at h
  obtain ⟨r, -, hr⟩ := h
  split at hr
  · cases hr
  · cases hr; rfl

/-- The start kinds: the scaled-product run's end kinds on the run's start registers. -/
def expoBAK : List (Nat × Kd) :=
  kList ((Gen.expoBA_facts0 fun _ => .pred false).map Prod.fst) (kOf eB5)

@[irreducible] def aB1 : List (Nat × Kd) :=
  kList ((Gen.expoBA_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoBAK) Gen.expoBA_items0)
@[irreducible] def aB2 : List (Nat × Kd) :=
  kList ((Gen.expoBA_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf aB1) Gen.expoBA_items1)
@[irreducible] def aB3 : List (Nat × Kd) :=
  kList ((Gen.expoBA_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf aB2) Gen.expoBA_items2)
@[irreducible] def aB4 : List (Nat × Kd) :=
  kList ((Gen.expoBA_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf aB3) Gen.expoBA_items3)
@[irreducible] def aB5 : List (Nat × Kd) :=
  kList ((Gen.expoBA_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf aB4) Gen.expoBA_items4)

theorem expoBA_kok (V : Nat → Value) :
    (kOk (kOf expoBAK) Gen.expoBA_items0 &&
      kNext expoBAK Gen.expoBA_items0 ((Gen.expoBA_facts1 V).map Prod.fst) aB1 &&
      kOk (kOf aB1) Gen.expoBA_items1 &&
      kNext aB1 Gen.expoBA_items1 ((Gen.expoBA_facts2 V).map Prod.fst) aB2 &&
      kOk (kOf aB2) Gen.expoBA_items2 &&
      kNext aB2 Gen.expoBA_items2 ((Gen.expoBA_facts3 V).map Prod.fst) aB3 &&
      kOk (kOf aB3) Gen.expoBA_items3 &&
      kNext aB3 Gen.expoBA_items3 ((Gen.expoBA_facts4 V).map Prod.fst) aB4 &&
      kOk (kOf aB4) Gen.expoBA_items4 &&
      kNext aB4 Gen.expoBA_items4 ((Gen.expoBA_facts5 V).map Prod.fst) aB5) = true := by
  unfold expoBAK
  kernel_rfl

theorem expoBA_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoBAK r).Has (lookupD (Gen.expoBA_facts0 V1) r)) :
    Gen.expoBA_cond V1 ∧ ∀ r, (kOf aB5 r).Has (lookupD (Gen.expoBA_facts5 V1) r) := by
  have h10 := expoBA_kok V1
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
  have hG0 : factsFrom ((Gen.expoBA_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBA_facts0 V1)) Gen.expoBA_items0) = Gen.expoBA_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoBA_items0 := by fns_okB Gen.expoBA_items0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoBAK) (L' := aB1)
    (G := Gen.expoBA_facts1 V1) (items := Gen.expoBA_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoBA_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBA_facts1 V1)) Gen.expoBA_items1) = Gen.expoBA_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoBA_items1 := by fns_okB Gen.expoBA_items1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := aB1) (L' := aB2)
    (G := Gen.expoBA_facts2 V1) (items := Gen.expoBA_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoBA_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBA_facts2 V1)) Gen.expoBA_items2) = Gen.expoBA_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoBA_items2 := by fns_okB Gen.expoBA_items2
  obtain ⟨c2, k3⟩ := kpiece_lit (L := aB2) (L' := aB3)
    (G := Gen.expoBA_facts3 V1) (items := Gen.expoBA_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.expoBA_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBA_facts3 V1)) Gen.expoBA_items3) = Gen.expoBA_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.expoBA_items3 := by fns_okB Gen.expoBA_items3
  obtain ⟨c3, k4⟩ := kpiece_lit (L := aB3) (L' := aB4)
    (G := Gen.expoBA_facts4 V1) (items := Gen.expoBA_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.expoBA_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoBA_facts4 V1)) Gen.expoBA_items4) = Gen.expoBA_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.expoBA_items4 := by fns_okB Gen.expoBA_items4
  obtain ⟨c4, k5⟩ := kpiece_lit (L := aB4) (L' := aB5)
    (G := Gen.expoBA_facts5 V1) (items := Gen.expoBA_items4) hG4 hk4 k4 hf4 hn5
  exact ⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, k5⟩

theorem expoBA_facts0_eq (V : Nat → Value) :
    Gen.expoBA_facts0 V = factsFrom ((Gen.expoBA_facts0 fun _ => .pred false).map Prod.fst) V := by
  kernel_rfl

/-- **The hardware path's condition**, from the values at the scaled-product run's end. -/
theorem expoBA_ok (hp : Pre p L m) (v : V) :
    Gen.expoBA_cond (lookupD (Gen.expoB0_facts5 (valueOfD p L g (narrB v)))) ∧
      ∀ r, (kOf aB5 r).Has (lookupD (Gen.expoBA_facts5
        (lookupD (Gen.expoB0_facts5 (valueOfD p L g (narrB v))))) r) := by
  have hk := (expoB0_ok (g := g) hp v).2
  refine expoBA_chain _ ?_
  rw [expoBA_facts0_eq]
  exact kstart (by unfold expoBAK; kernel_rfl) fun q hq => by rw [mem_kList hq]; exact hk q.1

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
