-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoB0
public import Kernels.TmlFa4Fwd.Proof.Softmax.NegScale
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarrB
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsMaxB
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarrBChain
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the scaled products

The run `Gen.expoB0_run` (pcs 5684 to 5814) from the values of the bias round's named-barrier
arrival (`narr .bias`): the subtracted maximum times the negated scale, the products' `fma2` with
the scale pair, and the 128 unpacked exponents. Its condition holds by the kinds of its start
values (`expoB0_ok`), and every register after it has the kind the checker computes
(`expoB0_kinds`: the exponents are reals or `-∞`). The values stay the run's generated terms; the
software `exp2` lanes read them by their kinds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The bias round's named-barrier arrival. -/
abbrev narrB (v : V) : D := ⟨.narr .bias, v, 0, []⟩

theorem valueOfD_narrB_statB (v : V) : valueOfD p L g (narrB v) = valueOfD p L g (statB v) := rfl

theorem bits0_fl : SK.fl.Has (.bits 32 (BitVec.ofNat 64 0)) := by
  refine ⟨?_, 0, readEReal_zero32⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ h; cases h; decide

theorem erealValue_fl {x : EReal} (h0 : x ≠ ⊥) (h1 : x < ⊤) : SK.fl.Has (erealValue .f32 x) := by
  rw [show x = ((x.toReal : ℝ) : EReal) from (EReal.coe_toReal h1.ne h0).symm, erealValue_coe]
  exact has_float_fl _

/-- The subtracted maximum is a number. -/
theorem statB_4565_fl (v : V) : SK.fl.Has (valueOfD p L g (statB v) 4565) := by
  rw [statB_4565]
  cases v.mf
  · show SK.fl.Has (if foldBE p v = ⊥ then _ else _)
    split
    · exact bits0_fl
    · exact erealValue_fl (by assumption) (foldBE_lt_top p v)
  · show SK.fl.Has (if keepB p v = true then _ else _)
    split <;> exact has_float_fl _

/-- The kinds of the run's start values. -/
def expoB0K : List (Nat × Kd) :=
  (1230, .s .fl) :: (4565, .s .fl) :: (7132, .s .pw) ::
    (List.range 64).map fun j => (8317 + 2 * j, .pr .ni)

theorem expoB0K_has (hp : Pre p L m) (v : V) :
    ∀ q ∈ expoB0K, q.2.Has (valueOfD p L g (narrB v) q.1) := by
  obtain ⟨s, hS, hs0, h32⟩ := scale_word hp
  intro q hq
  rw [valueOfD_narrB_statB]
  simp only [expoB0K, List.mem_cons, List.mem_map, List.mem_range] at hq
  rcases hq with rfl | rfl | rfl | ⟨j, hj, rfl⟩
  · show SK.fl.Has _
    exact has_float_fl _
  · exact statB_4565_fl v
  · show SK.pw.Has _
    rw [valueOfD_ctl _ (by rfl : ctl 7132 = true)]
    exact paramW_pw hS hs0 h32
  · show (Kd.pr .ni).Has _
    rw [statB_prod v hj]
    exact pair_has (ni_bv32 _ _ _) (ni_bv32 _ _ _)

theorem expoB0_facts0_eq (V : Nat → Value) :
    Gen.expoB0_facts0 V = factsFrom ((Gen.expoB0_facts0 V).map Prod.fst) V := by
  kernel_rfl

macro "fns_okexpoB0" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expoB0_items0, Gen.expoB0_items1, Gen.expoB0_items2,
    Gen.expoB0_items3, Gen.expoB0_items4, and_true, true_and]
  repeat' first | exact maxE_maxSpec | constructor))

@[irreducible] def eB1 : List (Nat × Kd) :=
  kList ((Gen.expoB0_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoB0K) Gen.expoB0_items0)
@[irreducible] def eB2 : List (Nat × Kd) :=
  kList ((Gen.expoB0_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf eB1) Gen.expoB0_items1)
@[irreducible] def eB3 : List (Nat × Kd) :=
  kList ((Gen.expoB0_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf eB2) Gen.expoB0_items2)
@[irreducible] def eB4 : List (Nat × Kd) :=
  kList ((Gen.expoB0_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf eB3) Gen.expoB0_items3)
@[irreducible] def eB5 : List (Nat × Kd) :=
  kList ((Gen.expoB0_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf eB4) Gen.expoB0_items4)

theorem expoB0_kok (V : Nat → Value) :
    (kOk (kOf expoB0K) Gen.expoB0_items0 &&
      kNext expoB0K Gen.expoB0_items0 ((Gen.expoB0_facts1 V).map Prod.fst) eB1 &&
      kOk (kOf eB1) Gen.expoB0_items1 &&
      kNext eB1 Gen.expoB0_items1 ((Gen.expoB0_facts2 V).map Prod.fst) eB2 &&
      kOk (kOf eB2) Gen.expoB0_items2 &&
      kNext eB2 Gen.expoB0_items2 ((Gen.expoB0_facts3 V).map Prod.fst) eB3 &&
      kOk (kOf eB3) Gen.expoB0_items3 &&
      kNext eB3 Gen.expoB0_items3 ((Gen.expoB0_facts4 V).map Prod.fst) eB4 &&
      kOk (kOf eB4) Gen.expoB0_items4 &&
      kNext eB4 Gen.expoB0_items4 ((Gen.expoB0_facts5 V).map Prod.fst) eB5) = true := by
  unfold expoB0K
  kernel_rfl

theorem expoB0_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoB0K r).Has (lookupD (Gen.expoB0_facts0 V1) r)) :
    Gen.expoB0_cond V1 ∧ ∀ r, (kOf eB5 r).Has (lookupD (Gen.expoB0_facts5 V1) r) := by
  have h10 := expoB0_kok V1
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
  have hG0 : factsFrom ((Gen.expoB0_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoB0_facts0 V1)) Gen.expoB0_items0) = Gen.expoB0_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoB0_items0 := by fns_okexpoB0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoB0K) (L' := eB1) (G := Gen.expoB0_facts1 V1)
    (items := Gen.expoB0_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoB0_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoB0_facts1 V1)) Gen.expoB0_items1) = Gen.expoB0_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoB0_items1 := by fns_okexpoB0
  obtain ⟨c1, k2⟩ := kpiece_lit (L := eB1) (L' := eB2) (G := Gen.expoB0_facts2 V1)
    (items := Gen.expoB0_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoB0_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoB0_facts2 V1)) Gen.expoB0_items2) = Gen.expoB0_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoB0_items2 := by fns_okexpoB0
  obtain ⟨c2, k3⟩ := kpiece_lit (L := eB2) (L' := eB3) (G := Gen.expoB0_facts3 V1)
    (items := Gen.expoB0_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.expoB0_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoB0_facts3 V1)) Gen.expoB0_items3) = Gen.expoB0_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.expoB0_items3 := by fns_okexpoB0
  obtain ⟨c3, k4⟩ := kpiece_lit (L := eB3) (L' := eB4) (G := Gen.expoB0_facts4 V1)
    (items := Gen.expoB0_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.expoB0_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoB0_facts4 V1)) Gen.expoB0_items4) = Gen.expoB0_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.expoB0_items4 := by fns_okexpoB0
  obtain ⟨c4, k5⟩ := kpiece_lit (L := eB4) (L' := eB5) (G := Gen.expoB0_facts5 V1)
    (items := Gen.expoB0_items4) hG4 hk4 k4 hf4 hn5
  exact ⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, k5⟩

theorem expoB0_ok (hp : Pre p L m) (v : V) :
    Gen.expoB0_cond (valueOfD p L g (narrB v)) ∧
      ∀ r, (kOf eB5 r).Has (lookupD (Gen.expoB0_facts5 (valueOfD p L g (narrB v))) r) := by
  refine expoB0_chain _ ?_
  rw [expoB0_facts0_eq]
  exact kstart (by kernel_rfl) (expoB0K_has hp v)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
