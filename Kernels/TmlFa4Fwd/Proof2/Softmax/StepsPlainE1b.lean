-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainE1

@[expose] public section

/-! # A plain round's exponent stretch: the kinds through runs 3 and 4

Each run after a software `exp2` site starts from the lookup in the site's outputs (`.float` of
the lane reading, kind `fl`), the defining site's constants (no kind) and the previous run's end
facts, whose kinds the previous run's check gives (`kinds_pre`). The runs' conditions then hold
by their literal kind lists (`expoP3_ok`, `expoP4_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The kinds at run 3's start (template outputs, then the previous run's end kinds). -/
def expoP3K : List (Nat × Kd) :=
  kList ((Gen.expoP3_facts0 fun _ => .pred false).map Prod.fst)
    (kOf (swK [5158, 5161] ++ (swK [5152, 5155] ++ r2L2)))

theorem expoP3_keys (V : Nat → Value) : (Gen.expoP3_facts0 V).map Prod.fst =
    (Gen.expoP3_facts0 fun _ => .pred false).map Prod.fst := by
  kernel_rfl

theorem expoP3_facts0_eq (V : Nat → Value) :
    Gen.expoP3_facts0 V = factsFrom ((Gen.expoP3_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The run's items read no role function but the conversions. -/
macro "fns_okexpoP3" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expoP3_items0, and_true,
    true_and]
  repeat' first | exact Gen.packE_spec | exact Gen.widenE_spec | constructor))

@[irreducible] def r3L1 : List (Nat × Kd) :=
  kList ((Gen.expoP3_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoP3K) Gen.expoP3_items0)

theorem expoP3_kok (V : Nat → Value) :
    (kOk (kOf expoP3K) Gen.expoP3_items0 &&
      kNext expoP3K Gen.expoP3_items0 ((Gen.expoP3_facts1 V).map Prod.fst) r3L1) = true := by
  unfold expoP3K
  kernel_rfl

theorem expoP3_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoP3K r).Has (lookupD (Gen.expoP3_facts0 V1) r)) :
    Gen.expoP3_cond V1 ∧ ∀ r, (kOf r3L1 r).Has (lookupD (Gen.expoP3_facts1 V1) r) := by
  have h2 := expoP3_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoP3_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP3_facts0 V1)) Gen.expoP3_items0) = Gen.expoP3_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoP3_items0 := by fns_okexpoP3
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoP3K) (L' := r3L1) (G := Gen.expoP3_facts1 V1)
    (items := Gen.expoP3_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The kinds at run 4's start (template outputs, then the previous run's end kinds). -/
def expoP4K : List (Nat × Kd) :=
  kList ((Gen.expoP4_facts0 fun _ => .pred false).map Prod.fst)
    (kOf (swK [5170, 5173] ++ (swK [5164, 5167] ++ r3L1)))

theorem expoP4_keys (V : Nat → Value) : (Gen.expoP4_facts0 V).map Prod.fst =
    (Gen.expoP4_facts0 fun _ => .pred false).map Prod.fst := by
  kernel_rfl

theorem expoP4_facts0_eq (V : Nat → Value) :
    Gen.expoP4_facts0 V = factsFrom ((Gen.expoP4_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The run's items read no role function but the conversions. -/
macro "fns_okexpoP4" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expoP4_items0, Gen.expoP4_items1, Gen.expoP4_items2, and_true,
    true_and]
  repeat' first | exact Gen.packE_spec | exact Gen.widenE_spec | constructor))

@[irreducible] def r4L1 : List (Nat × Kd) :=
  kList ((Gen.expoP4_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoP4K) Gen.expoP4_items0)
@[irreducible] def r4L2 : List (Nat × Kd) :=
  kList ((Gen.expoP4_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf r4L1) Gen.expoP4_items1)
@[irreducible] def r4L3 : List (Nat × Kd) :=
  kList ((Gen.expoP4_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf r4L2) Gen.expoP4_items2)

theorem expoP4_kok (V : Nat → Value) :
    (kOk (kOf expoP4K) Gen.expoP4_items0 &&
      kNext expoP4K Gen.expoP4_items0 ((Gen.expoP4_facts1 V).map Prod.fst) r4L1 &&
      kOk (kOf r4L1) Gen.expoP4_items1 &&
      kNext r4L1 Gen.expoP4_items1 ((Gen.expoP4_facts2 V).map Prod.fst) r4L2 &&
      kOk (kOf r4L2) Gen.expoP4_items2 &&
      kNext r4L2 Gen.expoP4_items2 ((Gen.expoP4_facts3 V).map Prod.fst) r4L3) = true := by
  unfold expoP4K
  kernel_rfl

theorem expoP4_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoP4K r).Has (lookupD (Gen.expoP4_facts0 V1) r)) :
    Gen.expoP4_cond V1 ∧ ∀ r, (kOf r4L3 r).Has (lookupD (Gen.expoP4_facts3 V1) r) := by
  have h6 := expoP4_kok V1
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
  have hG0 : factsFrom ((Gen.expoP4_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP4_facts0 V1)) Gen.expoP4_items0) = Gen.expoP4_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoP4_items0 := by fns_okexpoP4
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoP4K) (L' := r4L1) (G := Gen.expoP4_facts1 V1)
    (items := Gen.expoP4_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoP4_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP4_facts1 V1)) Gen.expoP4_items1) = Gen.expoP4_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoP4_items1 := by fns_okexpoP4
  obtain ⟨c1, k2⟩ := kpiece_lit (L := r4L1) (L' := r4L2) (G := Gen.expoP4_facts2 V1)
    (items := Gen.expoP4_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoP4_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP4_facts2 V1)) Gen.expoP4_items2) = Gen.expoP4_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoP4_items2 := by fns_okexpoP4
  obtain ⟨c2, k3⟩ := kpiece_lit (L := r4L2) (L' := r4L3) (G := Gen.expoP4_facts3 V1)
    (items := Gen.expoP4_items2) hG2 hk2 k2 hf2 hn3
  exact ⟨⟨⟨c0, c1⟩, c2⟩, k3⟩

theorem expoP3_ok (hp : Pre p L m) (v : V) : Gen.expoP3_cond (lookupD (expoPS5 p v)) ∧
    ∀ r, (kOf r3L1 r).Has (lookupD (Gen.expoP3_facts1 (lookupD (expoPS5 p v))) r) := by
  have hall : ∀ r, (kOf (swK [5158, 5161] ++ (swK [5152, 5155] ++ r2L2)) r).Has
      (lookupD (expoPS5 p v) r) := by
    unfold expoPS5
    refine kinds_pre (by kernel_rfl) (by pre_kinds) ?_
    exact kinds_pre (by kernel_rfl) (by pre_kinds) (expoP2_ok hp v).2
  have k0 : ∀ r, (kOf expoP3K r).Has
      (lookupD (Gen.expoP3_facts0 (lookupD (expoPS5 p v))) r) := by
    rw [expoP3_facts0_eq, expoP3_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  exact expoP3_chain _ k0

theorem expoP4_ok (hp : Pre p L m) (v : V) : Gen.expoP4_cond (lookupD (expoPS7 p v)) ∧
    ∀ r, (kOf r4L3 r).Has (lookupD (Gen.expoP4_facts3 (lookupD (expoPS7 p v))) r) := by
  have hall : ∀ r, (kOf (swK [5170, 5173] ++ (swK [5164, 5167] ++ r3L1)) r).Has
      (lookupD (expoPS7 p v) r) := by
    unfold expoPS7
    refine kinds_pre (by kernel_rfl) (by pre_kinds) ?_
    exact kinds_pre (by kernel_rfl) (by pre_kinds) (expoP3_ok hp v).2
  have k0 : ∀ r, (kOf expoP4K r).Has
      (lookupD (Gen.expoP4_facts0 (lookupD (expoPS7 p v))) r) := by
    rw [expoP4_facts0_eq, expoP4_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  exact expoP4_chain _ k0

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
