-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE0
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainSw
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # A plain round's exponent stretch: the kinds through runs 1 and 2

Each run after a software `exp2` site starts from the lookup in the site's outputs (`.float` of
the lane reading, kind `fl`), the defining site's constants (no kind) and the previous run's end
facts, whose kinds the previous run's check gives (`kinds_pre`). The runs' conditions then hold
by their literal kind lists, as for run 0 (`expoP1_ok`, `expoP2_ok`; runs 3 and 4 in
`StepsPlainE1b.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem lookup_none_keys {α : Type} {r : Nat} :
    ∀ {l : List (Nat × α)}, l.lookup r = none ↔ r ∉ l.map Prod.fst
  | [] => by simp
  | (a, x) :: l => by
    by_cases h : r = a
    · subst h; simp [List.lookup]
    · have hb : (r == a) = false := by simpa using h
      simp only [List.lookup, hb, List.map_cons, List.mem_cons, h, false_or]
      exact lookup_none_keys

/-- **Kinds after a prefix of written values**: a prefix whose own kinds hold, in front of facts
whose kinds hold. -/
theorem kinds_pre {pre G : List (Nat × Value)} {preK qK : List (Nat × Kd)}
    (hkeys : pre.map Prod.fst = preK.map Prod.fst)
    (hpre : ∀ r x, pre.lookup r = some x → (kOf (preK ++ qK) r).Has x)
    (hG : ∀ r, (kOf qK r).Has (lookupD G r)) :
    ∀ r, (kOf (preK ++ qK) r).Has (lookupD (pre ++ G) r) := by
  intro r
  cases h : pre.lookup r with
  | some x =>
    have := hpre r x h
    simp only [lookupD, List.lookup_append, h, Option.some_or, Option.getD_some]
    exact this
  | none =>
    have hk : preK.lookup r = none := by
      rw [lookup_none_keys, ← hkeys, ← lookup_none_keys]; exact h
    simp only [lookupD, kOf, List.lookup_append, h, hk, Option.none_or] at hG ⊢
    exact hG r

/-- The defining site's constant registers. -/
def constRegs : List Nat := [5666, 8766, 5667, 8770, 5668, 8771, 5669, 8773, 5670, 8775]

/-- The kinds the template outputs carry (kind `fl`) in front of a run's start. -/
def swK (os : List Nat) : List (Nat × Kd) := os.map fun o => (o, .s .fl)

/-- The kind lists' entries without a kind (the constants). -/
def noK (os : List Nat) : List (Nat × Kd) := os.map fun o => (o, .no)

theorem fl_laneR (x : Value) : SK.fl.Has (Value.float .f32 (laneR x)) := has_float_fl _

/-- The prefix property for two written values. -/
theorem pre2 {a b : Nat} {va vb : Value} {K : List (Nat × Kd)} (ha : (kOf K a).Has va)
    (hb : (kOf K b).Has vb) : ∀ r x, [(a, va), (b, vb)].lookup r = some x → (kOf K r).Has x := by
  intro r x h
  have hm := mem_of_lookup h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ha
  · exact hb

/-- The prefix property for constants without a kind. -/
theorem preNo {l : List (Nat × Value)} {K : List (Nat × Kd)}
    (hK : (l.map Prod.fst).all (fun r => decide (kOf K r = .no)) = true) :
    ∀ r x, l.lookup r = some x → (kOf K r).Has x := by
  intro r x h
  have hm := List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h)
  have := List.all_eq_true.mp hK r hm
  simp only [decide_eq_true_eq] at this
  rw [this]; trivial

/-- The prefix property of an appended prefix. -/
theorem preApp {l₁ l₂ : List (Nat × Value)} {K : List (Nat × Kd)}
    (h₁ : ∀ r x, l₁.lookup r = some x → (kOf K r).Has x)
    (h₂ : ∀ r x, l₂.lookup r = some x → (kOf K r).Has x) :
    ∀ r x, (l₁ ++ l₂).lookup r = some x → (kOf K r).Has x := by
  intro r x h
  rw [List.lookup_append] at h
  cases h1 : l₁.lookup r with
  | some y => rw [h1] at h; simp only [Option.some_or, Option.some.injEq] at h; subst h
              exact h₁ r y h1
  | none => rw [h1, Option.none_or] at h; exact h₂ r x h

/-- The prefix check for a site's two outputs. -/
macro "pre_kinds" : tactic => `(tactic| (
  unfold swOut
  exact pre2 (by rw [show kOf _ _ = Kd.s .fl by kernel_rfl]; exact fl_laneR _)
    (by rw [show kOf _ _ = Kd.s .fl by kernel_rfl]; exact fl_laneR _)))



/-- The kinds at run 1's start (template outputs, then the previous run's end kinds). -/
def expoP1K : List (Nat × Kd) :=
  kList ((Gen.expoP1_facts0 fun _ => .pred false).map Prod.fst)
    (kOf (swK [5134, 5137] ++ (swK [5128, 5131] ++ noK constRegs ++ qL7)))

theorem expoP1_keys (V : Nat → Value) : (Gen.expoP1_facts0 V).map Prod.fst =
    (Gen.expoP1_facts0 fun _ => .pred false).map Prod.fst := by
  kernel_rfl

theorem expoP1_facts0_eq (V : Nat → Value) :
    Gen.expoP1_facts0 V = factsFrom ((Gen.expoP1_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The run's items read no role function but the conversions. -/
macro "fns_okexpoP1" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expoP1_items0, and_true,
    true_and]
  repeat' first | exact Gen.packE_spec | exact Gen.widenE_spec | constructor))

@[irreducible] def r1L1 : List (Nat × Kd) :=
  kList ((Gen.expoP1_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoP1K) Gen.expoP1_items0)

theorem expoP1_kok (V : Nat → Value) :
    (kOk (kOf expoP1K) Gen.expoP1_items0 &&
      kNext expoP1K Gen.expoP1_items0 ((Gen.expoP1_facts1 V).map Prod.fst) r1L1) = true := by
  unfold expoP1K
  kernel_rfl

theorem expoP1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoP1K r).Has (lookupD (Gen.expoP1_facts0 V1) r)) :
    Gen.expoP1_cond V1 ∧ ∀ r, (kOf r1L1 r).Has (lookupD (Gen.expoP1_facts1 V1) r) := by
  have h2 := expoP1_kok V1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoP1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP1_facts0 V1)) Gen.expoP1_items0) = Gen.expoP1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoP1_items0 := by fns_okexpoP1
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoP1K) (L' := r1L1) (G := Gen.expoP1_facts1 V1)
    (items := Gen.expoP1_items0) hG0 hk0 k0 hf0 hn1
  exact ⟨c0, k1⟩

/-- The kinds at run 2's start (template outputs, then the previous run's end kinds). -/
def expoP2K : List (Nat × Kd) :=
  kList ((Gen.expoP2_facts0 fun _ => .pred false).map Prod.fst)
    (kOf (swK [5146, 5149] ++ (swK [5140, 5143] ++ r1L1)))

theorem expoP2_keys (V : Nat → Value) : (Gen.expoP2_facts0 V).map Prod.fst =
    (Gen.expoP2_facts0 fun _ => .pred false).map Prod.fst := by
  kernel_rfl

theorem expoP2_facts0_eq (V : Nat → Value) :
    Gen.expoP2_facts0 V = factsFrom ((Gen.expoP2_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The run's items read no role function but the conversions. -/
macro "fns_okexpoP2" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expoP2_items0, Gen.expoP2_items1, and_true,
    true_and]
  repeat' first | exact Gen.packE_spec | exact Gen.widenE_spec | constructor))

@[irreducible] def r2L1 : List (Nat × Kd) :=
  kList ((Gen.expoP2_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoP2K) Gen.expoP2_items0)
@[irreducible] def r2L2 : List (Nat × Kd) :=
  kList ((Gen.expoP2_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf r2L1) Gen.expoP2_items1)

theorem expoP2_kok (V : Nat → Value) :
    (kOk (kOf expoP2K) Gen.expoP2_items0 &&
      kNext expoP2K Gen.expoP2_items0 ((Gen.expoP2_facts1 V).map Prod.fst) r2L1 &&
      kOk (kOf r2L1) Gen.expoP2_items1 &&
      kNext r2L1 Gen.expoP2_items1 ((Gen.expoP2_facts2 V).map Prod.fst) r2L2) = true := by
  unfold expoP2K
  kernel_rfl

theorem expoP2_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoP2K r).Has (lookupD (Gen.expoP2_facts0 V1) r)) :
    Gen.expoP2_cond V1 ∧ ∀ r, (kOf r2L2 r).Has (lookupD (Gen.expoP2_facts2 V1) r) := by
  have h4 := expoP2_kok V1
  have hn2 := (band_split h4).2
  have h3 := (band_split h4).1
  have hk1 := (band_split h3).2
  have h2 := (band_split h3).1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.expoP2_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP2_facts0 V1)) Gen.expoP2_items0) = Gen.expoP2_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoP2_items0 := by fns_okexpoP2
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoP2K) (L' := r2L1) (G := Gen.expoP2_facts1 V1)
    (items := Gen.expoP2_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoP2_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP2_facts1 V1)) Gen.expoP2_items1) = Gen.expoP2_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoP2_items1 := by fns_okexpoP2
  obtain ⟨c1, k2⟩ := kpiece_lit (L := r2L1) (L' := r2L2) (G := Gen.expoP2_facts2 V1)
    (items := Gen.expoP2_items1) hG1 hk1 k1 hf1 hn2
  exact ⟨⟨c0, c1⟩, k2⟩
theorem expoP1_ok (hp : Pre p L m) (v : V) : Gen.expoP1_cond (lookupD (expoPS1 p v)) ∧
    ∀ r, (kOf r1L1 r).Has (lookupD (Gen.expoP1_facts1 (lookupD (expoPS1 p v))) r) := by
  have hall : ∀ r,
      (kOf (swK [5134, 5137] ++ (swK [5128, 5131] ++ noK constRegs ++ qL7)) r).Has
      (lookupD (expoPS1 p v) r) := by
    unfold expoPS1
    refine kinds_pre (by kernel_rfl) (by pre_kinds) ?_
    exact kinds_pre
      (pre := swOut (lookupD (expoPS0 p v)) 5564 5565 5128 5131 ++ cuteConsts)
      (preK := swK [5128, 5131] ++ noK constRegs) (by kernel_rfl)
      (preApp (by pre_kinds) (preNo (by kernel_rfl))) (expoP0_ok hp v).2
  have k0 : ∀ r, (kOf expoP1K r).Has
      (lookupD (Gen.expoP1_facts0 (lookupD (expoPS1 p v))) r) := by
    rw [expoP1_facts0_eq, expoP1_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  exact expoP1_chain _ k0

theorem expoP2_ok (hp : Pre p L m) (v : V) : Gen.expoP2_cond (lookupD (expoPS3 p v)) ∧
    ∀ r, (kOf r2L2 r).Has (lookupD (Gen.expoP2_facts2 (lookupD (expoPS3 p v))) r) := by
  have hall : ∀ r, (kOf (swK [5146, 5149] ++ (swK [5140, 5143] ++ r1L1)) r).Has
      (lookupD (expoPS3 p v) r) := by
    unfold expoPS3
    refine kinds_pre (by kernel_rfl) (by pre_kinds) ?_
    exact kinds_pre (by kernel_rfl) (by pre_kinds) (expoP1_ok hp v).2
  have k0 : ∀ r, (kOf expoP2K r).Has
      (lookupD (Gen.expoP2_facts0 (lookupD (expoPS3 p v))) r) := by
    rw [expoP2_facts0_eq, expoP2_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  exact expoP2_chain _ k0

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
