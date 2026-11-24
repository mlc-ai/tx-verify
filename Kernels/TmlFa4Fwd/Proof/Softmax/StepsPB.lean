-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasP
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKA
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKB
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBK8
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.PkB
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # A bias round's P part: the stores' unpacks

As the first round's (`StepsP1.lean`): after the first P store (sub-step 1 of `pst .bias 0`), the
second (`pst .bias 1`) and the arrival between the store waits (`parr .bias`), eight unpacks of
packed words into the next store's halves (`Gen.pkBA_run`, `pkBB`, `pkBC`), whose condition holds
by the words' kind (the tail's end kinds per path, `pB_words`), the state's other facts carried,
landing on the next store's table (`pBData`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem tailB_nodup (p : Params) (L : Launch) (g : Nat) (v : V) :
    ((tailB p L g v).map Prod.fst).Nodup :=
  nodup_of_nodupB (by unfold tailB; kernel_rfl)

/-- The P part's value of a register of the exponent stretch's terms. -/
theorem valueOfD_pB {d : D} (hd : valuesData p L g d = pBData p L g d.v) {r : Nat}
    (hr : r ∈ (tailB p L g d.v).map Prod.fst) :
    valueOfD p L g d r = lookupD (tailB p L g d.v) r := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  rw [valueOfD_prefix (G := tailB p L g d.v)
      (X := halvesB _ ++ valuesRun p d.v ++ valuesBiasM p d.v) hd (tailB_nodup ..) q hq,
    lookupD_of_mem_nodup (tailB_nodup ..) hq]

/-! ### The stores' unpacks -/

theorem pkBA_facts0_eq (V : Nat → Value) :
    Gen.pkBA_facts0 V = factsFrom ((Gen.pkBA_facts0 V).map Prod.fst) V := by kernel_rfl
theorem pkBB_facts0_eq (V : Nat → Value) :
    Gen.pkBB_facts0 V = factsFrom ((Gen.pkBB_facts0 V).map Prod.fst) V := by kernel_rfl
theorem pkBC_facts0_eq (V : Nat → Value) :
    Gen.pkBC_facts0 V = factsFrom ((Gen.pkBC_facts0 V).map Prod.fst) V := by kernel_rfl

theorem pr_w4 {k : Kd} {v : Value} (h : k.Has v) (hk : isPr k = true) : (Kd.pr .w4).Has v := by
  cases k with
  | pr s => exact ⟨h.1, SK.mono (by cases s <;> rfl) h.2.1, SK.mono (by cases s <;> rfl) h.2.2⟩
  | _ => simp [isPr] at hk

/-- The packed words of a bias round's P part. -/
def wordRegsB : List Nat := List.range' 8571 24

theorem expoBTA1_eq_B : @Gen.expoBTA1_facts4 = @Gen.expoBTB1_facts4 := rfl

/-- The packed words of a bias P state have the pair kind (from the tail's kinds, per path). -/
theorem pB_words (hp : Pre p L m) {d : D} (hd : valuesData p L g d = pBData p L g d.v)
    {rs : List Nat} (hrs : rs.all (wordRegsB.contains ·) = true) :
    ∀ q ∈ rs.map fun r => (r, Kd.pr .w4), q.2.Has (valueOfD p L g d q.1) := by
  intro q hq
  obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
  have hr : r ∈ wordRegsB := List.contains_iff_mem.mp (List.all_eq_true.mp hrs r hr')
  rw [valueOfD_pB hd (by
    have h : wordRegsB.all (((tailB p L g d.v).map Prod.fst).contains ·) = true := by
      unfold tailB; kernel_rfl
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h r hr))]
  unfold tailB vTailB
  cases Epilogue.scmp .lt .u d.v.bt (r301 p L g d.v)
  · have hk : wordRegsB.all (fun r => isPr (kOf tAb4 r)) = true := by decide +kernel
    exact pr_w4 ((tailA_ok (g := g) hp d.v).2.2.2 r) (List.all_eq_true.mp hk r hr)
  · have hk : wordRegsB.all (fun r => isPr (kOf tBb4 r)) = true := by decide +kernel
    rw [expoBTA1_eq_B]
    exact pr_w4 ((tailB_ok d.v (bb8_kinds hp d.v)).2.2.2 r) (List.all_eq_true.mp hk r hr)

theorem halvesB_nodup (E : List (Nat × Value)) : ((halvesB E).map Prod.fst).Nodup :=
  nodup_of_nodupB (by kernel_rfl)

/-- A P1 state's value of a store half: the split of the packed word's term. -/
theorem valueOfD_pBh {d : D} (hd : valuesData p L g d = pBData p L g d.v) {lo hi w : Nat}
    (hm : (lo, hi, w) ∈ unpackSpecB) :
    valueOfD p L g d lo = (splitValue 64 (lookupD (tailB p L g d.v) w)).1 ∧
    valueOfD p L g d hi = (splitValue 64 (lookupD (tailB p L g d.v) w)).2 := by
  have hkeys : unpackSpecB.all (fun q => !((tailB p L g d.v).map Prod.fst).contains q.1 &&
      !((tailB p L g d.v).map Prod.fst).contains q.2.1) = true := by
    unfold tailB; kernel_rfl
  have hq := List.all_eq_true.mp hkeys _ hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
  have hlo : (tailB p L g d.v).lookup lo = none := by
    cases h : (tailB p L g d.v).lookup lo with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hq.1] at this; cases this
  have hhi : (tailB p L g d.v).lookup hi = none := by
    cases h : (tailB p L g d.v).lookup hi with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hq.2] at this; cases this
  have hm1 : (lo, (splitValue 64 (lookupD (tailB p L g d.v) w)).1) ∈
      halvesB (tailB p L g d.v) :=
    List.mem_flatMap.mpr ⟨_, hm, by simp⟩
  have hm2 : (hi, (splitValue 64 (lookupD (tailB p L g d.v) w)).2) ∈
      halvesB (tailB p L g d.v) :=
    List.mem_flatMap.mpr ⟨_, hm, by simp⟩
  have e1 := lookup_prefix (X := []) (halvesB_nodup _) hm1
  have e2 := lookup_prefix (X := []) (halvesB_nodup _) hm2
  simp only [List.append_nil] at e1 e2
  simp only [valueOfD, hd, pBData, List.lookup_append, hlo, hhi, Option.none_or, e1, e2,
    Option.some_or, Option.getD_some, and_self]

/-- The words of an unpack spec are terms of the exponent stretch. -/
theorem valueOfD_pBw {d : D} (hd : valuesData p L g d = pBData p L g d.v) {lo hi w : Nat}
    (hm : (lo, hi, w) ∈ unpackSpecB) : valueOfD p L g d w = lookupD (tailB p L g d.v) w := by
  have hw : unpackSpecB.all (fun q => ((tailB p L g d.v).map Prod.fst).contains q.2.2) = true := by
    unfold tailB; kernel_rfl
  exact valueOfD_pB hd (List.contains_iff_mem.mp (List.all_eq_true.mp hw _ hm))

/-- The end facts of the unpacks, from the values of the halves at the next state. -/
theorem unpack_landB {W W' : Nat → Value} {G : List (Nat × Value)}
    (hG : ∀ q ∈ G, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecB ∧
      ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)))
    (hW : ∀ lo hi w, (lo, hi, w) ∈ unpackSpecB →
      W' lo = (splitValue 64 (W w)).1 ∧ W' hi = (splitValue 64 (W w)).2) :
    ∀ q ∈ G, W' q.1 = q.2 := by
  intro q hq
  obtain ⟨lo, hi, w, hm, (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩ := hG q hq
  · rw [e1, e2]; exact (hW lo hi w hm).1
  · rw [e1, e2]; exact (hW lo hi w hm).2

/-- The halves of the next P1 state from the words of this one. -/
theorem pB_halves {d d' : D} (hd : valuesData p L g d = pBData p L g d.v)
    (hd' : valuesData p L g d' = pBData p L g d'.v) (hv : d'.v = d.v) :
    ∀ lo hi w, (lo, hi, w) ∈ unpackSpecB →
      valueOfD p L g d' lo = (splitValue 64 (valueOfD p L g d w)).1 ∧
      valueOfD p L g d' hi = (splitValue 64 (valueOfD p L g d w)).2 := by
  intro lo hi w hm
  have h := valueOfD_pBh hd' hm
  rw [valueOfD_pBw hd hm, ← hv]
  exact h

theorem pkBA_G (V : Nat → Value) : factsFrom ((Gen.pkBA_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkBA_facts0 V)) Gen.pkBA_items0) = Gen.pkBA_facts1 V := by kernel_rfl
theorem pkBB_G (V : Nat → Value) : factsFrom ((Gen.pkBB_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkBB_facts0 V)) Gen.pkBB_items0) = Gen.pkBB_facts1 V := by kernel_rfl
theorem pkBC_G (V : Nat → Value) : factsFrom ((Gen.pkBC_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkBC_facts0 V)) Gen.pkBC_items0) = Gen.pkBC_facts1 V := by kernel_rfl

/-- Membership in a literal list, assigning the element's unknown parts. -/
macro "mem_lit" : tactic => `(tactic|
  repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-- The end facts of the three unpack runs have the spec's form. -/
theorem pkBA_spec (W : Nat → Value) :
    ∀ q ∈ Gen.pkBA_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecB ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkBA_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpecB; mem_lit, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpecB; mem_lit, .inr ⟨rfl, rfl⟩⟩
theorem pkBB_spec (W : Nat → Value) :
    ∀ q ∈ Gen.pkBB_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecB ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkBB_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpecB; mem_lit, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpecB; mem_lit, .inr ⟨rfl, rfl⟩⟩
theorem pkBC_spec (W : Nat → Value) :
    ∀ q ∈ Gen.pkBC_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecB ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkBC_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpecB; mem_lit, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpecB; mem_lit, .inr ⟨rfl, rfl⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
