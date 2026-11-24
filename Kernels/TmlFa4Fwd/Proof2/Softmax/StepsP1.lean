-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsP1Control

@[expose] public section

/-! # The first P publication's unpack segments

The segments land on probability stores with their unpacked register values. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The stores' unpacks -/

theorem pkA_facts0_eq (V : Nat → Value) :
    Gen.pkA_facts0 V = factsFrom ((Gen.pkA_facts0 V).map Prod.fst) V := by kernel_rfl
theorem pkB_facts0_eq (V : Nat → Value) :
    Gen.pkB_facts0 V = factsFrom ((Gen.pkB_facts0 V).map Prod.fst) V := by kernel_rfl
theorem pkC_facts0_eq (V : Nat → Value) :
    Gen.pkC_facts0 V = factsFrom ((Gen.pkC_facts0 V).map Prod.fst) V := by kernel_rfl

/-- The packed words of a P1 state have the pair kind (from the exponent stretch's kinds). -/
theorem p1_words (hp : Pre p L m) {d : D} (hd : valuesData p L g d = p1Data p L g d.v)
    {rs : List Nat} (hrs : rs.all (wordRegs1.contains ·) = true) :
    ∀ q ∈ rs.map fun r => (r, Kd.pr .w4), q.2.Has (valueOfD p L g d q.1) := by
  intro q hq
  obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
  have hr : r ∈ wordRegs1 := List.contains_iff_mem.mp (List.all_eq_true.mp hrs r hr')
  rw [valueOfD_p1 hd (by
    have h : wordRegs1.all (((expoE p L g d.v).map Prod.fst).contains ·) = true := by
      unfold expoE; kernel_rfl
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h r hr))]
  exact (expo1_ok (g := g) hp d.v).2.1 r hr

theorem halvesP1_nodup (E : List (Nat × Value)) : ((halvesP1 E).map Prod.fst).Nodup :=
  nodup_of_nodupB (by kernel_rfl)

/-- A P1 state's value of a store half: the split of the packed word's term. -/
theorem valueOfD_p1h {d : D} (hd : valuesData p L g d = p1Data p L g d.v) {lo hi w : Nat}
    (hm : (lo, hi, w) ∈ unpackSpec1) :
    valueOfD p L g d lo = (splitValue 64 (lookupD (expoE p L g d.v) w)).1 ∧
    valueOfD p L g d hi = (splitValue 64 (lookupD (expoE p L g d.v) w)).2 := by
  have hkeys : unpackSpec1.all (fun q => !((expoE p L g d.v).map Prod.fst).contains q.1 &&
      !((expoE p L g d.v).map Prod.fst).contains q.2.1) = true := by
    unfold expoE; kernel_rfl
  have hq := List.all_eq_true.mp hkeys _ hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
  have hlo : (expoE p L g d.v).lookup lo = none := by
    cases h : (expoE p L g d.v).lookup lo with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hq.1] at this; cases this
  have hhi : (expoE p L g d.v).lookup hi = none := by
    cases h : (expoE p L g d.v).lookup hi with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hq.2] at this; cases this
  have hm1 : (lo, (splitValue 64 (lookupD (expoE p L g d.v) w)).1) ∈
      halvesP1 (expoE p L g d.v) :=
    List.mem_flatMap.mpr ⟨_, hm, by simp⟩
  have hm2 : (hi, (splitValue 64 (lookupD (expoE p L g d.v) w)).2) ∈
      halvesP1 (expoE p L g d.v) :=
    List.mem_flatMap.mpr ⟨_, hm, by simp⟩
  have e1 := lookup_prefix (X := []) (halvesP1_nodup _) hm1
  have e2 := lookup_prefix (X := []) (halvesP1_nodup _) hm2
  simp only [List.append_nil] at e1 e2
  simp only [valueOfD, hd, p1Data, List.lookup_append, hlo, hhi, Option.none_or, e1, e2,
    Option.getD_some, and_self]

/-- The words of an unpack spec are terms of the exponent stretch. -/
theorem valueOfD_p1w {d : D} (hd : valuesData p L g d = p1Data p L g d.v) {lo hi w : Nat}
    (hm : (lo, hi, w) ∈ unpackSpec1) : valueOfD p L g d w = lookupD (expoE p L g d.v) w := by
  have hw : unpackSpec1.all (fun q => ((expoE p L g d.v).map Prod.fst).contains q.2.2) = true := by
    unfold expoE; kernel_rfl
  exact valueOfD_p1 hd (List.contains_iff_mem.mp (List.all_eq_true.mp hw _ hm))

/-- The end facts of the unpacks, from the values of the halves at the next state. -/
theorem unpack_land {W W' : Nat → Value} {G : List (Nat × Value)}
    (hG : ∀ q ∈ G, ∃ lo hi w, (lo, hi, w) ∈ unpackSpec1 ∧
      ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)))
    (hW : ∀ lo hi w, (lo, hi, w) ∈ unpackSpec1 →
      W' lo = (splitValue 64 (W w)).1 ∧ W' hi = (splitValue 64 (W w)).2) :
    ∀ q ∈ G, W' q.1 = q.2 := by
  intro q hq
  obtain ⟨lo, hi, w, hm, (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩ := hG q hq
  · rw [e1, e2]; exact (hW lo hi w hm).1
  · rw [e1, e2]; exact (hW lo hi w hm).2

/-- The halves of the next P1 state from the words of this one. -/
theorem p1_halves {d d' : D} (hd : valuesData p L g d = p1Data p L g d.v)
    (hd' : valuesData p L g d' = p1Data p L g d'.v) (hv : d'.v = d.v) :
    ∀ lo hi w, (lo, hi, w) ∈ unpackSpec1 →
      valueOfD p L g d' lo = (splitValue 64 (valueOfD p L g d w)).1 ∧
      valueOfD p L g d' hi = (splitValue 64 (valueOfD p L g d w)).2 := by
  intro lo hi w hm
  have h := valueOfD_p1h hd' hm
  rw [valueOfD_p1w hd hm, ← hv]
  exact h

theorem pkA_G (V : Nat → Value) : factsFrom ((Gen.pkA_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkA_facts0 V)) Gen.pkA_items0) = Gen.pkA_facts1 V := by kernel_rfl
theorem pkB_G (V : Nat → Value) : factsFrom ((Gen.pkB_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkB_facts0 V)) Gen.pkB_items0) = Gen.pkB_facts1 V := by kernel_rfl
theorem pkC_G (V : Nat → Value) : factsFrom ((Gen.pkC_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkC_facts0 V)) Gen.pkC_items0) = Gen.pkC_facts1 V := by kernel_rfl

/-- Membership in a literal list, assigning the element's unknown parts. -/
macro "mem_lit" : tactic => `(tactic|
  repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-- The end facts of the three unpack runs have the spec's form. -/
theorem pkA_spec (W : Nat → Value) : ∀ q ∈ Gen.pkA_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpec1 ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkA_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpec1; mem_lit, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpec1; mem_lit, .inr ⟨rfl, rfl⟩⟩
theorem pkB_spec (W : Nat → Value) : ∀ q ∈ Gen.pkB_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpec1 ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkB_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpec1; mem_lit, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpec1; mem_lit, .inr ⟨rfl, rfl⟩⟩
theorem pkC_spec (W : Nat → Value) : ∀ q ∈ Gen.pkC_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpec1 ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkC_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpec1; mem_lit, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpec1; mem_lit, .inr ⟨rfl, rfl⟩⟩

set_option hygiene false in
/-- An unpack run from state `d` between two states of the first round's P part, landing on the
second (`d'`). -/
macro "p1_unpack " d:term:max d':term:max run:ident eq:ident f0:ident items:ident
    hG:ident sp:ident : tactic =>
  `(tactic| (
  have hrun := $run L g (valueOfD p L g $d)
  have hfr := SegD.frame (H := factsD p L g $d) Gen.rulesFrame hrun rfl (by kernel_rfl)
    (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start ?_ |>.weaken_end ?_) ?_
  · intro R hR
    refine (holds_append _ _ _).mpr ⟨?_, hR⟩
    rw [$eq:ident]
    exact holds_sub hR (by kernel_rfl)
  · intro R hR
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    exact land_run (unpack_land ($sp _) (p1_halves (d := $d) (d' := $d') rfl rfl rfl))
      (fun r _ => rfl) (by kernel_rfl) h1 h2
  · have hV : ∀ r, (kOf ((($f0 (valueOfD p L g $d)).map Prod.fst).map fun r => (r, Kd.pr .w4))
        r).Has (lookupD ($f0 (valueOfD p L g $d)) r) := by
      rw [$eq:ident]
      exact kstart (by kernel_rfl) (p1_words hp rfl (by kernel_rfl))
    exact (kpiece ($hG _) (by kernel_rfl) hV (by simp [kFns, XItem.FnOk, $items:ident])).1))

/-- **The first P store** after its implicit wait, and the unpacks of the second store's halves. -/
theorem stepAt_pst1_0s (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pst .first 0, v, 1, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_tcStStore (dn := D.mk' (.pst .first 1) v) (by code_lookup)
    (by rw [Assumptions.all_tcStWaitLd]; kernel_rfl) rfl rfl (fun _ => rfl)
    ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  p1_unpack (⟨.pst .first 0, v, 1, []⟩ : D) (D.mk' (.pst .first 1) v) Gen.pkA_run pkA_facts0_eq
    Gen.pkA_facts0 Gen.pkA_items0 pkA_G pkA_spec

/-- **The second P store** and the unpacks of the third store's halves. -/
theorem stepAt_pst1_1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pst .first 1, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issueAt (dn := D.mk' (.pst .first 2) v) (by code_lookup)
    (fun hpc hf => fires_tcSt_next (by rw [hpc, Assumptions.all_tcStWaitLd]; rfl) hf)
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  p1_unpack (⟨.pst .first 1, v, 0, []⟩ : D) (D.mk' (.pst .first 2) v) Gen.pkB_run pkB_facts0_eq
    Gen.pkB_facts0 Gen.pkB_items0 pkB_G pkB_spec

/-- **The arrival between the store waits** and the unpacks of the fourth store's halves. -/
theorem stepAt_parr1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.parr .first, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_arrive (dn := D.mk' (.pst .first 3) v) (by code_lookup) ?_
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro r hr q hq e
    cases hr
    have hk : (liveD (livePc ⟨.parr .first, v, 0, []⟩)).contains 8186 = false := by kernel_rfl
    simp only [factsD, factsFrom, List.mem_map] at hq
    obtain ⟨r', hr', rfl⟩ := hq
    simp only at e
    subst e
    rw [List.contains_iff_mem.mpr hr'] at hk
    cases hk
  · p1_unpack (⟨.parr .first, v, 0, []⟩ : D) (D.mk' (.pst .first 3) v) Gen.pkC_run pkC_facts0_eq
      Gen.pkC_facts0 Gen.pkC_items0 pkC_G pkC_spec

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
