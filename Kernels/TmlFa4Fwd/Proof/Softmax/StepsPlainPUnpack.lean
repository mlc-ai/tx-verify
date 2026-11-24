-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.PkP
public import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE3
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1Control
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1b
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # Unpacking the plain round's probability stores

The generated unpack segments use the kinds of the packed words. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The halves the plain store unpacks write, as splits of the packed words' terms. -/
abbrev halvesPP (E : List (Nat × Value)) : List (Nat × Value) :=
  unpackSpecP.flatMap fun (lo, hi, w) =>
    [(lo, (splitValue 64 (lookupD E w)).1), (hi, (splitValue 64 (lookupD E w)).2)]

theorem pPData_eq (p : Params) (v : V) : pPData p v = expoPE p v ++ halvesPP (expoPE p v) := rfl

/-- The packed words of the plain P part. -/
def wordRegsP : List Nat := List.range' 8798 8 ++ List.range' 8834 16

theorem expoPE_nodup (p : Params) (v : V) : ((expoPE p v).map Prod.fst).Nodup :=
  nodup_of_nodupB (by unfold expoPE; kernel_rfl)

theorem pP_wordK (hp : Pre p L m) (v : V) :
    ∀ r ∈ wordRegsP, (Kd.pr .w4).Has (lookupD (expoPE p v) r) := by
  intro r hr
  have hk : wordRegsP.all (fun r => decide (kOf r4L3 r = .pr .w4)) = true := by kernel_rfl
  have := List.all_eq_true.mp hk r hr
  simp only [decide_eq_true_eq] at this
  have h := (expoP4_ok hp v).2 r
  rw [this] at h
  exact h

theorem valueOfD_pP {d : D} (hd : valuesData p L g d = pPData p d.v) {r : Nat}
    (hr : r ∈ (expoPE p d.v).map Prod.fst) :
    valueOfD p L g d r = lookupD (expoPE p d.v) r := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  rw [valueOfD_prefix (G := expoPE p d.v) (X := halvesPP _) (hd.trans (pPData_eq p d.v))
      (expoPE_nodup ..) q hq,
    lookupD_of_mem_nodup (expoPE_nodup ..) hq]

theorem pkPA_facts0_eq (V : Nat → Value) :
    Gen.pkPA_facts0 V = factsFrom ((Gen.pkPA_facts0 V).map Prod.fst) V := by kernel_rfl
theorem pkPB_facts0_eq (V : Nat → Value) :
    Gen.pkPB_facts0 V = factsFrom ((Gen.pkPB_facts0 V).map Prod.fst) V := by kernel_rfl
theorem pkPC_facts0_eq (V : Nat → Value) :
    Gen.pkPC_facts0 V = factsFrom ((Gen.pkPC_facts0 V).map Prod.fst) V := by kernel_rfl

/-- The packed words of a P1 state have the pair kind (from the exponent stretch's kinds). -/
theorem pP_words (hp : Pre p L m) {d : D} (hd : valuesData p L g d = pPData p d.v)
    {rs : List Nat} (hrs : rs.all (wordRegsP.contains ·) = true) :
    ∀ q ∈ rs.map fun r => (r, Kd.pr .w4), q.2.Has (valueOfD p L g d q.1) := by
  intro q hq
  obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
  have hr : r ∈ wordRegsP := List.contains_iff_mem.mp (List.all_eq_true.mp hrs r hr')
  rw [valueOfD_pP hd (by
    have h : wordRegsP.all (((expoPE p d.v).map Prod.fst).contains ·) = true := by
      unfold expoPE; kernel_rfl
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h r hr))]
  exact pP_wordK hp d.v r hr

theorem halvesPP_nodup (E : List (Nat × Value)) : ((halvesPP E).map Prod.fst).Nodup :=
  nodup_of_nodupB (by kernel_rfl)

/-- A P1 state's value of a store half: the split of the packed word's term. -/
theorem valueOfD_pPh {d : D} (hd : valuesData p L g d = pPData p d.v) {lo hi w : Nat}
    (hm : (lo, hi, w) ∈ unpackSpecP) :
    valueOfD p L g d lo = (splitValue 64 (lookupD (expoPE p d.v) w)).1 ∧
    valueOfD p L g d hi = (splitValue 64 (lookupD (expoPE p d.v) w)).2 := by
  have hkeys : unpackSpecP.all (fun q => !((expoPE p d.v).map Prod.fst).contains q.1 &&
      !((expoPE p d.v).map Prod.fst).contains q.2.1) = true := by
    unfold expoPE; kernel_rfl
  have hq := List.all_eq_true.mp hkeys _ hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
  have hlo : (expoPE p d.v).lookup lo = none := by
    cases h : (expoPE p d.v).lookup lo with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hq.1] at this; cases this
  have hhi : (expoPE p d.v).lookup hi = none := by
    cases h : (expoPE p d.v).lookup hi with
    | none => rfl
    | some x =>
      have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h))
      rw [hq.2] at this; cases this
  have hm1 : (lo, (splitValue 64 (lookupD (expoPE p d.v) w)).1) ∈
      halvesPP (expoPE p d.v) :=
    List.mem_flatMap.mpr ⟨_, hm, by simp⟩
  have hm2 : (hi, (splitValue 64 (lookupD (expoPE p d.v) w)).2) ∈
      halvesPP (expoPE p d.v) :=
    List.mem_flatMap.mpr ⟨_, hm, by simp⟩
  have e1 := lookup_prefix (X := []) (halvesPP_nodup _) hm1
  have e2 := lookup_prefix (X := []) (halvesPP_nodup _) hm2
  simp only [List.append_nil] at e1 e2
  simp only [valueOfD, hd, pPData_eq, List.lookup_append, hlo, hhi, Option.none_or, e1, e2,
    Option.getD_some, and_self]

/-- The words of an unpack spec are terms of the exponent stretch. -/
theorem valueOfD_pPw {d : D} (hd : valuesData p L g d = pPData p d.v) {lo hi w : Nat}
    (hm : (lo, hi, w) ∈ unpackSpecP) : valueOfD p L g d w = lookupD (expoPE p d.v) w := by
  have hw : unpackSpecP.all (fun q => ((expoPE p d.v).map Prod.fst).contains q.2.2) = true := by
    unfold expoPE; kernel_rfl
  exact valueOfD_pP hd (List.contains_iff_mem.mp (List.all_eq_true.mp hw _ hm))

/-- The end facts of the unpacks, from the values of the halves at the next state. -/
theorem unpack_landP {W W' : Nat → Value} {G : List (Nat × Value)}
    (hG : ∀ q ∈ G, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecP ∧
      ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)))
    (hW : ∀ lo hi w, (lo, hi, w) ∈ unpackSpecP →
      W' lo = (splitValue 64 (W w)).1 ∧ W' hi = (splitValue 64 (W w)).2) :
    ∀ q ∈ G, W' q.1 = q.2 := by
  intro q hq
  obtain ⟨lo, hi, w, hm, (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩ := hG q hq
  · rw [e1, e2]; exact (hW lo hi w hm).1
  · rw [e1, e2]; exact (hW lo hi w hm).2

/-- The halves of the next P1 state from the words of this one. -/
theorem pP_halves {d d' : D} (hd : valuesData p L g d = pPData p d.v)
    (hd' : valuesData p L g d' = pPData p d'.v) (hv : d'.v = d.v) :
    ∀ lo hi w, (lo, hi, w) ∈ unpackSpecP →
      valueOfD p L g d' lo = (splitValue 64 (valueOfD p L g d w)).1 ∧
      valueOfD p L g d' hi = (splitValue 64 (valueOfD p L g d w)).2 := by
  intro lo hi w hm
  have h := valueOfD_pPh hd' hm
  rw [valueOfD_pPw hd hm, ← hv]
  exact h

theorem pkPA_G (V : Nat → Value) : factsFrom ((Gen.pkPA_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkPA_facts0 V)) Gen.pkPA_items0) = Gen.pkPA_facts1 V := by kernel_rfl
theorem pkPB_G (V : Nat → Value) : factsFrom ((Gen.pkPB_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkPB_facts0 V)) Gen.pkPB_items0) = Gen.pkPB_facts1 V := by kernel_rfl
theorem pkPC_G (V : Nat → Value) : factsFrom ((Gen.pkPC_facts1 V).map Prod.fst)
    (xFinal (lookupD (Gen.pkPC_facts0 V)) Gen.pkPC_items0) = Gen.pkPC_facts1 V := by kernel_rfl

/-- Membership in a literal list, assigning the element's unknown parts. -/
macro "mem_litP" : tactic => `(tactic|
  repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-- The end facts of the three unpack runs have the spec's form. -/
theorem pkPA_spec (W : Nat → Value) :
    ∀ q ∈ Gen.pkPA_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecP ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkPA_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpecP; mem_litP, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpecP; mem_litP, .inr ⟨rfl, rfl⟩⟩
theorem pkPB_spec (W : Nat → Value) :
    ∀ q ∈ Gen.pkPB_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecP ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkPB_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpecP; mem_litP, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpecP; mem_litP, .inr ⟨rfl, rfl⟩⟩
theorem pkPC_spec (W : Nat → Value) :
    ∀ q ∈ Gen.pkPC_facts1 W, ∃ lo hi w, (lo, hi, w) ∈ unpackSpecP ∧
    ((q.1 = lo ∧ q.2 = (splitValue 64 (W w)).1) ∨ (q.1 = hi ∧ q.2 = (splitValue 64 (W w)).2)) := by
  intro q hq
  simp only [Gen.pkPC_facts1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
    | exact ⟨_, _, _, by unfold unpackSpecP; mem_litP, .inl ⟨rfl, rfl⟩⟩
    | exact ⟨_, _, _, by unfold unpackSpecP; mem_litP, .inr ⟨rfl, rfl⟩⟩

set_option hygiene false in
/-- An unpack run from state `d` between two states of a plain round's P part, landing on the
second (`d'`). -/
macro "pP_unpack " d:term:max d':term:max run:ident eq:ident f0:ident items:ident
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
    exact land_run (unpack_landP ($sp _) (pP_halves (d := $d) (d' := $d') rfl rfl rfl))
      (fun r _ => rfl) (by kernel_rfl) h1 h2
  · have hV : ∀ r, (kOf ((($f0 (valueOfD p L g $d)).map Prod.fst).map fun r => (r, Kd.pr .w4))
        r).Has (lookupD ($f0 (valueOfD p L g $d)) r) := by
      rw [$eq:ident]
      exact kstart (by kernel_rfl) (pP_words hp rfl (by kernel_rfl))
    exact (kpiece ($hG _) (by kernel_rfl) hV (by simp [kFns, XItem.FnOk, $items:ident])).1))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
