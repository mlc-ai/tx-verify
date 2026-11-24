-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Checks
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The first round's exponent stretch

Compose the generated run from pc 4399 to the first P store and check its outputs. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The packed words, the probabilities and the first store's halves at the first P store. -/
def wordRegs1 : List Nat := List.range' 8162 24
def probRegs1 : List Nat := List.range' 1231 128
def halfRegs1 : List Nat := List.range' 3879 16

theorem kind_of_eval {K : Nat → Kd} {V : Nat → Value} (hk : ∀ r, (K r).Has (V r)) {k : Kd}
    {l : List Nat} (he : l.all (fun r => decide (K r = k)) = true) : ∀ r ∈ l, k.Has (V r) := by
  intro r hr
  have := List.all_eq_true.mp he r hr
  simp only [decide_eq_true_eq] at this
  rw [← this]; exact hk r

/-- **The exponent stretch's pieces**: their conditions, and the kinds of the end values, from the
kinds of the start values. -/
theorem expo1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expo1K r).Has (lookupD (Gen.expo1_facts0 V1) r)) :
    Gen.expo1_cond V1 ∧ ∀ r, (kOf eL14 r).Has (lookupD (Gen.expo1_facts14 V1) r) := by
  have h28 := expo1_kok V1
  have hn14 := (band_split h28).2
  have h27 := (band_split h28).1
  have hk13 := (band_split h27).2
  have h26 := (band_split h27).1
  have hn13 := (band_split h26).2
  have h25 := (band_split h26).1
  have hk12 := (band_split h25).2
  have h24 := (band_split h25).1
  have hn12 := (band_split h24).2
  have h23 := (band_split h24).1
  have hk11 := (band_split h23).2
  have h22 := (band_split h23).1
  have hn11 := (band_split h22).2
  have h21 := (band_split h22).1
  have hk10 := (band_split h21).2
  have h20 := (band_split h21).1
  have hn10 := (band_split h20).2
  have h19 := (band_split h20).1
  have hk9 := (band_split h19).2
  have h18 := (band_split h19).1
  have hn9 := (band_split h18).2
  have h17 := (band_split h18).1
  have hk8 := (band_split h17).2
  have h16 := (band_split h17).1
  have hn8 := (band_split h16).2
  have h15 := (band_split h16).1
  have hk7 := (band_split h15).2
  have h14 := (band_split h15).1
  have hn7 := (band_split h14).2
  have h13 := (band_split h14).1
  have hk6 := (band_split h13).2
  have h12 := (band_split h13).1
  have hn6 := (band_split h12).2
  have h11 := (band_split h12).1
  have hk5 := (band_split h11).2
  have h10 := (band_split h11).1
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
  have hG0 : factsFrom ((Gen.expo1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts0 V1)) Gen.expo1_items0) = Gen.expo1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expo1_items0 := by fns_ok
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expo1K) (L' := eL1) (G := Gen.expo1_facts1 V1)
    (items := Gen.expo1_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expo1_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts1 V1)) Gen.expo1_items1) = Gen.expo1_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expo1_items1 := by fns_ok
  obtain ⟨c1, k2⟩ := kpiece_lit (L := eL1) (L' := eL2) (G := Gen.expo1_facts2 V1)
    (items := Gen.expo1_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expo1_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts2 V1)) Gen.expo1_items2) = Gen.expo1_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expo1_items2 := by fns_ok
  obtain ⟨c2, k3⟩ := kpiece_lit (L := eL2) (L' := eL3) (G := Gen.expo1_facts3 V1)
    (items := Gen.expo1_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.expo1_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts3 V1)) Gen.expo1_items3) = Gen.expo1_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.expo1_items3 := by fns_ok
  obtain ⟨c3, k4⟩ := kpiece_lit (L := eL3) (L' := eL4) (G := Gen.expo1_facts4 V1)
    (items := Gen.expo1_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.expo1_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts4 V1)) Gen.expo1_items4) = Gen.expo1_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.expo1_items4 := by fns_ok
  obtain ⟨c4, k5⟩ := kpiece_lit (L := eL4) (L' := eL5) (G := Gen.expo1_facts5 V1)
    (items := Gen.expo1_items4) hG4 hk4 k4 hf4 hn5
  have hG5 : factsFrom ((Gen.expo1_facts6 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts5 V1)) Gen.expo1_items5) = Gen.expo1_facts6 V1 := by
    kernel_rfl
  have hf5 : kFns Gen.expo1_items5 := by fns_ok
  obtain ⟨c5, k6⟩ := kpiece_lit (L := eL5) (L' := eL6) (G := Gen.expo1_facts6 V1)
    (items := Gen.expo1_items5) hG5 hk5 k5 hf5 hn6
  have hG6 : factsFrom ((Gen.expo1_facts7 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts6 V1)) Gen.expo1_items6) = Gen.expo1_facts7 V1 := by
    kernel_rfl
  have hf6 : kFns Gen.expo1_items6 := by fns_ok
  obtain ⟨c6, k7⟩ := kpiece_lit (L := eL6) (L' := eL7) (G := Gen.expo1_facts7 V1)
    (items := Gen.expo1_items6) hG6 hk6 k6 hf6 hn7
  have hG7 : factsFrom ((Gen.expo1_facts8 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts7 V1)) Gen.expo1_items7) = Gen.expo1_facts8 V1 := by
    kernel_rfl
  have hf7 : kFns Gen.expo1_items7 := by fns_ok
  obtain ⟨c7, k8⟩ := kpiece_lit (L := eL7) (L' := eL8) (G := Gen.expo1_facts8 V1)
    (items := Gen.expo1_items7) hG7 hk7 k7 hf7 hn8
  have hG8 : factsFrom ((Gen.expo1_facts9 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts8 V1)) Gen.expo1_items8) = Gen.expo1_facts9 V1 := by
    kernel_rfl
  have hf8 : kFns Gen.expo1_items8 := by fns_ok
  obtain ⟨c8, k9⟩ := kpiece_lit (L := eL8) (L' := eL9) (G := Gen.expo1_facts9 V1)
    (items := Gen.expo1_items8) hG8 hk8 k8 hf8 hn9
  have hG9 : factsFrom ((Gen.expo1_facts10 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts9 V1)) Gen.expo1_items9) = Gen.expo1_facts10 V1 := by
    kernel_rfl
  have hf9 : kFns Gen.expo1_items9 := by fns_ok
  obtain ⟨c9, k10⟩ := kpiece_lit (L := eL9) (L' := eL10) (G := Gen.expo1_facts10 V1)
    (items := Gen.expo1_items9) hG9 hk9 k9 hf9 hn10
  have hG10 : factsFrom ((Gen.expo1_facts11 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts10 V1)) Gen.expo1_items10) = Gen.expo1_facts11 V1 := by
    kernel_rfl
  have hf10 : kFns Gen.expo1_items10 := by fns_ok
  obtain ⟨c10, k11⟩ := kpiece_lit (L := eL10) (L' := eL11) (G := Gen.expo1_facts11 V1)
    (items := Gen.expo1_items10) hG10 hk10 k10 hf10 hn11
  have hG11 : factsFrom ((Gen.expo1_facts12 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts11 V1)) Gen.expo1_items11) = Gen.expo1_facts12 V1 := by
    kernel_rfl
  have hf11 : kFns Gen.expo1_items11 := by fns_ok
  obtain ⟨c11, k12⟩ := kpiece_lit (L := eL11) (L' := eL12) (G := Gen.expo1_facts12 V1)
    (items := Gen.expo1_items11) hG11 hk11 k11 hf11 hn12
  have hG12 : factsFrom ((Gen.expo1_facts13 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts12 V1)) Gen.expo1_items12) = Gen.expo1_facts13 V1 := by
    kernel_rfl
  have hf12 : kFns Gen.expo1_items12 := by fns_ok
  obtain ⟨c12, k13⟩ := kpiece_lit (L := eL12) (L' := eL13) (G := Gen.expo1_facts13 V1)
    (items := Gen.expo1_items12) hG12 hk12 k12 hf12 hn13
  have hG13 : factsFrom ((Gen.expo1_facts14 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expo1_facts13 V1)) Gen.expo1_items13) = Gen.expo1_facts14 V1 := by
    kernel_rfl
  have hf13 : kFns Gen.expo1_items13 := by fns_ok
  obtain ⟨c13, k14⟩ := kpiece_lit (L := eL13) (L' := eL14) (G := Gen.expo1_facts14 V1)
    (items := Gen.expo1_items13) hG13 hk13 k13 hf13 hn14
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, k14⟩

theorem expo1_kinds_eval :
    (wordRegs1.all (fun r => decide (kOf eL14 r = .pr .w4)) &&
      probRegs1.all (fun r => decide (kOf eL14 r = .s .nn)) &&
      halfRegs1.all (fun r => decide (kOf eL14 r = .s .w4))) = true := by
  kernel_rfl

theorem expo1_ok (hp : Pre p L m) (v : V) : Gen.expo1_cond (vExpo1 p L g v) ∧
    (∀ r ∈ wordRegs1, (Kd.pr .w4).Has (lookupD (expoE p L g v) r)) ∧
    (∀ r ∈ probRegs1, (Kd.s .nn).Has (lookupD (expoE p L g v) r)) ∧
    (∀ r ∈ halfRegs1, (Kd.s .w4).Has (lookupD (expoE p L g v) r)) := by
  have k0 : ∀ r, (kOf expo1K r).Has (lookupD (Gen.expo1_facts0 (vExpo1 p L g v)) r) := by
    rw [expo1_facts0_eq]
    exact kstart (by kernel_rfl) (expo1K_has hp v)
  obtain ⟨hc, hk⟩ := expo1_chain _ k0
  have he := expo1_kinds_eval
  exact ⟨hc, kind_of_eval hk (band_split (band_split he).1).1,
    kind_of_eval hk (band_split (band_split he).1).2, kind_of_eval hk (band_split he).2⟩

/-! ### The step -/

/-- Distinct keys, by evaluation. -/
def nodupB : List Nat → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

theorem nodup_of_nodupB : ∀ {l : List Nat}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nodupB h.2⟩
    have := List.contains_iff_mem.mpr hm
    rw [h.1] at this
    cases this

theorem expoE_nodup (p : Params) (L : Launch) (g : Nat) (v : V) :
    ((expoE p L g v).map Prod.fst).Nodup :=
  nodup_of_nodupB (by unfold expoE; kernel_rfl)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
