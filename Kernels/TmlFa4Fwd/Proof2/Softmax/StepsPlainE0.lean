-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsNarr1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Gen.ExpoP

@[expose] public section

/-! # A plain round's exponent stretch: the start values and the first run

The values the plain round's exponent stretch reads at pc 6892 are `vExpoP` (`Machine.lean`);
on the first generated run's keys they are the arrival state's (`expoP_start`). The first run's
condition holds by the kinds of those values (`expoP0_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The registers the first run reads. -/
def expoP0Keys : List Nat := (Gen.expoP0_facts0 fun _ => .pred false).map Prod.fst

/-- **The start values are the arrival state's** on the first run's keys. -/
theorem expoP_start (v : V) : factsFrom expoP0Keys (vExpoP p v) =
    factsFrom expoP0Keys (valueOfD p L g ⟨.narr .plain, v, 0, []⟩) := by
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf <;> kernel_rfl

theorem expoP0_facts0_eq (V : Nat → Value) :
    Gen.expoP0_facts0 V = factsFrom ((Gen.expoP0_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The kinds of the first run's start values. -/
def expoP0K : List (Nat × Kd) :=
  [(1230, .s .fl), (5514, .s .fl), (8692, .pr .pw)] ++
    ((List.range' 8687 4 ++ List.range' 7431 60).map fun r => (r, .pr .fl))

theorem maxP_fl (p : Params) (v : V) : SK.fl.Has (maxP p v) := by
  unfold maxP
  split
  · split <;> exact has_float_fl _
  · exact has_float_fl _

theorem scaleW_pw (hp : Pre p L m) :
    (Kd.pr .pw).Has (joinValue (.bits 32 (Epilogue.paramW p.scaleLog2Bits))
      (.bits 32 (Epilogue.paramW p.scaleLog2Bits))) := by
  obtain ⟨s, hS, hs0, h32⟩ := scale_word hp
  have h := paramW_pw hS hs0 h32
  exact join_has h h

theorem expoP0K_has (hp : Pre p L m) (v : V) : ∀ q ∈ expoP0K, q.2.Has (vExpoP p v q.1) := by
  intro q hq
  simp only [expoP0K, List.mem_append, List.mem_cons, List.mem_map, List.mem_range',
    List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl) | ⟨r, (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩), rfl⟩
  · show SK.fl.Has (vExpoP p v 1230)
    simp only [vExpoP, ↓reduceIte, negS]
    exact has_float_fl _
  · show SK.fl.Has (vExpoP p v 5514)
    simp only [vExpoP, show (5514 : Nat) ≠ 1230 by decide, ↓reduceIte, true_or]
    exact maxP_fl p v
  · show (Kd.pr .pw).Has (vExpoP p v 8692)
    simp only [vExpoP, show (8692 : Nat) ≠ 1230 by decide, show (8692 : Nat) ≠ 5514 by decide,
      show (8692 : Nat) ≠ 7256 by decide, show (8692 : Nat) ≠ 1492 by decide,
      show (8692 : Nat) ≠ 7257 by decide, ↓reduceIte, or_self]
    exact scaleW_pw hp
  all_goals
    show (Kd.pr .fl).Has (vExpoP p v _)
    unfold vExpoP
    split_ifs <;> first | omega | exact pair_has (has_float_fl _) (has_float_fl _)

/-- The first run's items read no role function but the packs. -/
macro "fns_okexpoP0" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expoP0_items0, Gen.expoP0_items1, Gen.expoP0_items2,
    Gen.expoP0_items3, Gen.expoP0_items4, Gen.expoP0_items5, Gen.expoP0_items6, and_true,
    true_and]
  repeat' first | exact Gen.packE_spec | exact Gen.widenE_spec | constructor))

/-- The kinds after each piece of the first run. -/
@[irreducible] def qL1 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf expoP0K) Gen.expoP0_items0)
@[irreducible] def qL2 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf qL1) Gen.expoP0_items1)
@[irreducible] def qL3 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf qL2) Gen.expoP0_items2)
@[irreducible] def qL4 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf qL3) Gen.expoP0_items3)
@[irreducible] def qL5 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf qL4) Gen.expoP0_items4)
@[irreducible] def qL6 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts6 fun _ => .pred false).map Prod.fst)
    (kOut (kOf qL5) Gen.expoP0_items5)
@[irreducible] def qL7 : List (Nat × Kd) :=
  kList ((Gen.expoP0_facts7 fun _ => .pred false).map Prod.fst)
    (kOut (kOf qL6) Gen.expoP0_items6)

theorem expoP0_kok (V : Nat → Value) :
    (kOk (kOf expoP0K) Gen.expoP0_items0 &&
      kNext expoP0K Gen.expoP0_items0 ((Gen.expoP0_facts1 V).map Prod.fst) qL1 &&
      kOk (kOf qL1) Gen.expoP0_items1 &&
      kNext qL1 Gen.expoP0_items1 ((Gen.expoP0_facts2 V).map Prod.fst) qL2 &&
      kOk (kOf qL2) Gen.expoP0_items2 &&
      kNext qL2 Gen.expoP0_items2 ((Gen.expoP0_facts3 V).map Prod.fst) qL3 &&
      kOk (kOf qL3) Gen.expoP0_items3 &&
      kNext qL3 Gen.expoP0_items3 ((Gen.expoP0_facts4 V).map Prod.fst) qL4 &&
      kOk (kOf qL4) Gen.expoP0_items4 &&
      kNext qL4 Gen.expoP0_items4 ((Gen.expoP0_facts5 V).map Prod.fst) qL5 &&
      kOk (kOf qL5) Gen.expoP0_items5 &&
      kNext qL5 Gen.expoP0_items5 ((Gen.expoP0_facts6 V).map Prod.fst) qL6 &&
      kOk (kOf qL6) Gen.expoP0_items6 &&
      kNext qL6 Gen.expoP0_items6 ((Gen.expoP0_facts7 V).map Prod.fst) qL7) = true := by
  unfold expoP0K
  kernel_rfl

theorem expoP0_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf expoP0K r).Has (lookupD (Gen.expoP0_facts0 V1) r)) :
    Gen.expoP0_cond V1 ∧ ∀ r, (kOf qL7 r).Has (lookupD (Gen.expoP0_facts7 V1) r) := by
  have h14 := expoP0_kok V1
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
  have hG0 : factsFrom ((Gen.expoP0_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts0 V1)) Gen.expoP0_items0) = Gen.expoP0_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.expoP0_items0 := by fns_okexpoP0
  obtain ⟨c0, k1⟩ := kpiece_lit (L := expoP0K) (L' := qL1) (G := Gen.expoP0_facts1 V1)
    (items := Gen.expoP0_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.expoP0_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts1 V1)) Gen.expoP0_items1) = Gen.expoP0_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.expoP0_items1 := by fns_okexpoP0
  obtain ⟨c1, k2⟩ := kpiece_lit (L := qL1) (L' := qL2) (G := Gen.expoP0_facts2 V1)
    (items := Gen.expoP0_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.expoP0_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts2 V1)) Gen.expoP0_items2) = Gen.expoP0_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.expoP0_items2 := by fns_okexpoP0
  obtain ⟨c2, k3⟩ := kpiece_lit (L := qL2) (L' := qL3) (G := Gen.expoP0_facts3 V1)
    (items := Gen.expoP0_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.expoP0_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts3 V1)) Gen.expoP0_items3) = Gen.expoP0_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.expoP0_items3 := by fns_okexpoP0
  obtain ⟨c3, k4⟩ := kpiece_lit (L := qL3) (L' := qL4) (G := Gen.expoP0_facts4 V1)
    (items := Gen.expoP0_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.expoP0_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts4 V1)) Gen.expoP0_items4) = Gen.expoP0_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.expoP0_items4 := by fns_okexpoP0
  obtain ⟨c4, k5⟩ := kpiece_lit (L := qL4) (L' := qL5) (G := Gen.expoP0_facts5 V1)
    (items := Gen.expoP0_items4) hG4 hk4 k4 hf4 hn5
  have hG5 : factsFrom ((Gen.expoP0_facts6 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts5 V1)) Gen.expoP0_items5) = Gen.expoP0_facts6 V1 := by
    kernel_rfl
  have hf5 : kFns Gen.expoP0_items5 := by fns_okexpoP0
  obtain ⟨c5, k6⟩ := kpiece_lit (L := qL5) (L' := qL6) (G := Gen.expoP0_facts6 V1)
    (items := Gen.expoP0_items5) hG5 hk5 k5 hf5 hn6
  have hG6 : factsFrom ((Gen.expoP0_facts7 V1).map Prod.fst)
      (xFinal (lookupD (Gen.expoP0_facts6 V1)) Gen.expoP0_items6) = Gen.expoP0_facts7 V1 := by
    kernel_rfl
  have hf6 : kFns Gen.expoP0_items6 := by fns_okexpoP0
  obtain ⟨c6, k7⟩ := kpiece_lit (L := qL6) (L' := qL7) (G := Gen.expoP0_facts7 V1)
    (items := Gen.expoP0_items6) hG6 hk6 k6 hf6 hn7
  exact ⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, k7⟩

theorem expoP0_ok (hp : Pre p L m) (v : V) : Gen.expoP0_cond (vExpoP p v) ∧
    ∀ r, (kOf qL7 r).Has (lookupD (Gen.expoP0_facts7 (vExpoP p v)) r) := by
  have k0 : ∀ r, (kOf expoP0K r).Has (lookupD (Gen.expoP0_facts0 (vExpoP p v)) r) := by
    rw [expoP0_facts0_eq]
    exact kstart (by kernel_rfl) (expoP0K_has hp v)
  exact expoP0_chain _ k0

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
