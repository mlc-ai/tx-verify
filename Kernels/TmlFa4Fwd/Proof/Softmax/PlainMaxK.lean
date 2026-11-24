-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.MaxP
public import Kernels.TmlFa4Fwd.Proof.Softmax.PlainMaxV
public import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # A plain round's maximum: the run's condition, value and frame

The run `Gen.maxP_run` (pcs 6747 to 6876) from the values of the statistics store's state of a
plain round (`statP`): its condition holds by the kinds of its start values (`maxP_ok`: the
maximum before the round is a real or `-∞`, the 128 scores are reals; the kind checker's
`max.f32` rule), its value is the fold of the state (`maxP_val`), and with the facts of the live
registers at pc 6747 carried it runs from those facts to the facts of the table at the cut
pc 6877 (`maxP_mid`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The statistics store's state of a plain round. -/
abbrev statP (v : V) : D := ⟨.stat true, v, 0, []⟩

theorem valuesData_statP (v : V) : valuesData p L g (statP v) =
    valuesPairs .plain v 64 ++ valuesPlainP p v := rfl

theorem lookup_none_of_keys {G : List (Nat × Value)} {r : Nat}
    (h : (G.map Prod.fst).contains r = false) : G.lookup r = none := by
  induction G with
  | nil => rfl
  | cons a G ih =>
    obtain ⟨k, x⟩ := a
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at h
    simp only [List.lookup, h.1, ih h.2]

theorem pairs_lookup_none (v : V) {r : Nat}
    (h : ((List.range 64).map (pairReg .plain)).contains r = false) :
    (valuesPairs .plain v 64).lookup r = none :=
  lookup_none_of_keys (by rw [show (valuesPairs .plain v 64).map Prod.fst =
    (List.range 64).map (pairReg .plain) by simp [valuesPairs]]; exact h)

theorem statP_mx (v : V) : valueOfD p L g (statP v) 7255 = mxVal v := by
  simp only [valueOfD, valuesData_statP, List.lookup_append,
    pairs_lookup_none v (r := 7255) (by kernel_rfl), Option.none_or]
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf <;> rfl

theorem statP_fold (v : V) :
    valueOfD p L g (statP v) 5509 = .float .f32 (foldP v) := by
  simp only [valueOfD, valuesData_statP, List.lookup_append,
    pairs_lookup_none v (r := 5509) (by kernel_rfl), Option.none_or]
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf <;> rfl

theorem statP_pair (v : V) {j : Nat} (hj : j < 64) :
    valueOfD p L g (statP v) (pairReg .plain j) =
      .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))) := by
  have hnd : ((valuesPairs .plain v 64).map Prod.fst).Nodup := by
    rw [show (valuesPairs .plain v 64).map Prod.fst =
      (List.range 64).map (pairReg .plain) by simp [valuesPairs]]
    exact nodup_of_nodupB (by kernel_rfl)
  have hm : (pairReg .plain j, Value.pair (.float .f32 (v.score (2 * j)))
      (.float .f32 (v.score (2 * j + 1)))) ∈ valuesPairs .plain v 64 :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have := lookup_prefix (X := valuesPlainP p v) hnd hm
  simp only [valueOfD, valuesData_statP, this, Option.getD_some]

theorem mxVal_eqP (v : V) : mxVal v = erealValue .f32 (mxE v) := by
  cases h : v.mf
  · simp only [mxVal, mxE, h, Bool.false_eq_true, ↓reduceIte, erealValue_bot]
  · simp only [mxVal, mxE, h, ↓reduceIte, erealValue_coe]

/-! ### The condition of the run -/

def maxPK : List (Nat × Kd) :=
  (7255, .s .ni) :: (List.range 64).map fun j => (pairReg .plain j, .pr .ni)

theorem ni_float (r : ℝ) : SK.ni.Has (.float .f32 r) :=
  .inl ⟨clean_float _, _, readEReal_float _⟩

theorem maxPK_has (v : V) : ∀ q ∈ maxPK, q.2.Has (valueOfD p L g (statP v) q.1) := by
  intro q hq
  simp only [maxPK, List.mem_cons, List.mem_map, List.mem_range] at hq
  rcases hq with rfl | ⟨j, hj, rfl⟩
  · show SK.ni.Has _
    rw [statP_mx]
    unfold mxVal
    split
    · exact ni_float _
    · exact .inr rfl
  · show (Kd.pr .ni).Has _
    rw [statP_pair v hj]
    exact pair_has (ni_float _) (ni_float _)

theorem maxP_facts0_eq (V : Nat → Value) :
    Gen.maxP_facts0 V = factsFrom ((Gen.maxP_facts0 V).map Prod.fst) V := by
  kernel_rfl

macro "fns_okmaxP" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.maxP_items0, Gen.maxP_items1, Gen.maxP_items2,
    Gen.maxP_items3, Gen.maxP_items4, and_true, true_and]
  repeat' first | exact maxE_maxSpec | constructor))

@[irreducible] def mP1 : List (Nat × Kd) :=
  kList ((Gen.maxP_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf maxPK) Gen.maxP_items0)
@[irreducible] def mP2 : List (Nat × Kd) :=
  kList ((Gen.maxP_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mP1) Gen.maxP_items1)
@[irreducible] def mP3 : List (Nat × Kd) :=
  kList ((Gen.maxP_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mP2) Gen.maxP_items2)
@[irreducible] def mP4 : List (Nat × Kd) :=
  kList ((Gen.maxP_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mP3) Gen.maxP_items3)
@[irreducible] def mP5 : List (Nat × Kd) :=
  kList ((Gen.maxP_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mP4) Gen.maxP_items4)

theorem maxP_kok (V : Nat → Value) :
    (kOk (kOf maxPK) Gen.maxP_items0 &&
      kNext maxPK Gen.maxP_items0 ((Gen.maxP_facts1 V).map Prod.fst) mP1 &&
      kOk (kOf mP1) Gen.maxP_items1 &&
      kNext mP1 Gen.maxP_items1 ((Gen.maxP_facts2 V).map Prod.fst) mP2 &&
      kOk (kOf mP2) Gen.maxP_items2 &&
      kNext mP2 Gen.maxP_items2 ((Gen.maxP_facts3 V).map Prod.fst) mP3 &&
      kOk (kOf mP3) Gen.maxP_items3 &&
      kNext mP3 Gen.maxP_items3 ((Gen.maxP_facts4 V).map Prod.fst) mP4 &&
      kOk (kOf mP4) Gen.maxP_items4 &&
      kNext mP4 Gen.maxP_items4 ((Gen.maxP_facts5 V).map Prod.fst) mP5) = true := by
  unfold maxPK
  kernel_rfl

theorem maxP_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf maxPK r).Has (lookupD (Gen.maxP_facts0 V1) r)) : Gen.maxP_cond V1 := by
  have h10 := maxP_kok V1
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
  have hG0 : factsFrom ((Gen.maxP_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxP_facts0 V1)) Gen.maxP_items0) = Gen.maxP_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.maxP_items0 := by fns_okmaxP
  obtain ⟨c0, k1⟩ := kpiece_lit (L := maxPK) (L' := mP1) (G := Gen.maxP_facts1 V1)
    (items := Gen.maxP_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.maxP_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxP_facts1 V1)) Gen.maxP_items1) = Gen.maxP_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.maxP_items1 := by fns_okmaxP
  obtain ⟨c1, k2⟩ := kpiece_lit (L := mP1) (L' := mP2) (G := Gen.maxP_facts2 V1)
    (items := Gen.maxP_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.maxP_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxP_facts2 V1)) Gen.maxP_items2) = Gen.maxP_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.maxP_items2 := by fns_okmaxP
  obtain ⟨c2, k3⟩ := kpiece_lit (L := mP2) (L' := mP3) (G := Gen.maxP_facts3 V1)
    (items := Gen.maxP_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.maxP_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxP_facts3 V1)) Gen.maxP_items3) = Gen.maxP_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.maxP_items3 := by fns_okmaxP
  obtain ⟨c3, k4⟩ := kpiece_lit (L := mP3) (L' := mP4) (G := Gen.maxP_facts4 V1)
    (items := Gen.maxP_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.maxP_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxP_facts4 V1)) Gen.maxP_items4) = Gen.maxP_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.maxP_items4 := by fns_okmaxP
  obtain ⟨c4, k5⟩ := kpiece_lit (L := mP4) (L' := mP5) (G := Gen.maxP_facts5 V1)
    (items := Gen.maxP_items4) hG4 hk4 k4 hf4 hn5
  exact ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩

theorem maxP_ok (v : V) : Gen.maxP_cond (valueOfD p L g (statP v)) := by
  refine maxP_chain _ ?_
  rw [maxP_facts0_eq]
  exact kstart (by kernel_rfl) (maxPK_has v)

/-- **A plain round's maximum** at pc 6877. -/
theorem maxP_val (v : V) :
    Gen.maxP_v6876 (valueOfD p L g (statP v)) = .float .f32 (foldP v) := by
  rw [maxP_value _ (mxE v) (fun i => (v.score i : EReal)) ((statP_mx v).trans (mxVal_eqP v))
    fun j hj => by rw [statP_pair v hj, erealValue_coe, erealValue_coe]]
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf
  · exact (congrArg (erealValue .f32) (foldB_bot _)).trans (erealValue_coe _ _)
  · exact (congrArg (erealValue .f32) (foldB_coe _ _)).trans (erealValue_coe _ _)

/-- **From pc 6747 to the cut** (pc 6877): the run with the live registers' facts carried. -/
theorem maxP_mid (v : V) {X : Value} (hX : valueOfD p L g (statP v) 7255 = X) :
    ∃ n, Seg kernel Assumptions.all L g n 6747
      ((7255, X) :: factsFrom (liveCut 6747) (valueOfD p L g (statP v))) 6877
      ((7255, X) :: factsFrom (liveCut 6877) (valueOfD p L g (statP v))) := by
  have p3 := seg_frame (lo := 6747) (hi := 6890)
    (H := factsFrom (liveCut 6747) (valueOfD p L g (statP v)))
    (seg_of_segD (Gen.maxP_run L g (valueOfD p L g (statP v))) (maxP_ok v))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  refine Seg.comp_ex (seg_start_ex p3 fun R hR => (holds_append _ _ _).mpr
    ⟨by rw [maxP_facts0_eq]; exact holds_sub hR.2 (by kernel_rfl), hR.2⟩) ?_
  refine ⟨0, Seg.refl _ _ |>.weaken_end fun R hR => ?_⟩
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
  simp only [Gen.maxP_facts5, holds_cons, holds_nil, and_true] at h1
  have hc : (liveCut 6877).all (fun r => r == 5509 || (liveCut 6747).contains r) = true := by
    kernel_rfl
  refine ⟨?_, holds_of_pointwise fun r hr => ?_⟩
  · rw [← hX]; exact holds_mem h2 (mem_factsFrom
      (List.contains_iff_mem.mp (show (liveCut 6747).contains 7255 = true by kernel_rfl)))
  · have := List.all_eq_true.mp hc r hr
    rcases Bool.or_eq_true_iff.mp this with h | h
    · rw [beq_iff_eq.mp h, h1, maxP_val, statP_fold]
    · exact holds_mem h2 (mem_factsFrom (List.contains_iff_mem.mp h))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
