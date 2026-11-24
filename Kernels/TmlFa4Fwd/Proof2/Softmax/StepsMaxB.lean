-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsProdB
public import Kernels.TmlFa4Fwd.Proof2.Softmax.BiasMax

@[expose] public section

/-! # The bias round's maximum: the run's condition and value

The run `Gen.maxB_run` (pcs 5536 to 5665) from the values of the statistics store's state: its
condition holds by the kinds of its start values (`maxB_ok`: the maximum before the round and
the 128 products are reals or `-∞`; the kind checker's `max.f32` rule), and its value is the
code's fold (`maxB_val`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The statistics store's state of a bias round. -/
abbrev statB (v : V) : D := ⟨.stat false, v, 0, []⟩

theorem valuesData_statB (v : V) : valuesData p L g (statB v) =
    valuesRun p v ++ valuesBiasM p v ++ valuesProdB p v := rfl

theorem mxVal_eq (v : V) : mxVal v = erealValue .f32 (mxE v) := by
  cases h : v.mf
  · simp only [mxVal, mxE, h, Bool.false_eq_true, ↓reduceIte, erealValue_bot]
  · simp only [mxVal, mxE, h, ↓reduceIte, erealValue_coe]

theorem statB_mx (v : V) : valueOfD p L g (statB v) 7251 = mxVal v := by
  simp only [valueOfD, valuesData_statB, List.lookup_append, valuesRun, List.lookup,
    beq_self_eq_true, Option.some_or, Option.getD_some]

theorem statB_prod (v : V) {j : Nat} (hj : j < 64) :
    valueOfD p L g (statB v) (8317 + 2 * j) =
      .pair (bv32 (bpf v) (bps p v) (2 * j)) (bv32 (bpf v) (bps p v) (2 * j + 1)) := by
  have hnd : ((valuesRun p v ++ valuesBiasM p v ++ valuesProdB p v).map Prod.fst).Nodup := by
    exact nodup_of_nodupB (by kernel_rfl)
  have hm : (8317 + 2 * j, Value.pair (bv32 (bpf v) (bps p v) (2 * j))
      (bv32 (bpf v) (bps p v) (2 * j + 1))) ∈ valuesRun p v ++ valuesBiasM p v ++ valuesProdB p v :=
    List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have := lookup_prefix (X := []) hnd hm
  simp only [List.append_nil] at this
  simp only [valueOfD, valuesData_statB, this, Option.getD_some]

/-! ### The condition of the run -/

def maxBK : List (Nat × Kd) :=
  (7251, .s .ni) :: (List.range 64).map fun j => (8317 + 2 * j, .pr .ni)

theorem ni_bv32 (bf : Nat → Bool) (sc : Nat → ℝ) (n : Nat) : SK.ni.Has (bv32 bf sc n) := by
  unfold bv32
  split
  · exact .inl ⟨clean_float _, _, readEReal_float _⟩
  · exact .inr rfl

theorem maxBK_has (v : V) : ∀ q ∈ maxBK, q.2.Has (valueOfD p L g (statB v) q.1) := by
  intro q hq
  simp only [maxBK, List.mem_cons, List.mem_map, List.mem_range] at hq
  rcases hq with rfl | ⟨j, hj, rfl⟩
  · show SK.ni.Has _
    rw [statB_mx]
    unfold mxVal
    split
    · exact .inl ⟨clean_float _, _, readEReal_float _⟩
    · exact .inr rfl
  · show (Kd.pr .ni).Has _
    rw [statB_prod v hj]
    exact pair_has (ni_bv32 _ _ _) (ni_bv32 _ _ _)

theorem maxB_facts0_eq (V : Nat → Value) :
    Gen.maxB_facts0 V = factsFrom ((Gen.maxB_facts0 V).map Prod.fst) V := by
  kernel_rfl

macro "fns_okmaxB" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.maxB_items0, Gen.maxB_items1, Gen.maxB_items2,
    Gen.maxB_items3, Gen.maxB_items4, and_true, true_and]
  repeat' first | exact maxE_maxSpec | constructor))

@[irreducible] def mB1 : List (Nat × Kd) :=
  kList ((Gen.maxB_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf maxBK) Gen.maxB_items0)
@[irreducible] def mB2 : List (Nat × Kd) :=
  kList ((Gen.maxB_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mB1) Gen.maxB_items1)
@[irreducible] def mB3 : List (Nat × Kd) :=
  kList ((Gen.maxB_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mB2) Gen.maxB_items2)
@[irreducible] def mB4 : List (Nat × Kd) :=
  kList ((Gen.maxB_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mB3) Gen.maxB_items3)
@[irreducible] def mB5 : List (Nat × Kd) :=
  kList ((Gen.maxB_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf mB4) Gen.maxB_items4)

theorem maxB_kok (V : Nat → Value) :
    (kOk (kOf maxBK) Gen.maxB_items0 &&
      kNext maxBK Gen.maxB_items0 ((Gen.maxB_facts1 V).map Prod.fst) mB1 &&
      kOk (kOf mB1) Gen.maxB_items1 &&
      kNext mB1 Gen.maxB_items1 ((Gen.maxB_facts2 V).map Prod.fst) mB2 &&
      kOk (kOf mB2) Gen.maxB_items2 &&
      kNext mB2 Gen.maxB_items2 ((Gen.maxB_facts3 V).map Prod.fst) mB3 &&
      kOk (kOf mB3) Gen.maxB_items3 &&
      kNext mB3 Gen.maxB_items3 ((Gen.maxB_facts4 V).map Prod.fst) mB4 &&
      kOk (kOf mB4) Gen.maxB_items4 &&
      kNext mB4 Gen.maxB_items4 ((Gen.maxB_facts5 V).map Prod.fst) mB5) = true := by
  unfold maxBK
  kernel_rfl

theorem maxB_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf maxBK r).Has (lookupD (Gen.maxB_facts0 V1) r)) : Gen.maxB_cond V1 := by
  have h10 := maxB_kok V1
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
  have hG0 : factsFrom ((Gen.maxB_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxB_facts0 V1)) Gen.maxB_items0) = Gen.maxB_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.maxB_items0 := by fns_okmaxB
  obtain ⟨c0, k1⟩ := kpiece_lit (L := maxBK) (L' := mB1) (G := Gen.maxB_facts1 V1)
    (items := Gen.maxB_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.maxB_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxB_facts1 V1)) Gen.maxB_items1) = Gen.maxB_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.maxB_items1 := by fns_okmaxB
  obtain ⟨c1, k2⟩ := kpiece_lit (L := mB1) (L' := mB2) (G := Gen.maxB_facts2 V1)
    (items := Gen.maxB_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.maxB_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxB_facts2 V1)) Gen.maxB_items2) = Gen.maxB_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.maxB_items2 := by fns_okmaxB
  obtain ⟨c2, k3⟩ := kpiece_lit (L := mB2) (L' := mB3) (G := Gen.maxB_facts3 V1)
    (items := Gen.maxB_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.maxB_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxB_facts3 V1)) Gen.maxB_items3) = Gen.maxB_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.maxB_items3 := by fns_okmaxB
  obtain ⟨c3, k4⟩ := kpiece_lit (L := mB3) (L' := mB4) (G := Gen.maxB_facts4 V1)
    (items := Gen.maxB_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.maxB_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.maxB_facts4 V1)) Gen.maxB_items4) = Gen.maxB_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.maxB_items4 := by fns_okmaxB
  obtain ⟨c4, k5⟩ := kpiece_lit (L := mB4) (L' := mB5) (G := Gen.maxB_facts5 V1)
    (items := Gen.maxB_items4) hG4 hk4 k4 hf4 hn5
  exact ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩

theorem maxB_ok (v : V) : Gen.maxB_cond (valueOfD p L g (statB v)) := by
  refine maxB_chain _ ?_
  rw [maxB_facts0_eq]
  exact kstart (by kernel_rfl) (maxBK_has v)

/-- **The bias round's maximum** at pc 5666. -/
theorem maxB_val (v : V) :
    Gen.maxB_v5665 (valueOfD p L g (statB v)) = erealValue .f32 (foldBE p v) := by
  refine maxB_value _ _ _ ((statB_mx v).trans (mxVal_eq v)) fun j hj => ?_
  rw [statB_prod v hj]
  simp only [bv32, ← erealValue_bvl]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
