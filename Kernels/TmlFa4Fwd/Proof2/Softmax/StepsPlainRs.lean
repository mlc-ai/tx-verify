-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainE3
public import Lemmas.Flow.Recip

@[expose] public section

/-! # A plain round's row sum: the kinds of its runs and its value

The row sum (pcs 7466 to 7598) is run a (the row sum before the round times the factor), the
move of `0` at pc 7467 and run b (the add tree). Run a's start kinds are run 4's end kinds with
`%r6197` and `%r432` reals; run b's are run a's end kinds with the zero; the last `add.f32` reads
two reals, so the sum is the number value `rsPG` (`rsP_float`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The P part's data have run 4's end kinds. -/
theorem pP_kinds (hp : Pre p L m) (v : V) : ∀ r, (kOf r4L3 r).Has (lookupD (pPData p v) r) := by
  intro r
  have h := (expoP4_ok hp v).2 r
  cases hr : (expoPE p v).lookup r with
  | some x =>
    have e : lookupD (expoPE p v) r = x := by simp only [lookupD, hr, Option.getD_some]
    have e2 : lookupD (pPData p v) r = x := by
      simp only [pPData, lookupD, List.lookup_append, hr, Option.some_or, Option.getD_some]
    rw [e2, ← e]
    exact h
  | none =>
    have hk : (r4L3.lookup r) = none := by
      have hsub : (r4L3.map Prod.fst).all (((expoPE p v).map Prod.fst).contains ·) = true := by
        unfold expoPE; kernel_rfl
      cases e : r4L3.lookup r with
      | none => rfl
      | some k =>
        have hm := List.mem_map_of_mem (f := Prod.fst) (mem_of_lookupK e)
        have := List.contains_iff_mem.mp (List.all_eq_true.mp hsub r hm)
        exact absurd hr (by
          obtain ⟨y, hy⟩ := lookup_some this
          rw [hy]; simp)
    simp only [kOf, hk, Option.getD_none]
    trivial

theorem one_fl : SK.fl.Has (.bits 32 (BitVec.ofNat 64 1065353216)) := by
  have hc := classify_word f32Value_one one_ne_zero (by norm_num)
  rw [show truncBits 32 (BitVec.ofNat 64 1065353216) = BitVec.ofNat 64 1065353216 by decide] at hc
  refine ⟨⟨rfl, ?_, ?_⟩, 1, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ h; cases h; decide
  have := readEReal_bits_fin (w := 32) (x := BitVec.ofNat 64 1065353216) (s := 1) hc
  simpa using this

theorem facP_fl (p : Params) (v : V) : SK.fl.Has (facP p v) := by
  unfold facP
  split
  · split
    · exact one_fl
    · exact has_float_fl _
  · exact has_float_fl _

theorem pP_7257 (v : V) : lookupD (pPData p v) 7257 = .float .f32 v.rs := by kernel_rfl
theorem pP_1492 (v : V) : lookupD (pPData p v) 1492 = facP p v := by kernel_rfl

/-- Run a's start kinds. -/
def raK : List (Nat × Kd) :=
  kList ((Gen.rsumPa_facts0 fun _ => .pred false).map Prod.fst)
    (Function.update (Function.update (kOf r4L3) 7257 (.s .fl)) 1492 (.s .fl))

theorem rsumPa_facts0_eq (V : Nat → Value) :
    Gen.rsumPa_facts0 V = factsFrom ((Gen.rsumPa_facts0 V).map Prod.fst) V := by kernel_rfl
theorem rsumPa_keys (V : Nat → Value) : (Gen.rsumPa_facts0 V).map Prod.fst =
    (Gen.rsumPa_facts0 fun _ => .pred false).map Prod.fst := by kernel_rfl

/-- **Run a**: its condition and its end kinds. -/
theorem rsumPa_ok (hp : Pre p L m) (v : V) : Gen.rsumPa_cond (lookupD (pPData p v)) ∧
    ∀ r, (kOn ((Gen.rsumPa_facts1 (lookupD (pPData p v))).map Prod.fst)
      (kOut (kOf raK) Gen.rsumPa_items0) r).Has
        (lookupD (Gen.rsumPa_facts1 (lookupD (pPData p v))) r) := by
  have hall : ∀ r, ((Function.update (Function.update (kOf r4L3) 7257 (.s .fl)) 1492
      (.s .fl)) r).Has (lookupD (pPData p v) r) := by
    intro r
    by_cases e1 : r = 1492
    · subst e1; rw [Function.update_self, pP_1492]; exact facP_fl p v
    rw [Function.update_of_ne e1]
    by_cases e2 : r = 7257
    · subst e2; rw [Function.update_self, pP_7257]; exact has_float_fl _
    rw [Function.update_of_ne e2]
    exact pP_kinds hp v r
  have k0 : ∀ r, (kOf raK r).Has (lookupD (Gen.rsumPa_facts0 (lookupD (pPData p v))) r) := by
    rw [rsumPa_facts0_eq, rsumPa_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  exact kpiece (by kernel_rfl) (by kernel_rfl) k0 (by simp [kFns, XItem.FnOk, Gen.rsumPa_items0])

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
