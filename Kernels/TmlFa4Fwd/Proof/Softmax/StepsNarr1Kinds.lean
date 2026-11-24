-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.NegScale
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # Input kinds for the first round's exponent stretch

These facts supply the generated run starting at pc 4399. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The kinds of the start values -/

theorem mre_lt_top {k : Nat} {mw : BitVec 64} {i : Nat} {x : EReal} (hx : x < ⊤) :
    mre k mw i x < ⊤ := by
  unfold mre
  split_ifs <;> first | exact hx | exact bot_lt_top

theorem foldM_lt_top (mw : BitVec 64) {sc : Nat → EReal} (hsc : ∀ n, sc n < ⊤) :
    foldM mw sc < ⊤ := by
  simp only [foldM]
  repeat' apply max_lt
  all_goals exact mre_lt_top (hsc _)

theorem bpe_lt_top (bf : Nat → Bool) (sc : Nat → ℝ) (n : Nat) : bpe bf sc n < ⊤ := by
  unfold bpe; split <;> simp

theorem foldF_lt_top (p : Params) (L : Launch) (g : Nat) (v : V) : foldF p L g v < ⊤ :=
  foldM_lt_top _ fun n => bpe_lt_top _ _ n

theorem readEReal_zero32 : Assumption.readEReal .f32 (.bits 32 (BitVec.ofNat 64 0)) =
    some (.ok ((0 : ℝ) : EReal)) := by
  have hz := classify_bits (fmt := .f32) (n := 0) (x := .zero false) (by decide) (by decide)
  change Assumption.readEReal.ofDatum (classify .f32 (.bits 32 (BitVec.ofNat 64 0))) = _
  change classify .f32 (.bits 32 (BitVec.ofNat 64 0)) = .ok (.zero false) at hz
  rw [hz]
  simp [Assumption.readEReal.ofDatum, pure, Except.pure]

theorem selMax_fl {x : EReal} (hx : x < ⊤) : SK.fl.Has (selMax x) := by
  unfold selMax
  split
  · refine ⟨?_, 0, readEReal_zero32⟩
    refine ⟨rfl, ?_, ?_⟩
    · intro _ _ _ h; cases h
    · intro _ _ h; cases h; decide
  · rename_i hb
    have : x = ((x.toReal : ℝ) : EReal) := (EReal.coe_toReal hx.ne hb).symm
    rw [this, erealValue_coe]
    exact has_float_fl _

theorem elemVal_ni (mw : BitVec 64) (bf : Nat → Bool) (sc : Nat → ℝ) (n : Nat) :
    SK.ni.Has (elemVal mw bf sc n) := by
  unfold elemVal bv32
  split_ifs <;> first | exact .inr rfl | exact .inl (has_float_fl _)

theorem paramW_pw {S : Nat} {s : ℚ} (hS : f32Value S = some s) (h0 : 0 < s) (h32 : S < 2 ^ 32) :
    SK.pw.Has (.bits 32 (Epilogue.paramW S)) := by
  refine ⟨⟨rfl, ?_, ?_⟩, (s : ℝ), by exact_mod_cast h0,
    readEReal_bits_fin (classify_word hS h0.ne' h32)⟩
  · intro _ _ _ h; cases h
  · intro _ _ h
    cases h
    exact truncBits_toNat_lt 32 _

theorem vExpo1_narr (p : Params) (L : Launch) (g : Nat) (v : V) :
    valueOfD p L g ⟨.narr .first, v, 0, []⟩ = valueOfD0 p L g ⟨.narr .first, v, 0, []⟩ := rfl

/-- The kinds of the exponent stretch's start values. -/
def expo1K : List (Nat × Kd) :=
  (3685, .s .fl) :: (1230, .s .fl) :: (7132, .s .pw) :: elemRegs.map fun r => (r, .s .ni)

theorem elem_ni (p : Params) (L : Launch) (g : Nat) (v : V) {r : Nat} (hr : r ∈ elemRegs) :
    SK.ni.Has (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩ r) := by
  have hk : r ∈ (valuesNarr1 p L g v).map Prod.fst := by
    have h : elemRegs.all (((valuesNarr1 p L g v).map Prod.fst).contains ·) = true := by
      kernel_rfl
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h r hr)
  obtain ⟨x, hx⟩ := lookup_some hk
  have hm := mem_of_lookup hx
  simp only [valueOfD0, valuesData0, hx, Option.getD_some]
  simp only [valuesNarr1, List.mem_map, List.mem_range, List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨n, -, -, rfl⟩
  · exact absurd (List.contains_iff_mem.mpr hr) (by
      rw [show elemRegs.contains 3685 = false by rfl]; simp)
  · exact absurd (List.contains_iff_mem.mpr hr) (by
      rw [show elemRegs.contains 7256 = false by rfl]; simp)
  · exact elemVal_ni _ _ _ _

theorem lookup_head (k : Nat) (x : Value) (l : List (Nat × Value)) :
    ((k, x) :: l).lookup k = some x := by
  simp [List.lookup]

theorem v0_3685 (p : Params) (L : Launch) (g : Nat) (v : V) :
    valueOfD0 p L g ⟨.narr .first, v, 0, []⟩ 3685 = selMax (foldF p L g v) := by
  unfold valueOfD0
  rw [show valuesData0 p L g ⟨.narr .first, v, 0, []⟩ = valuesNarr1 p L g v from rfl,
    valuesNarr1, lookup_head, Option.getD_some]

/-- The values the exponent stretch reads are the arrival state's, after the negated scale. -/
theorem vExpo1_eq (v : V) {V0 : Nat → Value} {r : Nat}
    (hr : r ∈ (Gen.expo1_facts0 V0).map Prod.fst) :
    vExpo1 p L g v r =
      Function.update (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) 1230 (negS p) r := by
  by_cases e : r = 1230
  · subst e; rw [Function.update_self]; rfl
  rw [Function.update_of_ne e]
  cases h : (valuesNarr1 p L g v).lookup r with
  | some x =>
    simp only [vExpo1, valueOfD0, List.lookup_append, h, Option.some_or, Option.getD_some]
    show x = ((valuesNarr1 p L g v).lookup r).getD _
    rw [h, Option.getD_some]
  | none =>
    have hk : ((Gen.expo1_facts0 V0).map Prod.fst).all (fun r => r == 1230 || r == 7132 ||
        ((valuesNarr1 p L g v).map Prod.fst).contains r) = true := by kernel_rfl
    have := List.all_eq_true.mp hk r hr
    simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at this
    rcases this with rfl | hc
    · rfl
    · obtain ⟨x, hx⟩ := lookup_some (List.contains_iff_mem.mp hc)
      rw [h] at hx; cases hx

theorem expo1K_has (hp : Pre p L m) (v : V) :
    ∀ q ∈ expo1K, q.2.Has (vExpo1 p L g v q.1) := by
  obtain ⟨s, hS, hs0, h32⟩ := scale_word hp
  have hk : ∀ q ∈ expo1K, q.1 ∈ (Gen.expo1_facts0 (vExpo1 p L g v)).map Prod.fst := by
    have h : (expo1K.map Prod.fst).all
        (((Gen.expo1_facts0 (vExpo1 p L g v)).map Prod.fst).contains ·) = true := by
      unfold expo1K; kernel_rfl
    intro q hq
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h q.1 (List.mem_map_of_mem hq))
  intro q hq
  rw [vExpo1_eq v (hk q hq)]
  simp only [expo1K, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | rfl | rfl | ⟨r, hr, rfl⟩
  · show SK.fl.Has (Function.update (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) 1230 (negS p) 3685)
    simp only [Function.update_of_ne (by decide : (3685 : Nat) ≠ 1230), v0_3685]
    exact selMax_fl (foldF_lt_top p L g v)
  · show SK.fl.Has (Function.update (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) 1230 (negS p) 1230)
    simp only [Function.update_self, negS]
    exact has_float_fl _
  · show SK.pw.Has (Function.update (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) 1230 (negS p) 7132)
    simp only [Function.update_of_ne (by decide : (7132 : Nat) ≠ 1230), ← vExpo1_narr,
      valueOfD_ctl _ (by rfl : ctl 7132 = true)]
    exact paramW_pw hS hs0 h32
  · have hne : r ≠ 1230 := by
      rintro rfl
      exact absurd (List.contains_iff_mem.mpr hr) (by
        rw [show elemRegs.contains 1230 = false by rfl]; simp)
    show SK.ni.Has (Function.update (valueOfD0 p L g ⟨.narr .first, v, 0, []⟩) 1230 (negS p) r)
    simp only [Function.update_of_ne hne]
    exact elem_ni p L g v hr

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
