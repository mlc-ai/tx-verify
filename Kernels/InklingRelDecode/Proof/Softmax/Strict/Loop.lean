-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Adv
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Vals
import Kernels.InklingRelDecode.Gen.TypedLateLane01
import Kernels.InklingRelDecode.Gen.TypedLate01
@[expose] public section
/-! # The loop's head: the counters of the next iteration and its tests (pcs 1014 to 1049) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

open Lean in
set_option hygiene false in
/-- A window of the lane whose pieces are halves (no singles), over the facts of its end. -/
macro "winh " n:ident : tactic => do
  let w := (n.getId.toString.drop 3).toString
  let ns := Name.mkStr `PTX.Kernels.InklingRelDecode.Gen s!"TypedLate{((w.drop 1).take 2).toString}"
  let ho := mkIdent (Name.mkStr ns (w ++ "_ho_ok"))
  `(tactic|
    (refine $n (A := Assumptions.all) (R := LateR' L g) (fp3_of (by decide +kernel))
      (facts_nmem (by (try dsimp only); decide +kernel) (by (try dsimp only); decide +kernel))
      (sub_facts (fun _ h => h) (by (try dsimp only); decide +kernel))
      (by intro pc h; exact absurd h (List.not_mem_nil))
      (by intro pc h; exact half_late (by revert pc; decide +kernel) ($ho pc h))))

/-- The test of pc 1049 is the equality of the counters. -/
theorem cmp_eq64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    compare Cmp.eq IType.b 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 b)) = decide (b = a) := by
  simp only [compare, truncBits, BitVec.toNat_ofNat, Int.natCast_mod, Int.natCast_pow]
  simp only [decide_eq_decide]
  omega

/-- The closers of the counters of the loop's end. -/
macro "late_loop" : tactic => `(tactic| first
  | late_vals
  | (simp [Control.valueOf, Control.scalarValue, Control.u32, b32, Nat.succ_mul, Nat.add_mul]
     exact congrArg (BitVec.ofNat 64) (by omega))
  | (simp [Control.valueOf, Control.scalarValue]
     exact cmp_eq64 (by omega) (by omega)))

/-- A span whose end facts are implied by those of a span's end. -/
theorem SegQ.endIn {Q : TState → Prop} {a b : Nat} {F G G' : List (Nat × Value)}
    (h : SegQ kernel Assumptions.all L g Q a F b G) (hs : ∀ p ∈ G', p ∈ G) :
    SegQ kernel Assumptions.all L g Q a F b G' :=
  h.comp (SegQ.weaken fun _ hR => holds_of_forall fun p hp => holds_mem hR (hs p hp))

theorem same_i0 (e : Control.Entry) (L : Launch) (g i : Nat) (s z : Site)
    (v : Control.Carry) : ∀ r ∈ [3, 175, 177, 462, 463, 464, 478],
      Control.valueOf e L g ⟨s, i, v⟩ r = Control.valueOf e L g ⟨z, i + 1, v⟩ r := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [Control.valueOf, Control.scalarValue, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem same_i1 (e : Control.Entry) (L : Launch) (g i : Nat) (s z : Site)
    (v : Control.Carry) : ∀ r ∈ [483, 486, 491, 496, 497, 500, 501],
      Control.valueOf e L g ⟨s, i, v⟩ r = Control.valueOf e L g ⟨z, i + 1, v⟩ r := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [Control.valueOf, Control.scalarValue, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem same_i2 (e : Control.Entry) (L : Launch) (g i : Nat) (s z : Site)
    (v : Control.Carry) : ∀ r ∈ [532, 533, 610, 623, 624, 666, 1533],
      Control.valueOf e L g ⟨s, i, v⟩ r = Control.valueOf e L g ⟨z, i + 1, v⟩ r := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [Control.valueOf, Control.scalarValue, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem same_i3 (e : Control.Entry) (L : Launch) (g i : Nat) (s z : Site)
    (v : Control.Carry) : ∀ r ∈ [1956, 1957, 1958, 1959, 2023, 2024],
      Control.valueOf e L g ⟨s, i, v⟩ r = Control.valueOf e L g ⟨z, i + 1, v⟩ r := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [Control.valueOf, Control.scalarValue, Nat.reduceEqDiff, ↓reduceIte, and_self]

/-- The registers live at the test that the iteration's end does not write keep their value. -/
theorem stable_1050 (e : Control.Entry) (L : Launch) (g i : Nat) (s z : Site)
    (v : Control.Carry) : ∀ r ∈ Control.ctlLive 1050, r ∈ [1912, 1913, 2446, 91] ∨
      Control.valueOf e L g ⟨s, i, v⟩ r = Control.valueOf e L g ⟨z, i + 1, v⟩ r := by
  have key : ∀ r ∈ Control.ctlLive 1050, r ∈ [1912, 1913, 2446, 91] ∨
      r ∈ [3, 175, 177, 462, 463, 464, 478] ∨ r ∈ [483, 486, 491, 496, 497, 500, 501] ∨
      r ∈ [532, 533, 610, 623, 624, 666, 1533] ∨ r ∈ [1956, 1957, 1958, 1959, 2023, 2024] := by
    decide +kernel
  intro r hr
  rcases key r hr with h | h | h | h | h
  · exact .inl h
  · exact .inr (same_i0 e L g i s z v r h)
  · exact .inr (same_i1 e L g i s z v r h)
  · exact .inr (same_i2 e L g i s z v r h)
  · exact .inr (same_i3 e L g i s z v r h)

/-- The facts of an iteration's end: the data facts and the table of `pc` at the values `V`. -/
noncomputable abbrev LF (L : Launch) (w : Data.Vals) (pc : Nat) (V : Nat → Value) :
    List (Nat × Value) :=
  Data.dF L ⟨⟨.arrive, 0, {}⟩, w⟩ ++ factsFrom (Control.ctlLive pc) V

/-- **The packs** of the P payload keep the facts. -/
theorem pack_win (V : Nat → Value) (w : Data.Vals) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1014 (LF L w 1014 V)
      1046 (LF L w 1046 V) := by
  refine SegQ.comp (b := 1022) (G := LF L w 1046 V) ?_ ?_
  · winh lw_l01_1014
  refine SegQ.comp (b := 1030) (G := LF L w 1046 V) ?_ ?_
  · winh lw_l01_1022
  refine SegQ.comp (b := 1038) (G := LF L w 1046 V) ?_ ?_
  · winh lw_l01_1030
  · winh lw_l01_1038

/-- The registers of the test that the iteration's end writes. -/
abbrev wr50 : List Nat := [1912, 1913, 2446, 91]

/-- The facts of the test: the registers it writes have the values of the next iteration. -/
noncomputable abbrev E50 (e : Control.Entry) (L : Launch) (g i : Nat) (v : Control.Carry) (z : Site)
    (w : Data.Vals) : List (Nat × Value) :=
  Data.dF L ⟨⟨.arrive, 0, {}⟩, w⟩ ++ ((1912, Control.valueOf e L g ⟨z, i + 1, v⟩ 1912) ::
    (1913, Control.valueOf e L g ⟨z, i + 1, v⟩ 1913) ::
    (2446, Control.valueOf e L g ⟨z, i + 1, v⟩ 2446) ::
    (91, Control.valueOf e L g ⟨z, i + 1, v⟩ 91) ::
    factsFrom ((Control.ctlLive 1050).filter (· ∉ wr50)) (Control.valueOf e L g ⟨.arrive, i, v⟩))

/-- The counters of the next iteration and the test: from pc 1046 to the branch at 1050. -/
theorem tail_1046 (i : Nat) (v : Control.Carry) (w : Data.Vals) (hl : e.limit < 2 ^ 32)
    (hi : i ≤ e.limit) (z : Site) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1046
      (LF L w 1046 (Control.valueOf e L g ⟨.arrive, i, v⟩)) 1050 (E50 e L g i v z w) := by
  refine SegQ.tauAll _ ?_
  simp only [LF, E50, Data.dF, Data.dFS, Data.inRound, Bool.false_eq_true, ↓reduceIte,
    List.append_nil, List.cons_append, List.nil_append]
  late_ctl 1046, 1050 using late_loop

/-- **The counters** of the next iteration and its test: from pc 1014 to the branch at 1050. -/
theorem head_loop (i : Nat) (v : Control.Carry) (w : Data.Vals) (hl : e.limit < 2 ^ 32)
    (hi : i ≤ e.limit) (z : Site) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1014
      (LF L w 1014 (Control.valueOf e L g ⟨.arrive, i, v⟩)) 1050
      (LF L w 1050 (Control.valueOf e L g ⟨z, i + 1, v⟩)) := by
  refine SegQ.endIn (G := E50 e L g i v z w)
    (SegQ.comp (pack_win _ w) (tail_1046 i v w hl hi z)) fun p hp => ?_
  rcases List.mem_append.mp hp with h | h
  · exact List.mem_append_left _ h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    refine List.mem_append_right _ ?_
    by_cases hw : r ∈ wr50
    · simp only [wr50, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp
    · have hk : r ∈ (Control.ctlLive 1050).filter (· ∉ wr50) :=
        List.mem_filter.mpr ⟨hr, by simpa using hw⟩
      rcases stable_1050 e L g i .arrive z v r hr with h | h
      · exact absurd h hw
      · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r, hk, ?_⟩))))
        rw [h]
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
