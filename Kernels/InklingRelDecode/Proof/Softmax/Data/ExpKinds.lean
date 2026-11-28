-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpRun
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpLib
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Kinds

@[expose] public section

/-! # The exponent window's first run gives numbers or `-inf`

From the running maximum (a number or `-inf`, a number where the rescale test holds), the round's
maximum used (a number), the negated scale (a number), the scale (positive) and the 64 masked
scores (numbers or `-inf`), the run of pcs 1847 to 1912 writes the 64 shifted scores, each a
number or `-inf`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- The registers of the 64 masked scores the window reads. -/
def scoreRegs : List Nat := runE1.live.filter fun r => decide (1400 ≤ r ∧ r < 1523)

/-- **What the exponent window reads**: the running maximum `m` (1914), the maximum used by the
round (1523), the rescale test (168), the scale (498), the negated scale (499) and the scores. -/
structure ExpIn (V : Nat → Value) : Prop where
  m : (Kd.s .ni).Has (V 1914)
  mu : (Kd.s .fl).Has (V 1523)
  pm : predOf (V 168) = true → (Kd.s .fl).Has (V 1914)
  sc : (Kd.s .pw).Has (V 498)
  ng : (Kd.s .fl).Has (V 499)
  s : ∀ r ∈ scoreRegs, (Kd.s .ni).Has (V r)

/-- The registers the first window leaves for the exponent window: the word it sends, the 64
masked scores and the two predicates of its mask. -/
def kXin : List Nat := 1520 :: (scoreRegs ++ [179, 180])

theorem fF_reg3 {E : List Value → Exec Value} {a b c : Nat} {x y z : Value} (hb : b ≠ a)
    (hc : c ≠ a) (hcb : c ≠ b) : fF E [.reg a, .reg b, .reg c] [x, y, z] = E [x, y, z] := by
  simp only [fF, regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, fOpnd, lk,
    List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hb, beq_false_of_ne hc,
    beq_false_of_ne hcb, beq_self_eq_true, Option.getD_some]

theorem scoreRegs_ne : ∀ r ∈ scoreRegs, r ≠ 498 ∧ r ≠ 1526 := by decide +kernel

theorem fma_out {V : Nat → Value} {s : Nat} {c : Value} (h : ExpIn V) (hs : s ∈ scoreRegs)
    (hc : (Kd.s .fl).Has c) : (Kd.s .ni).Has (okVal (.bits 32 0)
      ((fF (floatE (fmaI .rn false)) [.reg s, .reg 498, .reg 1526]) [V s, V 498, c])) := by
  obtain ⟨h1, h2⟩ := scoreRegs_ne s hs
  rw [fF_reg3 (a := s) (b := 498) (c := 1526) (Ne.symm h1) (Ne.symm h2) (by omega)]
  exact fma_has (h.s s hs) h.sc hc

/-- The maximum used and the shifted scores. -/
theorem e1_has {V : Nat → Value} (h : ExpIn V) :
    ∀ p ∈ Gen.ex1_facts3 V, (Kd.s .ni).Has p.2 := by
  have h47 : (Kd.s .fl).Has (Gen.ex1_v1847 V) :=
    selp2_has (k := .fl) (by decide) (by decide) (by decide) (by decide) h.pm h.mu
  have h48 : (Kd.s .fl).Has (Gen.ex1_v1848 V) := mul_fl_has h47 h.ng
  intro p hp
  simp only [Gen.ex1_facts3, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' rcases hp with rfl | hp
  all_goals exact fma_out h (by decide) h48

/-! ### The second run -/

/-- The registers of the shifted scores (the first run's outputs). -/
def xRegs : List Nat := runE1.outs

/-- The outputs of the sixteen software instances. -/
def swOuts : List Nat := (List.range 16).map (1271 + ·)

/-- The kind of a word of the second run: a pair of numbers in the registers 1994 to 2017, else
a number. -/
def ExpTy (r : Nat) (v : Value) : Prop :=
  if 1994 ≤ r ∧ r < 2018 then (Kd.pr .fl).Has v else (Kd.s .fl).Has v

theorem expTy_pr {r : Nat} {v : Value} (h : 1994 ≤ r ∧ r < 2018) (hv : (Kd.pr .fl).Has v) :
    ExpTy r v := by simp only [ExpTy, h, and_self, ite_true]; exact hv

theorem expTy_s {r : Nat} {v : Value} (h : ¬ (1994 ≤ r ∧ r < 2018)) (hv : (Kd.s .fl).Has v) :
    ExpTy r v := by simp only [ExpTy, h, ite_false]; exact hv

theorem add2_out {a b : Nat} {x y : Value} (hb : b ≠ a) (hx : (Kd.pr .fl).Has x)
    (hy : (Kd.pr .fl).Has y) :
    (Kd.pr .fl).Has (okVal (.bits 32 0) ((fF add2NL [.reg a, .reg b]) [x, y])) := by
  have e : (fF add2NL [.reg a, .reg b]) [x, y] = add2NE x y := by
    simp only [fF, regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, fOpnd, lk,
      List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hb,
      beq_self_eq_true, Option.getD_some, add2NL]
  rw [e]
  exact add2N_fl_has hx hy

/-- **The exponentials, their sums and the row sum are numbers**, when the shifted scores are
numbers or `-inf` and the outputs of the software instances are numbers. -/
theorem e2_has {W : Nat → Value} (hx : ∀ r ∈ xRegs, (Kd.s .ni).Has (W r))
    (hy : ∀ r ∈ swOuts, (Kd.s .fl).Has (W r)) : ∀ p ∈ Gen.ex2_facts5 W, ExpTy p.1 p.2 := by
  intro p hp
  simp only [Gen.ex2_facts5, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' rcases hp with rfl | hp
  all_goals dsimp only
  all_goals first
    | (refine expTy_pr (by decide) ?_
       repeat' first
        | exact hx _ (by decide)
        | apply ex2_has | apply join_fl_has)
    | (refine expTy_s (by decide) ?_
       repeat' first
        | exact hx _ (by decide)
        | apply ex2_has | apply join_fl_has | apply add2_out (by decide)
        | apply add_fl_has | apply split1_has | apply split2_has
        | refine selp2_has (k := .fl) (by decide) (by decide) (by decide) (by decide)
            (fun _ => hy _ (by decide)) ?_)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
