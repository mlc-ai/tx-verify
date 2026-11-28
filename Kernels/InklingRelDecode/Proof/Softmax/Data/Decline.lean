-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Flow.OutKinds

@[expose] public section

/-! # The ideal-real rule does not decline an arithmetic instruction on numbers

The scalar `add`, `sub` and `mul` of two operands decline (`execIdealFloat` is `none`) only on a
NaN operand, on `inf - inf` or on `0 * inf`: when both operands read as extended reals the sum or
product is defined. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Assumption

/-- A floating instruction of the given operation and lane count on `.f32`, with one destination
and two sources. -/
def arith2 (op : FOp) (lanes : Nat) (f : FloatInstr) (a b : Opnd) : Bool :=
  f.op == op && f.ty.lanes == lanes && f.ty.fmt == .f32 && f.dsts.map Option.isSome == [true] &&
    f.srcs == [a, b]

private theorem arith2_parts {op lanes f a b} (h : arith2 op lanes f a b = true) :
    f.op = op ∧ f.ty.lanes = lanes ∧ f.ty.fmt = .f32 ∧ (∃ d, f.dsts = [some d]) ∧
      f.srcs = [a, b] := by
  simp only [arith2, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, h5⟩
  rcases hd : f.dsts with _ | ⟨_ | d, _ | ⟨_, _⟩⟩ <;> simp_all

/-- **A scalar product of two operands that read as extended reals is not declined** when it is
defined. -/
theorem ideal_mul1 {L : Launch} {g : Nat} {t : TState} {f : FloatInstr} {a b : Opnd} {x y : EReal}
    (h : arith2 .mul 1 f a b = true) (hx : readERealOpnd t .f32 a = some (.ok x))
    (hy : readERealOpnd t .f32 b = some (.ok y)) (hm : mulEReal x y ≠ none) :
    execIdealFloat L g t (.float f) ≠ none := by
  obtain ⟨h1, h2, h3, ⟨d, hd⟩, h5⟩ := arith2_parts h
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hm
  simp [execIdealFloat, h1, h2, h3, hd, h5, bindRead, hx, hy, hz]

/-- **A scalar sum of two operands that read as extended reals is not declined** when it is
defined. -/
theorem ideal_add1 {L : Launch} {g : Nat} {t : TState} {f : FloatInstr} {a b : Opnd} {x y : EReal}
    (h : arith2 .add 1 f a b = true) (hx : readERealOpnd t .f32 a = some (.ok x))
    (hy : readERealOpnd t .f32 b = some (.ok y)) (hm : addEReal x y ≠ none) :
    execIdealFloat L g t (.float f) ≠ none := by
  obtain ⟨h1, h2, h3, ⟨d, hd⟩, h5⟩ := arith2_parts h
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hm
  simp [execIdealFloat, h1, h2, h3, hd, h5, bindRead, hx, hy, hz]

/-- **A scalar difference of two operands that read as extended reals is not declined** when it
is defined. -/
theorem ideal_sub1 {L : Launch} {g : Nat} {t : TState} {f : FloatInstr} {a b : Opnd} {x y : EReal}
    (h : arith2 .sub 1 f a b = true) (hx : readERealOpnd t .f32 a = some (.ok x))
    (hy : readERealOpnd t .f32 b = some (.ok y)) (hm : addEReal x (-y) ≠ none) :
    execIdealFloat L g t (.float f) ≠ none := by
  obtain ⟨h1, h2, h3, ⟨d, hd⟩, h5⟩ := arith2_parts h
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hm
  simp [execIdealFloat, h1, h2, h3, hd, h5, bindRead, hx, hy, hz]

/-- **A packed sum of two pairs that read as extended reals is not declined** when both lanes are
defined. -/
theorem ideal_add2 {L : Launch} {g : Nat} {t : TState} {f : FloatInstr} {a b : Opnd}
    {x0 x1 y0 y1 : EReal} (h : arith2 .add 2 f a b = true)
    (hx : readERealPair L g t a = some (.ok (x0, x1)))
    (hy : readERealPair L g t b = some (.ok (y0, y1))) (h0 : addEReal x0 y0 ≠ none)
    (h1 : addEReal x1 y1 ≠ none) : execIdealFloat L g t (.float f) ≠ none := by
  obtain ⟨h1', h2, h3, ⟨d, hd⟩, h5⟩ := arith2_parts h
  obtain ⟨z0, hz0⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨z1, hz1⟩ := Option.ne_none_iff_exists'.1 h1
  simp [execIdealFloat, h1', h2, hd, h5, bindRead, hx, hy, hz0, hz1]

/-- **A packed product of two pairs that read as extended reals is not declined** when both lanes
are defined. -/
theorem ideal_mul2 {L : Launch} {g : Nat} {t : TState} {f : FloatInstr} {a b : Opnd}
    {x0 x1 y0 y1 : EReal} (h : arith2 .mul 2 f a b = true)
    (hx : readERealPair L g t a = some (.ok (x0, x1)))
    (hy : readERealPair L g t b = some (.ok (y0, y1))) (h0 : mulEReal x0 y0 ≠ none)
    (h1 : mulEReal x1 y1 ≠ none) : execIdealFloat L g t (.float f) ≠ none := by
  obtain ⟨h1', h2, h3, ⟨d, hd⟩, h5⟩ := arith2_parts h
  obtain ⟨z0, hz0⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨z1, hz1⟩ := Option.ne_none_iff_exists'.1 h1
  simp [execIdealFloat, h1', h2, hd, h5, bindRead, hx, hy, hz0, hz1]

/-- The product of two real numbers is defined. -/
theorem mulEReal_real (r s : ℝ) : mulEReal (r : EReal) (s : EReal) ≠ none := by
  simp [mulEReal, EReal.coe_ne_top, EReal.coe_ne_bot, EReal.coe_eq_zero]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
