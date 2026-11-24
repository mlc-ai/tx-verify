-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Cvt

@[expose] public section

/-! # Floating-point instruction spellings

The Core states floating-point arithmetic as one `Op.float` record (`PROG-ISA-FLOAT`) whose
qualifier fields default to the unqualified, IEEE, non-saturating form, so a bare `fadd.f32`
instruction is a short record. These abbreviations give the arithmetic, comparison and
selection forms their PTX spelling for proof files; each is definitionally the record the
generated code tables contain, so `Flow.code_*` matches them without unfolding. -/

namespace PTX.Flow

/-- The one-lane type of an element format: the type of a non-packed float instruction. -/
abbrev ty1 (fmt : FloatFmt) : FTy := { fmt := fmt, lanes := 1 }

/-- `fadd.<fmt> dst, a, b`. -/
abbrev fadd (fmt : FloatFmt) (dst : Nat) (a b : Opnd) : Op :=
  .float { op := .add, ty := ty1 fmt, dsts := [some dst], srcs := [a, b] }

/-- `fsub.<fmt> dst, a, b`. -/
abbrev fsub (fmt : FloatFmt) (dst : Nat) (a b : Opnd) : Op :=
  .float { op := .sub, ty := ty1 fmt, dsts := [some dst], srcs := [a, b] }

/-- `fmul.<fmt> dst, a, b`. -/
abbrev fmulOp (fmt : FloatFmt) (dst : Nat) (a b : Opnd) : Op :=
  .float { op := .mul, ty := ty1 fmt, dsts := [some dst], srcs := [a, b] }

/-- `fmax.<fmt> dst, a, b`. -/
abbrev fmax (fmt : FloatFmt) (dst : Nat) (a b : Opnd) : Op :=
  .float { op := .max, ty := ty1 fmt, dsts := [some dst], srcs := [a, b] }

/-- `fmin.<fmt> dst, a, b`. -/
abbrev fmin (fmt : FloatFmt) (dst : Nat) (a b : Opnd) : Op :=
  .float { op := .min, ty := ty1 fmt, dsts := [some dst], srcs := [a, b] }

/-- `fma.rn.<fmt> dst, a, b, c`. -/
abbrev fma (fmt : FloatFmt) (dst : Nat) (a b c : Opnd) : Op :=
  .float { op := .fma, ty := ty1 fmt, rnd := some .rn, dsts := [some dst], srcs := [a, b, c] }

/-- `fsetp.<cmp>.<fmt> p|q, a, b`: a comparison writing its predicate to `dst`. -/
abbrev fsetp (c : FCmp) (bop : Option BoolOp) (fmt : FloatFmt) (dst : Nat) (a b : Opnd) : Op :=
  .float { op := .setp c bop, ty := ty1 fmt, dsts := [some dst], srcs := [a, b] }

end PTX.Flow
