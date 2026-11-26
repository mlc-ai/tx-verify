-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Rule
public import Lemmas.Register.RegisterFrame
public import Lemmas.Flow.Regs

@[expose] public section

/-! # Registers by type, and the instructions that cannot fail on them

A register's *tag* says what its value is as far as a local instruction can tell: a bit pattern of
a width, a nonzero one, or a predicate. `Typed env t` says the state's registers have the tags of
`env` (a list whose first entry for a register is its tag). `absOp env op = some (d, tag)` says
that the instruction `op`, a plain integer, move or conversion that reads only registers of `env`
(and constants), writes `d` with a value of `tag` and cannot fail: its local step is
`next (setReg t d v)` (`exec_of_abs`).

The checks are about the instruction's shape and the sources' tags, never about values, so a stretch
of code is typed once for every state whose registers have the tags. -/

namespace PTX.Flow.Tagged
open PTX PTX.Proof

/-- What a register holds, as far as an integer instruction can tell. -/
inductive Tag where
  | bits (w : Nat)
  | nz (w : Nat)
  | pred
  deriving DecidableEq, Repr

/-- A value has the tag. -/
def Tag.ok : Tag → Option Value → Prop
  | .bits w, v => ∃ x, v = some (.bits w x)
  | .nz w, v => ∃ x, v = some (.bits w x) ∧ x.toNat % 2 ^ w ≠ 0
  | .pred, v => ∃ b, v = some (.pred b)

/-- The tags of registers: the first entry of a register is its tag. -/
abbrev Env := List (Nat × Tag)

/-- The state's registers have the tags of `env`. -/
def Typed (env : Env) (t : TState) : Prop :=
  ∀ r tg, env.lookup r = some tg → tg.ok (t.regs r)

/-- An operand read as a bit pattern of any width: a constant or a register of bits. -/
def rb (env : Env) : Opnd → Bool
  | .imm _ => true
  | .reg r => match env.lookup r with
    | some (.bits _) | some (.nz _) => true
    | _ => false
  | _ => false

/-- An operand read as a value of exactly `w` bits: a constant or a register of `w` bits. -/
def rw (env : Env) (w : Nat) : Opnd → Bool
  | .imm _ => true
  | .reg r => match env.lookup r with
    | some (.bits v) | some (.nz v) => v == w
    | _ => false
  | _ => false

/-- An operand read as a predicate: a register of a predicate. -/
def rp (env : Env) : Opnd → Bool
  | .reg r => env.lookup r == some .pred
  | _ => false

/-- A nonzero divisor of width `w`. -/
def rz (env : Env) (w : Nat) : Opnd → Bool
  | .reg r => env.lookup r == some (.nz w)
  | _ => false

variable {L : Launch} {g : Nat} {t : TState} {env : Env}

theorem typed_bits {r w} (ht : Typed env t) (h : env.lookup r = some (.bits w)) :
    ∃ x, t.regs r = some (.bits w x) := ht r _ h

theorem typed_nz {r w} (ht : Typed env t) (h : env.lookup r = some (.nz w)) :
    ∃ x, t.regs r = some (.bits w x) ∧ x.toNat % 2 ^ w ≠ 0 := ht r _ h

theorem typed_pred {r} (ht : Typed env t) (h : env.lookup r = some .pred) :
    ∃ b, t.regs r = some (.pred b) := ht r _ h

theorem readBits_rb {o : Opnd} (h : rb env o = true) (ht : Typed env t) (w : Nat) :
    ∃ x, readBits L g t w o = .ok x := by
  cases o with
  | reg r =>
    simp only [rb] at h
    cases hl : env.lookup r with
    | none => simp [hl] at h
    | some tg =>
      cases tg
      · obtain ⟨x, hx⟩ := typed_bits ht hl
        exact ⟨truncBits w x, by simp [readBits, readReg, hx, pure, Except.pure, bind, Except.bind]⟩
      · obtain ⟨x, hx, -⟩ := typed_nz ht hl
        exact ⟨truncBits w x, by simp [readBits, readReg, hx, pure, Except.pure, bind, Except.bind]⟩
      · simp [hl] at h
  | imm v => exact ⟨_, rfl⟩
  | _ => simp [rb] at h

theorem readValue_rw {o : Opnd} {w : Nat} (h : rw env w o = true) (ht : Typed env t) :
    ∃ x, readValue L g t w o = .ok (.bits w x) := by
  cases o with
  | reg r =>
    simp only [rw] at h
    cases hl : env.lookup r with
    | none => simp [hl] at h
    | some tg =>
      cases tg <;> simp only [hl, beq_iff_eq] at h
      · subst h
        obtain ⟨x, hx⟩ := typed_bits ht hl
        exact ⟨x, by simp [readValue, readReg, hx, pure, Except.pure]⟩
      · subst h
        obtain ⟨x, hx, -⟩ := typed_nz ht hl
        exact ⟨x, by simp [readValue, readReg, hx, pure, Except.pure]⟩
      · simp at h
  | imm v => exact ⟨_, rfl⟩
  | _ => simp [rw] at h

theorem readValue_rb {o : Opnd} (h : rb env o = true) (ht : Typed env t) (w : Nat) :
    ∃ v x, readValue L g t w o = .ok (.bits v x) := by
  cases o with
  | reg r =>
    simp only [rb] at h
    cases hl : env.lookup r with
    | none => simp [hl] at h
    | some tg =>
      cases tg with
      | bits v =>
        obtain ⟨x, hx⟩ := typed_bits ht hl
        exact ⟨v, x, by simp [readValue, readReg, hx, pure, Except.pure]⟩
      | nz v =>
        obtain ⟨x, hx, -⟩ := typed_nz ht hl
        exact ⟨v, x, by simp [readValue, readReg, hx, pure, Except.pure]⟩
      | pred => simp [hl] at h
  | imm v => exact ⟨_, _, rfl⟩
  | _ => simp [rb] at h

theorem readPred_rp {o : Opnd} (h : rp env o = true) (ht : Typed env t) :
    ∃ b, readPred L g t o = .ok b := by
  cases o <;> simp only [rp, Bool.false_eq_true] at h
  rename_i r
  obtain ⟨b, hb⟩ := typed_pred ht (by simpa using h)
  exact ⟨b, by simp [readPred, readReg, hb, pure, Except.pure, bind, Except.bind]⟩


/-! ### Integer instructions -/

/-- The destination and tag of a plain integer instruction on tagged registers. -/
def absInt (env : Env) (i : IntInstr) : Option (Nat × Tag) :=
  match i.op, i.ty, i.sat, i.dsts, i.srcs with
  | .add, .int _ w, false, [some d], [a, b] | .sub, .int _ w, false, [some d], [a, b]
  | .mul .lo, .int _ w, false, [some d], [a, b] | .mul .hi, .int _ w, false, [some d], [a, b]
  | .min false, .int _ w, false, [some d], [a, b] | .max false, .int _ w, false, [some d], [a, b]
  | .shl, .int _ w, false, [some d], [a, b] | .shr, .int _ w, false, [some d], [a, b] =>
    if i.rule == some .threadInt && rb env a && rb env b then some (d, .bits w) else none
  | .and, .int _ w, false, [some d], [a, b] | .or, .int _ w, false, [some d], [a, b]
  | .xor, .int _ w, false, [some d], [a, b] =>
    if i.rule == some .threadInt && w != 1 && rb env a && rb env b then some (d, .bits w)
    else none
  | .mul .wide, .int _ w, false, [some d], [a, b] =>
    if i.rule == some .threadInt && rb env a && rb env b then some (d, .bits (2 * w)) else none
  | .mad .lo, .int _ w, false, [some d], [a, b, c] =>
    if i.rule == some .threadInt && rb env a && rb env b && rb env c then some (d, .bits w)
    else none
  | .neg, .int _ w, false, [some d], [a] =>
    if i.rule == some .threadInt && rb env a then some (d, .bits w) else none
  | .setp _ none, .int _ _, false, [some d], [a, b] =>
    if i.rule == some .threadInt && rb env a && rb env b then some (d, .pred) else none
  | .and, .pred, false, [some d], [a, b] | .or, .pred, false, [some d], [a, b]
  | .xor, .pred, false, [some d], [a, b] =>
    if i.rule == some .threadInt && rp env a && rp env b then some (d, .pred) else none
  | .div, .int .u w, false, [some d], [a, b] =>
    if i.rule == some .threadInt && rb env a && rz env w b then some (d, .bits w) else none
  | .selp, .int _ w, false, [some d], [a, b, .reg p] =>
    if i.rule == some .threadMove && rw env w a && rw env w b && rp env (.reg p) then
      some (d, .bits w)
    else none
  | _, _, _, _, _ => none

theorem fin_bits {i : IntInstr} {d w : Nat} (hr : i.rule = some .threadInt)
    (h : ∃ r, execInt L g t i = .ok (next (setReg t d (.bits w r)))) :
    ∃ v, execLocal L g t (.int i) = .ok (next (setReg t d v)) ∧ (Tag.bits w).ok (some v) :=
  have ⟨r, h⟩ := h
  ⟨_, by rw [execLocal_int hr]; exact h, r, rfl⟩

theorem truncBits_toNat {w : Nat} {x : BitVec 64} : (truncBits w x).toNat = x.toNat % 2 ^ w := by
  have hx := x.isLt
  simp only [truncBits, BitVec.toNat_ofNat]
  rcases Nat.le_total (2 ^ w) (2 ^ 64) with hp | hp
  · exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hp)
  · exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) hx)

theorem intDiv_u {w : Nat} {x y : BitVec 64} (h : y.toNat % 2 ^ w ≠ 0) :
    ∃ q, intDiv .u w x y = .ok q := by
  have hx : intOf .u w x = ((x.toNat % 2 ^ w : Nat) : Int) := by simp [intOf]
  have hy : intOf .u w y = ((y.toNat % 2 ^ w : Nat) : Int) := by simp [intOf]
  have h0 : ¬ (((y.toNat % 2 ^ w : Nat) : Int) = 0) := by exact_mod_cast h
  have h1 : ¬ (((y.toNat % 2 ^ w : Nat) : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
  have h2 : ¬ (((x.toNat % 2 ^ w : Nat) : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
  simp only [intDiv, hx, hy, h0, h1, h2, bind, Except.bind, pure, Except.pure]
  simp

set_option hygiene false in
local macro "abs_open" : tactic => `(tactic| (
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc))

set_option hygiene false in
local macro "abs_run" : tactic => `(tactic| (
  simp [execInt, hx, hy, DType.width, bind, Except.bind, pure, Except.pure]
  try (split <;> exact ⟨_, rfl⟩)
  try exact ⟨_, rfl⟩))

set_option hygiene false in
local macro "abs_run1" : tactic => `(tactic| (
  simp [execInt, hx, hy, h1, DType.width, bind, Except.bind, pure, Except.pure]
  try exact ⟨_, rfl⟩))

theorem fin_pred {i : IntInstr} {d : Nat} (hr : i.rule = some .threadInt)
    (h : ∃ r, execInt L g t i = .ok (next (setReg t d (.pred r)))) :
    ∃ v, execLocal L g t (.int i) = .ok (next (setReg t d v)) ∧ Tag.pred.ok (some v) :=
  have ⟨r, h⟩ := h
  ⟨_, by rw [execLocal_int hr]; exact h, r, rfl⟩

theorem exec_of_absInt {i : IntInstr} {d : Nat} {tg : Tag} (h : absInt env i = some (d, tg))
    (ht : Typed env t) :
    ∃ v, execLocal L g t (.int i) = .ok (next (setReg t d v)) ∧ tg.ok (some v) := by
  rcases i with ⟨op, ty, sat, dsts, srcs⟩
  unfold absInt at h
  simp only at h
  split at h
  all_goals try (simp only [reduceCtorEq] at h)
  case h_1 =>
    rename_i k w d' a b
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    obtain ⟨v1, x1, h1⟩ := readValue_rb (L := L) (g := g) ha ht w
    obtain ⟨v2, x2, h2⟩ := readValue_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    simp [execInt, h1, h2, hx, hy, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  case h_2 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    obtain ⟨v1, x1, h1⟩ := readValue_rb (L := L) (g := g) ha ht w
    refine fin_bits hr ?_
    abs_run1
  case h_3 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    abs_run
  case h_4 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    abs_run
  case h_5 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    abs_run
  case h_6 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    abs_run
  case h_7 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht 32
    refine fin_bits hr ?_
    abs_run
  case h_8 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht 32
    refine fin_bits hr ?_
    abs_run
  case h_9 | h_10 | h_11 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨⟨hr, hw⟩, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    simp [execInt, hx, hy, hw, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  case h_12 =>
    rename_i k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_bits hr ?_
    abs_run
  case h_13 =>
    rename_i k w d' a b c
    abs_open
    obtain ⟨⟨⟨hr, ha⟩, hb⟩, hc⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    obtain ⟨z, hz⟩ := readBits_rb (L := L) (g := g) hc ht w
    refine fin_bits hr ?_
    simp [execInt, hx, hy, hz, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  case h_14 =>
    rename_i k w d' a
    abs_open
    obtain ⟨hr, ha⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    refine fin_bits hr ?_
    simp [execInt, hx, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  case h_15 =>
    rename_i c k w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    obtain ⟨y, hy⟩ := readBits_rb (L := L) (g := g) hb ht w
    refine fin_pred hr ⟨compare c ((DType.int k w).kind?.getD IType.b) w x y, ?_⟩
    simp [execInt, hx, hy, DType.width, bind, Except.bind, pure, Except.pure]

  case h_16 | h_17 | h_18 =>
    rename_i d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    obtain ⟨x, hx⟩ := readPred_rp (L := L) (g := g) ha ht
    obtain ⟨y, hy⟩ := readPred_rp (L := L) (g := g) hb ht
    refine fin_pred hr ?_
    simp [execInt, hx, hy, DType.width, bind, Except.bind, pure, Except.pure]
    first
      | (cases h : (x && y) <;> simp)
      | (cases h : (x || y) <;> simp)
      | (cases h : (x ^^ y) <;> simp)
  case h_19 =>
    rename_i w d' a b
    abs_open
    obtain ⟨⟨hr, ha⟩, hz⟩ := hc
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht w
    cases b <;> simp only [rz, beq_iff_eq, Bool.false_eq_true] at hz
    rename_i rb'
    obtain ⟨y0, hy0, hnz⟩ := typed_nz ht hz
    have hy : readBits L g t w (.reg rb') = .ok (truncBits w y0) := by
      simp [readBits, readReg, hy0, bind, Except.bind, pure, Except.pure]
    obtain ⟨q, hq⟩ := intDiv_u (w := w) (x := x) (y := truncBits w y0)
      (by rw [truncBits_toNat, Nat.mod_mod]; exact hnz)
    refine fin_bits hr ?_
    simp [execInt, intResult, hx, hy, hq, DType.intLanes?, DType.width, bind, Except.bind, pure,
      Except.pure]
    exact ⟨_, rfl⟩
  case h_20 =>
    rename_i k w d' a b p
    abs_open
    obtain ⟨⟨⟨hr, ha⟩, hb⟩, hp⟩ := hc
    obtain ⟨x, hx⟩ := readValue_rw (L := L) (g := g) ha ht
    obtain ⟨y, hy⟩ := readValue_rw (L := L) (g := g) hb ht
    obtain ⟨q, hq⟩ := typed_pred ht (by simpa [rp] using hp)
    refine ⟨.bits w (if q then x else y), ?_, _, rfl⟩
    rw [execLocal_selp hr]
    cases q <;>
      simp [execMove, readReg, hx, hy, hq, Value.bytes, DType.width, bind, Except.bind, pure,
        Except.pure]

/-! ### Moves, conversions, and the step -/

/-- The destination and tag of a scalar move of a value of `w` bits. -/
def absMove (env : Env) (m : MoveInstr) : Option (Nat × Tag) :=
  match m.kind, m.ty, m.dsts, m.srcs with
  | .scalar, .int _ w, [some d], [a] =>
    if m.rule == some .threadMove && rw env w a then some (d, .bits w) else none
  | _, _, _, _ => none

/-- The destination and tag of an integer conversion of a bit pattern. -/
def absCvt (env : Env) (c : CvtInstr) : Option (Nat × Tag) :=
  match c.dst, c.src, c.srcs, c.ext with
  | .int _ dw, .int _ _, [a], .same =>
    if c.rule == some .threadCvt && rb env a then some (c.d, .bits dw) else none
  | _, _, _, _ => none

/-- The destination and tag of an instruction that cannot fail on tagged registers. -/
def absOp (env : Env) : Op → Option (Nat × Tag)
  | .int i => absInt env i
  | .move m => absMove env m
  | .cvt c => absCvt env c
  | _ => none

theorem exec_of_absMove {m : MoveInstr} {d : Nat} {tg : Tag} (h : absMove env m = some (d, tg))
    (ht : Typed env t) :
    ∃ v, execLocal L g t (.move m) = .ok (next (setReg t d v)) ∧ tg.ok (some v) := by
  rcases m with ⟨kind, ty, dsts, srcs⟩
  unfold absMove at h
  simp only at h
  split at h
  · rename_i k w d' a
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hr, ha⟩ := hc
    obtain ⟨x, hx⟩ := readValue_rw (L := L) (g := g) ha ht
    refine ⟨.bits w x, ?_, x, rfl⟩
    rw [execLocal_move hr]
    simp [execMove, hx, Value.bytes, DType.width, bind, Except.bind, pure, Except.pure]
  · simp at h

theorem exec_of_absCvt {c : CvtInstr} {d : Nat} {tg : Tag} (h : absCvt env c = some (d, tg))
    (ht : Typed env t) :
    ∃ v, execLocal L g t (.cvt c) = .ok (next (setReg t d v)) ∧ tg.ok (some v) := by
  rcases c with ⟨dst, src, rnd, ftz, sat, relu, satfinite, pzo, scaled, pack, d', ext, srcs⟩
  unfold absCvt at h
  simp only at h
  split at h
  · rename_i dk dw sk sw a
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hr, ha⟩ := hc
    obtain ⟨v1, x1, h1⟩ := readValue_rb (L := L) (g := g) ha ht sw
    obtain ⟨x, hx⟩ := readBits_rb (L := L) (g := g) ha ht sw
    rw [execLocal_cvt hr]
    unfold execCvt
    simp only [h1, hx, bind, Except.bind, pure, Except.pure]
    split
    · exact ⟨_, rfl, _, rfl⟩
    · exact ⟨_, rfl, _, rfl⟩
  · simp at h

theorem exec_of_abs {op : Op} {d : Nat} {tg : Tag} (h : absOp env op = some (d, tg))
    (ht : Typed env t) :
    ∃ v, execLocal L g t op = .ok (next (setReg t d v)) ∧ tg.ok (some v) := by
  cases op <;> simp only [absOp, reduceCtorEq] at h
  · exact exec_of_absInt h ht
  · exact exec_of_absMove h ht
  · exact exec_of_absCvt h ht

theorem dsts_of_absInt {i : IntInstr} {d : Nat} {tg : Tag} (h : absInt env i = some (d, tg)) :
    i.dsts = [some d] := by
  rcases i with ⟨op, ty, sat, dsts, srcs⟩
  unfold absInt at h
  simp only at h
  split at h <;>
    first
      | (simp only [reduceCtorEq] at h)
      | (split_ifs at h with hc
         simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, -⟩ := h
         rfl)

theorem writes_of_abs {op : Op} {d : Nat} {tg : Tag} (h : absOp env op = some (d, tg)) :
    writesRegs op = [d] := by
  cases op <;> simp only [absOp, reduceCtorEq] at h
  · simp [writesRegs, dsts_of_absInt h]
  · rename_i m
    rcases m with ⟨kind, ty, dsts, srcs⟩
    unfold absMove at h
    simp only at h
    split at h
    · split_ifs at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
    · simp at h
  · rename_i c
    unfold absCvt at h
    split at h
    · split_ifs at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
    · simp at h

/-- The state after the instruction has the registers' tags, with the destination's. -/
theorem typed_set {d : Nat} {tg : Tag} {v : Value} (ht : Typed env t) (hv : tg.ok (some v)) :
    Typed ((d, tg) :: env) (next (setReg t d v)) := by
  intro r tg' h
  by_cases hr : r = d
  · subst hr
    simp [List.lookup] at h
    subst h
    simpa [next, setReg] using hv
  · have h' : env.lookup r = some tg' := by
      have hb : (r == d) = false := by simpa using hr
      simpa only [List.lookup, hb] using h
    simpa [next, setReg, Function.update_of_ne hr] using ht r tg' h'

end PTX.Flow.Tagged
