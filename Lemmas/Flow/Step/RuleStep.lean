-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.FloatOutcome
public import Lemmas.Flow.MaxCore
public import Lemmas.Flow.Widen
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.FloatWord
public import Lemmas.Flow.Lg2Core
public meta import Lean

@[expose] public section

/-! # Local steps that a kernel assumption gives a rule

A proof tool for `seg_sym`: one local instruction whose step is the rule of an assumption of the
kernel's list (exact real arithmetic for floating instructions, `idealReal`; the exact function of
an approximate instruction, `approxExact`; or a kernel's own rule, such as a logarithm), on
operands that the facts give. Nothing here is specific to a kernel.

* `Seg.rule1`: such a step as a piece of a segment, `pc → pc + 1`, writing one register.
* `rule_step`'s evaluation (`ruleStepProof`): the first assumption of the list whose rule
  selects the instruction (found by evaluation; the ones before it give no rule), then its rule
  evaluated by `simp` with the operands' facts and the lemmas below: exact real operations on
  finite numbers are their real results (`mulEReal_coe`, `erealValue_coe`, …), a 32-bit constant
  reads as its rational number (`readEReal_bits32`), and a condition of the rule is decided by
  the facts of the reals in context (a case split's hypothesis, say).

Reals are kept as the operations the code performs (`x * y`, `x⁻¹`); comparisons as
`erealCompare` of the reals; a constant as its real number (`1`, `3 / 2`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-! ### The selected rule -/

theorem execLocalRule_cons_none {a : Assumption} {t : TState} {op : Op} {e : Exec TState}
    (ha : a.localRule L g t op = none) (h : execLocalRule A L g t op = e) :
    execLocalRule (a :: A) L g t op = e := by
  unfold execLocalRule at h ⊢
  simp only [List.findSome?_cons, ha]
  exact h

theorem execLocalRule_cons_some {a : Assumption} {t : TState} {op : Op} {e : Exec TState}
    (ha : a.localRule L g t op = some e) : execLocalRule (a :: A) L g t op = e := by
  unfold execLocalRule
  simp only [List.findSome?_cons, ha]

/-- **A local step that writes one register**, as a piece of a segment: its step from every state
with the facts `F` (`hex`, at the state's registers `R` and call frame `cf`). -/
theorem Seg.rule1 {pc d : Nat} {op : Op} {F : List (Nat × Value)} {v : Value}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ R cf, Holds R F → execLocalA A L g ⟨pc, R, cf, 0, [], none⟩ op =
      .ok (PTX.next (setReg ⟨pc, R, cf, 0, [], none⟩ d v)))
    (hd : ∀ r ∈ F, r.1 ≠ d) :
    ∃ n, Seg K A L g n pc F (pc + 1) ((d, v) :: F) := by
  refine ⟨1, fun t h => ⟨_, ?_, At.set h hd⟩⟩
  obtain ⟨tpc, R, cf, sub, acc, fault⟩ := t
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4
  exact run_local hc hl ⟨rfl, rfl, rfl, rfl, h5⟩ (hex R cf h5)

/-! ### Exact real operations on finite numbers -/

theorem bindRead_some_ok {α β : Type} (a : α) (k : α → Option (Exec β)) :
    bindRead (some (.ok a)) k = k a := rfl

theorem bindRead_some_error {α β : Type} (e : Fault) (k : α → Option (Exec β)) :
    bindRead (some (.error e)) k = some (.error e) := rfl

theorem readEReal_float_self (fmt : FloatFmt) (x : ℝ) :
    readEReal fmt (.float fmt x) = some (.ok (x : EReal)) := by
  simp [readEReal, pure, Except.pure]

theorem pairRead_float (x y : ℝ) :
    pairRead (.pair (.float .f32 x) (.float .f32 y)) = some (.ok ((x : EReal), (y : EReal))) := by
  simp [pairRead, splitValue, readEReal_float_self, pure, Except.pure]

theorem joinValue_float (f f' : FloatFmt) (x y : ℝ) :
    joinValue (.float f x) (.float f' y) = .pair (.float f x) (.float f' y) := rfl

/-- A register operand reads as its value (`readERealOpnd_reg` at a state given by its fields). -/
theorem readERealOpnd_regs {pc : Nat} {R : Nat → Option Value} {cf : Option Bool} {sub : Nat}
    {acc : List Value} {f : Option Fault} {fmt : FloatFmt} {r : Nat} {v : Value}
    (h : R r = some v) :
    readERealOpnd ⟨pc, R, cf, sub, acc, f⟩ fmt (.reg r) = readEReal fmt v :=
  readERealOpnd_reg (t := ⟨pc, R, cf, sub, acc, f⟩) h

theorem readERealPair_regs {pc : Nat} {R : Nat → Option Value} {cf : Option Bool} {sub : Nat}
    {acc : List Value} {f : Option Fault} {r : Nat} {v : Value} (h : R r = some v) :
    readERealPair L g ⟨pc, R, cf, sub, acc, f⟩ (.reg r) = pairRead v :=
  readERealPair_reg_val (t := ⟨pc, R, cf, sub, acc, f⟩) h

/-- A register operand whose value reads as `e` (a conditional value, say) reads as `e`. -/
theorem readERealOpnd_regs_read {pc : Nat} {R : Nat → Option Value} {cf : Option Bool}
    {sub : Nat} {acc : List Value} {f : Option Fault} {fmt : FloatFmt} {r : Nat} {v : Value}
    {e : EReal} (h : R r = some v) (hv : readEReal fmt v = some (.ok e)) :
    readERealOpnd ⟨pc, R, cf, sub, acc, f⟩ fmt (.reg r) = some (.ok e) := by
  rw [readERealOpnd_regs h, hv]

theorem readERealOpnd_regs_float {pc : Nat} {R : Nat → Option Value} {cf : Option Bool}
    {sub : Nat} {acc : List Value} {f : Option Fault} {fmt : FloatFmt} {r : Nat} {x : ℝ}
    (h : R r = some (.float fmt x)) :
    readERealOpnd ⟨pc, R, cf, sub, acc, f⟩ fmt (.reg r) = some (.ok (x : EReal)) := by
  rw [readERealOpnd_regs h, readEReal_float_self]

theorem readERealPair_regs_float {pc : Nat} {R : Nat → Option Value} {cf : Option Bool}
    {sub : Nat} {acc : List Value} {f : Option Fault} {r : Nat} {x y : ℝ}
    (h : R r = some (.pair (.float .f32 x) (.float .f32 y))) :
    readERealPair L g ⟨pc, R, cf, sub, acc, f⟩ (.reg r) = some (.ok ((x : EReal),
      (y : EReal))) := by
  rw [readERealPair_regs h, pairRead_float]

theorem readERealOpnd_f32imm (t : TState) (fmt : FloatFmt) (b : Nat) :
    readERealOpnd t fmt (.f32imm b) = readEReal fmt (.bits 32 (BitVec.ofNat 64 b)) := rfl

theorem addEReal_coe_neg (x y : ℝ) :
    addEReal (x : EReal) (-(y : EReal)) = some ((x - y : ℝ) : EReal) := by
  rw [← EReal.coe_neg, addEReal_coe, sub_eq_add_neg]

theorem neg_coe_ereal (x : ℝ) : -(x : EReal) = ((-x : ℝ) : EReal) := (EReal.coe_neg x).symm

theorem coe_min_ereal {x y : ℝ} : min (x : EReal) (y : EReal) = ((min x y : ℝ) : EReal) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (EReal.coe_le_coe h)]
  · rw [min_eq_right h, min_eq_right (EReal.coe_le_coe h)]

theorem ereal_coe_eq_top_or_bot (x : ℝ) : ((x : EReal) = ⊤ ∨ (x : EReal) = ⊥) = False := by
  simp

/-- The comparisons of two reals as extended reals, as comparisons of the reals. -/
theorem erealCompare_coe_eq (x y : ℝ) : erealCompare .eq (x : EReal) y = decide (x = y) := by
  simp [erealCompare]
theorem erealCompare_coe_ne (x y : ℝ) : erealCompare .ne (x : EReal) y = decide (x ≠ y) := by
  simp [erealCompare]
theorem erealCompare_coe_lt (x y : ℝ) : erealCompare .lt (x : EReal) y = decide (x < y) := by
  simp [erealCompare]
theorem erealCompare_coe_lo (x y : ℝ) : erealCompare .lo (x : EReal) y = decide (x < y) := by
  simp [erealCompare]
theorem erealCompare_coe_le (x y : ℝ) : erealCompare .le (x : EReal) y = decide (x ≤ y) := by
  simp [erealCompare]
theorem erealCompare_coe_ls (x y : ℝ) : erealCompare .ls (x : EReal) y = decide (x ≤ y) := by
  simp [erealCompare]
theorem erealCompare_coe_gt (x y : ℝ) : erealCompare .gt (x : EReal) y = decide (y < x) := by
  simp [erealCompare]
theorem erealCompare_coe_hi (x y : ℝ) : erealCompare .hi (x : EReal) y = decide (y < x) := by
  simp [erealCompare]
theorem erealCompare_coe_ge (x y : ℝ) : erealCompare .ge (x : EReal) y = decide (y ≤ x) := by
  simp [erealCompare]
theorem erealCompare_coe_hs (x y : ℝ) : erealCompare .hs (x : EReal) y = decide (y ≤ x) := by
  simp [erealCompare]

/-- **A 32-bit constant** that encodes the rational `q` reads as `q` (the two side conditions are
decided by evaluation). -/
theorem readEReal_bits32 {x : BitVec 64} (n : Nat) (q : ℚ) (hx : x = BitVec.ofNat 64 n)
    (hb : n < 2 ^ 64) (hq : f32Value n = some q) :
    readEReal .f32 (.bits 32 x) = some (.ok (((q : ℝ)) : EReal)) := by
  subst hx
  exact readEReal_of_valFloat (valFloat_b32 hb hq)

/-- A conditional value reads as the conditional of its two readings. -/
theorem readEReal_ite {fmt : FloatFmt} {p : Prop} [Decidable p] {va vb : Value} {a b : EReal}
    (ha : readEReal fmt va = some (.ok a)) (hb : readEReal fmt vb = some (.ok b)) :
    readEReal fmt (if p then va else vb) = some (.ok (if p then a else b)) := by
  split <;> assumption

/-- A pair of two values that read as extended reals reads as the pair of them. -/
theorem pairRead_pair {a b : Value} {x y : EReal} (ha : readEReal .f32 a = some (.ok x))
    (hb : readEReal .f32 b = some (.ok y)) :
    pairRead (.pair a b) = some (.ok (x, y)) := by
  simp [pairRead, splitValue, ha, hb, pure, Except.pure]

/-- The join of two values that read as extended reals reads as the pair of them (when neither
is a bit vector or a slice, the join is their pair; two bit vectors would merge). -/
theorem pairRead_join {a b : Value} {x y : EReal} (hj : joinValue a b = .pair a b)
    (ha : readEReal .f32 a = some (.ok x)) (hb : readEReal .f32 b = some (.ok y)) :
    pairRead (joinValue a b) = some (.ok (x, y)) := by
  rw [hj]; exact pairRead_pair ha hb

/-- A register operand whose value is a pair that reads as `(x, y)` reads as that pair. -/
theorem readERealPair_regs_read {pc : Nat} {R : Nat → Option Value} {cf : Option Bool}
    {sub : Nat} {acc : List Value} {f : Option Fault} {r : Nat} {v : Value} {x y : EReal}
    (h : R r = some v) (hv : pairRead v = some (.ok (x, y))) :
    readERealPair L g ⟨pc, R, cf, sub, acc, f⟩ (.reg r) = some (.ok (x, y)) := by
  rw [readERealPair_regs h, hv]

/-- The value an ideal rule writes for an extended real reads as that extended real. -/
theorem readEReal_erealValue_f32 (e : EReal) :
    readEReal .f32 (erealValue .f32 e) = some (.ok e) := by
  unfold erealValue
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rfl
  · simp only [readEReal, ite_true, pure, Except.pure, EReal.coe_toReal h1 h2]

/-- Exact operations with an infinite operand and a finite one: the infinity, its sign by the
finite operand's for a product (a zero has no rule). -/
theorem mulEReal_bot_pos {y : ℝ} (hy : 0 < y) : mulEReal ⊥ (y : EReal) = some ⊥ := by
  simp [mulEReal, hy.ne', EReal.bot_mul_coe_of_pos hy]
theorem mulEReal_bot_neg {y : ℝ} (hy : y < 0) : mulEReal ⊥ (y : EReal) = some ⊤ := by
  simp [mulEReal, hy.ne, EReal.bot_mul_coe_of_neg hy]
theorem mulEReal_top_pos {y : ℝ} (hy : 0 < y) : mulEReal ⊤ (y : EReal) = some ⊤ := by
  simp [mulEReal, hy.ne', EReal.top_mul_coe_of_pos hy]
theorem mulEReal_top_neg {y : ℝ} (hy : y < 0) : mulEReal ⊤ (y : EReal) = some ⊥ := by
  simp [mulEReal, hy.ne, EReal.top_mul_coe_of_neg hy]
theorem addEReal_bot_coe (y : ℝ) : addEReal ⊥ (y : EReal) = some ⊥ := by
  simp [addEReal]
theorem addEReal_top_coe (y : ℝ) : addEReal ⊤ (y : EReal) = some ⊤ := by
  simp [addEReal]
theorem addEReal_coe_bot (y : ℝ) : addEReal (y : EReal) ⊥ = some ⊥ := by
  simp [addEReal]
theorem addEReal_coe_top (y : ℝ) : addEReal (y : EReal) ⊤ = some ⊤ := by
  simp [addEReal]
/-- A real plus `-∞` (an `fma` whose addend is `-∞`, as Core's `lg2` of a zero row sum gives) is
`-∞`; likewise `+∞`. -/
theorem coe_add_bot (y : ℝ) : (y : EReal) + ⊥ = ⊥ := EReal.add_bot _
theorem coe_add_top (y : ℝ) : (y : EReal) + ⊤ = ⊤ := EReal.coe_add_top y
/-- The `f32` value of an infinity: its bits (the literal `readEReal_f32_ninf` reads back). -/
theorem erealValue_f32_bot : erealValue .f32 ⊥ = .bits 32 (BitVec.ofNat 64 4286578688) := by
  simp [erealValue]; rfl
theorem erealValue_f32_top : erealValue .f32 ⊤ = .bits 32 (BitVec.ofNat 64 2139095040) := by
  simp [erealValue]; rfl

/-- A fact by its position in an explicit list (checked by evaluating the lookup). -/
theorem mem_idx {l : List (Nat × Value)} {a : Nat × Value} (i : Nat) (h : l[i]? = some a) :
    a ∈ l :=
  List.mem_of_getElem? h

/-- The 32-bit patterns of the two infinities. -/
theorem readEReal_f32_ninf :
    readEReal .f32 (.bits 32 (BitVec.ofNat 64 4286578688)) = some (.ok ⊥) := rfl
theorem readEReal_f32_pinf :
    readEReal .f32 (.bits 32 (BitVec.ofNat 64 2139095040)) = some (.ok ⊤) := rfl

end

/-! ### Evaluation of the selected rule -/

open Lean Meta Elab Tactic

/-- The fact of register `r` in a fact list `F` (explicit facts, appends, the table part
`factsFrom live v`, definitions unfolded): a proof of `(r, x) ∈ F'` for the form `F'` reached,
and the value `x`, by position. -/
meta partial def factMemPos (F : Expr) (r : Nat) : MetaM (Option (Expr × Expr × Expr)) := do
  let F ← whnfR (← instantiateMVars F)
  if F.isAppOfArity ``List.cons 3 then
    let α := F.getArg! 0
    let u ← getDecLevel α
    let hd := F.getArg! 1
    let tl := F.getArg! 2
    let hd' ← whnfR hd
    if hd'.isAppOfArity ``Prod.mk 4 then
      if regLit? (← whnfD (hd'.getArg! 2)) == some r then
        return some (mkApp3 (mkConst ``List.Mem.head [u]) α hd tl, hd'.getArg! 3, hd)
    let some (pf, v, e) ← factMemPos tl r | return none
    return some (mkApp5 (mkConst ``List.Mem.tail [u]) α e hd tl pf, v, e)
  if F.isAppOfArity ``PTX.Flow.factsFrom 2 then
    let live := F.getArg! 0
    let ls ← regList live
    unless ls.contains r do return none
    let val := F.getArg! 1
    let hl ← mkExpectedTypeHint (← memProof r ls.toList)
      (← mkAppM ``Membership.mem #[live, mkNatLit r])
    let v := (mkApp val (mkNatLit r)).headBeta
    return some (mkApp4 (mkConst ``PTX.Flow.mem_factsFrom) live val (mkNatLit r) hl, v,
      ← mkAppM ``Prod.mk #[mkNatLit r, mkApp val (mkNatLit r)])
  if F.isAppOfArity ``HAppend.hAppend 6 then
    let (a, b) := (F.getArg! 4, F.getArg! 5)
    if let some (pf, v, e) ← factMemPos a r then
      return some (← mkAppM ``List.mem_append_left #[b, pf], v, e)
    if let some (pf, v, e) ← factMemPos b r then
      return some (← mkAppM ``List.mem_append_right #[a, pf], v, e)
    return none
  match ← unfoldDefinition? F with
  | some F' => factMemPos F'.headBeta r
  | none => return none

/-- `fact_mem_pos`: `(r, x) ∈ F` by the position of `r`'s fact in `F`, as a term the kernel checks
(no unification against the table): `x` is the fact's value (assigned when it is a hole; when it
is given, it must be the value as the table writes it, up to projections). -/
elab "fact_mem_pos" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``Membership.mem 5 do throwError "fact_mem_pos: not a membership"
  let F := ty.getArg! 3
  let p ← whnfR (ty.getArg! 4)
  unless p.isAppOfArity ``Prod.mk 4 do throwError "fact_mem_pos: not a fact"
  let some r := regLit? (← whnfD (p.getArg! 2)) | throwError "fact_mem_pos: not a register"
  let some (pf, v, _) ← factMemPos F r | throwError "fact_mem_pos: no fact of {r}"
  let x ← instantiateMVars (p.getArg! 3)
  if x.isMVar then
    unless ← isDefEq x v do throwError "fact_mem_pos: the value"
  else unless x == v || (← projNorm x) == (← projNorm (← evalTable v)) do
    throwError "fact_mem_pos: the value of {r} is not the fact's"
  goal.assign (← mkExpectedTypeHint (← instantiateMVars pf) ty)
  replaceMainGoal []

/-- A proof of `(r, v) ∈ F` for an explicit fact or a table fact, by position (`fact_mem_pos`),
else by searching the list. -/
macro "fact_mem" : tactic => `(tactic| first
  | fact_mem_pos
  | repeat' first
      | exact PTX.Flow.mem_factsFrom (by lit_mem)
      | exact List.mem_cons_self ..
      | apply List.mem_cons_of_mem)

/-- `sym_seg_free`: prove `SegFreePc A pc` for a literal `pc`: `seg_free_pc`, or a kernel's rule
(one that unfolds its assumption list, say). -/
syntax "sym_seg_free" : tactic
macro_rules | `(tactic| sym_seg_free) => `(tactic| seg_free_pc)


/-- The rational number an IEEE single-precision pattern encodes, as numerator and denominator
(lowest terms); `none` for an infinity or a NaN. -/
meta def f32Rat (n : Nat) : Option (Int × Nat) :=
  let sign := (n >>> 31) % 2
  let e := (n >>> 23) % 256
  let m := n % 8388608
  if e = 255 then none else
    let (mant, ex) : Nat × Int := if e = 0 then (m, -149) else (m + 8388608, (e : Int) - 150)
    let (num, den) : Nat × Nat :=
      if ex ≥ 0 then (mant * 2 ^ ex.toNat, 1) else (mant, 2 ^ (-ex).toNat)
    let gc := Nat.gcd num den
    let (num, den) := if gc = 0 then (0, 1) else (num / gc, den / gc)
    some (if sign = 1 then -(num : Int) else num, den)

/-- The rational literal `num / den` as a term of `ℚ`. -/
meta def ratLit (num : Int) (den : Nat) : MetaM Expr := do
  let q := mkConst ``Rat
  let natQ (k : Nat) : MetaM Expr := mkAppOptM ``OfNat.ofNat #[q, mkRawNatLit k, none]
  let absN ← natQ num.natAbs
  let base ← if den = 1 then pure absN else mkAppM ``HDiv.hDiv #[absN, ← natQ den]
  if num < 0 then mkAppM ``Neg.neg #[base] else pure base

/-- `readEReal .f32 (.bits 32 x)` for a literal `x` that encodes a finite number or an infinity:
the right side `some (.ok e)` of its equation, with the proof. -/
meta def readLit? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  unless e.isAppOfArity ``PTX.Assumption.readEReal 2 do return none
  unless (← whnfR (e.getArg! 0)).isConstOf ``PTX.FloatFmt.f32 do return none
  let v ← whnfR (e.getArg! 1)
  unless v.isAppOfArity ``PTX.Value.bits 2 do return none
  let w0 ← instantiateMVars (v.getArg! 0)
  let some w := w0.nat? <|> w0.rawNatLit? | return none
  unless w == 32 do return none
  let x := v.getArg! 1
  let some n ← (try some <$> natValue (← mkAppM ``BitVec.toNat #[x]) catch _ => pure none) |
    return none
  unless n < 2 ^ 32 do return none
  -- an infinity
  if n == 4286578688 || n == 2139095040 then
    let pf := mkConst (if n == 4286578688 then ``PTX.Flow.readEReal_f32_ninf
      else ``PTX.Flow.readEReal_f32_pinf)
    let some (_, _, r) := (← inferType pf).eq? | return none
    return some (r, ← mkExpectedTypeHint pf (← mkEq e r))
  let some (num, den) := f32Rat n | return none
  let q ← ratLit num den
  let hx ← mkEqRefl x
  let hb ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit n,
    ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]])
  let hq ← mkDecideProof (← mkEq (← mkAppM ``PTX.f32Value #[mkNatLit n])
    (← mkAppM ``Option.some #[q]))
  let pf ← mkAppOptM ``PTX.Flow.readEReal_bits32
    #[some x, some (mkNatLit n), some q, some hx, some hb, some hq]
  let ty ← inferType pf
  let some (_, _, rhs) := ty.eq? | return none
  return some (rhs, pf)

/-- `readEReal .f32 (.bits 32 x)` for a literal `x` that encodes a finite number or an infinity:
that extended real. -/
simproc_decl readEReal_lit (Assumption.readEReal _ _) := fun e => do
  let some (rhs, pf) ← readLit? e | return .continue
  return .done { expr := rhs, proof? := some pf }

/-- Whether `e` evaluates to the number `n`. -/
meta def isNum (e : Expr) (n : Nat) : MetaM Bool := do
  try return (← natValue e) == n catch _ => return false

/-- A proof of `s ≠ 0` from a hypothesis `s ≠ 0`, `0 < s` or `s < 0` in context. -/
meta def neZero? (s : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let h := decl.toExpr
    let tryE (pf : MetaM Expr) : MetaM (Option Expr) := do
      try
        let p ← pf
        let want ← mkAppM ``Ne #[s, ← mkAppOptM ``OfNat.ofNat #[← inferType s, mkRawNatLit 0, none]]
        if ← withNewMCtxDepth (isDefEq (← inferType p) want) then return some p else return none
      catch _ => return none
    if ty.isAppOfArity ``Ne 3 then
      if let some p ← tryE (pure h) then return some p
    if ty.isAppOfArity ``LT.lt 4 then
      if let some p ← tryE (mkAppM ``ne_of_gt #[h]) then return some p
      if let some p ← tryE (mkAppM ``ne_of_lt #[h]) then return some p
  return none

/-- A hypothesis in context that classifies the word `x` (of a value `.bits 32 x`) as a finite
`f32` datum `s`: `(proof of classify .f32 (.bits 32 x) = .ok (.fin s), s)`, from a hypothesis
`classify .f32 (.bits 32 x') = .ok (.fin s)` with `x'` the word `x`, or from `f32Value e = some s`
with `e` its number `x.toNat` and `s ≠ 0` (`neZero?`; `classify_word_f32`). -/
meta def wordHyp? (x : Expr) : MetaM (Option (Expr × Expr)) := do
  let n ← mkAppM ``BitVec.toNat #[x]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    if lhs.isAppOfArity ``PTX.classify 2 && rhs.isAppOfArity ``Except.ok 3 then
      let d ← whnfR (rhs.getArg! 2)
      unless d.isAppOfArity ``PTX.FVal.fin 1 do continue
      unless (← whnfR (lhs.getArg! 0)).isConstOf ``PTX.FloatFmt.f32 do continue
      let v ← whnfR (lhs.getArg! 1)
      unless v.isAppOfArity ``PTX.Value.bits 2 do continue
      unless ← isNum (v.getArg! 0) 32 do continue
      if ← withNewMCtxDepth (isDefEq (v.getArg! 1) x) then
        let want ← mkAppM ``PTX.classify #[mkConst ``PTX.FloatFmt.f32,
          ← mkAppM ``PTX.Value.bits #[mkNatLit 32, x]]
        let pf ← mkExpectedTypeHint decl.toExpr (← mkEq want rhs)
        return some (pf, d.appArg!)
    else if lhs.isAppOfArity ``PTX.f32Value 1 && rhs.isAppOfArity ``Option.some 2 then
      if ← withNewMCtxDepth (isDefEq lhs.appArg! n) then
        let s := rhs.getArg! 1
        let some hs ← neZero? s | continue
        let hx ← mkExpectedTypeHint decl.toExpr (← mkEq (← mkAppM ``PTX.f32Value #[n]) rhs)
        return some (← mkAppM ``PTX.Flow.classify_word_f32 #[hx, hs], s)
  return none

/-- A bound `x.toNat < 2 ^ 32` for the low word of a pack: `x` is `truncBits 32 y`
(`truncBits_toNat_lt`, a launch word say), or a hypothesis gives it. -/
meta def word32Bound? (x : Expr) : MetaM (Option Expr) := do
  let x' ← whnfR x
  if x'.isAppOfArity ``PTX.truncBits 2 then
    if ← isNum (x'.getArg! 0) 32 then
      return some (← mkAppM ``PTX.Flow.truncBits_toNat_lt #[x'.getArg! 0, x'.getArg! 1])
  let want ← mkAppM ``LT.lt #[← mkAppM ``BitVec.toNat #[x],
    ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 32]]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← withNewMCtxDepth (isDefEq decl.type want) then return some decl.toExpr
  return none

/-- A register value in the form the evaluation of a rule reads: abbreviations unfolded, and a
`joinValue` of two floating values as their pair (by definition). -/
meta def ruleValue (v : Expr) : MetaM Expr :=
  Meta.transform v (post := fun x => do
    let some c := x.getAppFn.constName? | return .done x
    if c == ``PTX.joinValue && x.getAppNumArgs == 2 then
      let lo ← whnfR (x.getArg! 0)
      let hi ← whnfR (x.getArg! 1)
      if lo.isAppOfArity ``PTX.Value.float 2 && hi.isAppOfArity ``PTX.Value.float 2 then
        return .done (mkApp2 (mkConst ``PTX.Value.pair) lo hi)
      return .done x
    if (← getEnv).isConstructor c then return .done x
    if (← isProjectionFn c) then return .done x
    if (← getReducibilityStatus c) == .reducible then
      let x' ← whnfR x
      if x' != x then return .visit x'
    return .done x)

/-- A reading of the `.f32` value `v` in the extended reals: `(e, proof of readEReal .f32 v =
some (.ok e))`, for a payload, an infinite or finite 32-bit constant, the value an ideal rule
wrote (`erealValue`), and a conditional of such values (a floating `selp` on a symbolic
predicate); `none` for any other value. -/
meta partial def erealRead? (v : Expr) : MetaM (Option (Expr × Expr)) := do
  let v ← whnfR v
  let out (pf : Expr) : MetaM (Option (Expr × Expr)) := do
    let ty ← instantiateMVars (← inferType pf)
    let some (_, _, rhs) := ty.eq? | return none
    let rhs ← whnfR rhs
    unless rhs.isAppOfArity ``Option.some 2 do return none
    let r ← whnfR (rhs.getArg! 1)
    unless r.isAppOfArity ``Except.ok 3 do return none
    return some (r.getArg! 2, pf)
  if v.isAppOfArity ``ite 5 then
    let some (a, pa) ← erealRead? (v.getArg! 3) | return none
    let some (b, pb) ← erealRead? (v.getArg! 4) | return none
    let fmt := mkConst ``PTX.FloatFmt.f32
    let pf := mkAppN (mkConst ``PTX.Flow.readEReal_ite)
      #[fmt, v.getArg! 1, v.getArg! 2, v.getArg! 3, v.getArg! 4, a, b, pa, pb]
    return ← out pf
  if v.isAppOfArity ``PTX.Value.float 2 then
    unless (← whnfR (v.getArg! 0)).isConstOf ``PTX.FloatFmt.f32 do return none
    return ← out (← mkAppM ``PTX.Flow.readEReal_float_self
      #[mkConst ``PTX.FloatFmt.f32, v.getArg! 1])
  if v.isAppOfArity ``PTX.Assumption.erealValue 2 then
    unless (← whnfR (v.getArg! 0)).isConstOf ``PTX.FloatFmt.f32 do return none
    return ← out (← mkAppM ``PTX.Flow.readEReal_erealValue_f32 #[v.getArg! 1])
  if v.isAppOfArity ``PTX.Value.bits 2 then
    let e ← mkAppM ``PTX.Assumption.readEReal #[mkConst ``PTX.FloatFmt.f32, v]
    if let some (_, pf) ← readLit? e then return ← out pf
    -- a symbolic word that a hypothesis classifies (`wordHyp?`)
    unless ← isNum (v.getArg! 0) 32 do return none
    let some (h, _) ← wordHyp? (v.getArg! 1) | return none
    return ← out (← mkAppM ``PTX.Flow.readEReal_bits_fin #[h])
  return none

/-- The reading of two 32-bit words `a`, `b` packed into one 64-bit word: the proof of
`pairRead v = some (.ok (x, y))` from `pairRead_bits_or` (`v = .bits 64 (a ||| b <<< 32)`) or
`pairRead_join_bits` (`v = joinValue (.bits 32 a) (.bits 32 b)`), with the words read by
`erealRead?` (a constant, or a word a hypothesis classifies) and the low word's bound by
`word32Bound?`. -/
meta def wordPairProof? (v : Expr) : MetaM (Option Expr) := do
  let is32 (w : Expr) : MetaM Bool := isNum w 32
  let words (a b : Expr) (lem : Name) : MetaM (Option Expr) := do
    let va ← mkAppM ``PTX.Value.bits #[mkNatLit 32, a]
    let vb ← mkAppM ``PTX.Value.bits #[mkNatLit 32, b]
    let some (_, pa) ← erealRead? va | return none
    let some (_, pb) ← erealRead? vb | return none
    let some hb ← word32Bound? a | return none
    return some (← mkAppM lem #[hb, pa, pb])
  if v.isAppOfArity ``PTX.joinValue 2 then
    let a ← whnfR (v.getArg! 0)
    let b ← whnfR (v.getArg! 1)
    unless a.isAppOfArity ``PTX.Value.bits 2 && b.isAppOfArity ``PTX.Value.bits 2 do return none
    unless (← is32 (a.getArg! 0)) && (← is32 (b.getArg! 0)) do return none
    return ← words (a.getArg! 1) (b.getArg! 1) ``PTX.Flow.pairRead_join_bits
  if v.isAppOfArity ``PTX.Value.bits 2 then
    unless ← isNum (v.getArg! 0) 64 do return none
    let z ← whnfR (v.getArg! 1)
    unless z.isAppOfArity ``HOr.hOr 6 do return none
    let sh ← whnfR (z.getArg! 5)
    unless sh.isAppOfArity ``HShiftLeft.hShiftLeft 6 do return none
    unless ← isNum (sh.getArg! 5) 32 do return none
    return ← words (z.getArg! 4) (sh.getArg! 4) ``PTX.Flow.pairRead_bits_or
  return none

/-- A reading of a pair value: `.pair a b`, or `joinValue a b` where `a` is a payload, a written
value or a conditional (not a bit vector, so the join is the pair), with `a`, `b` read by
`erealRead?`, or two packed words (`wordPairProof?`): the proof of
`pairRead v = some (.ok (x, y))`. -/
meta def pairReadProof? (v : Expr) : MetaM (Option Expr) := do
  let v ← whnfR v
  if let some pf ← wordPairProof? v then return some pf
  if v.isAppOfArity ``PTX.Value.pair 2 then
    let some (_, pa) ← erealRead? (v.getArg! 0) | return none
    let some (_, pb) ← erealRead? (v.getArg! 1) | return none
    return some (← mkAppM ``PTX.Flow.pairRead_pair #[pa, pb])
  if v.isAppOfArity ``PTX.joinValue 2 then
    let a ← whnfR (v.getArg! 0)
    if let some (_, pa) ← erealRead? a then
      if let some (_, pb) ← erealRead? (v.getArg! 1) then
        -- the join is the pair (by evaluation: neither two bit vectors nor two slices)
        let pr ← mkAppM ``PTX.Value.pair #[v.getArg! 0, v.getArg! 1]
        if ← withNewMCtxDepth (isDefEq v pr) then
          let hj ← mkExpectedTypeHint (← mkEqRefl pr) (← mkEq v pr)
          return some (← mkAppM ``PTX.Flow.pairRead_join #[hj, pa, pb])
  -- a closed 64-bit value (two merged constant halves, say): its halves' readings, checked by
  -- evaluation
  if v.hasFVar || v.hasMVar then return none
  let vw ← whnfD v
  unless vw.isAppOfArity ``PTX.Value.bits 2 do return none
  let some n ← (try some <$> natValue (← mkAppM ``BitVec.toNat #[vw.getArg! 1]) catch _ =>
    pure none) | return none
  let half (k : Nat) : MetaM (Option Expr) := do
    let hv ← mkAppM ``PTX.Value.bits #[mkRawNatLit 32, ← mkAppM ``BitVec.ofNat
      #[mkNatLit 64, mkNatLit k]]
    let some (r, _) ← readLit? (← mkAppM ``PTX.Assumption.readEReal
      #[mkConst ``PTX.FloatFmt.f32, hv]) | return none
    -- `r` is `some (.ok x)`
    let r ← whnfR r
    unless r.isAppOfArity ``Option.some 2 do return none
    let r1 ← whnfR (r.getArg! 1)
    unless r1.isAppOfArity ``Except.ok 3 do return none
    return some (r1.getArg! 2)
  let some x0 ← half (n % 2 ^ 32) | return none
  let some x1 ← half (n / 2 ^ 32 % 2 ^ 32) | return none
  let e ← mkAppM ``PTX.Flow.pairRead #[v]
  let rhs ← mkAppM ``Option.some #[← mkAppOptM ``Except.ok #[mkConst ``PTX.Fault, none,
    ← mkAppM ``Prod.mk #[x0, x1]]]
  let ty ← mkEq e rhs
  unless ← withNewMCtxDepth (isDefEq e rhs) do return none
  return some (← mkExpectedTypeHint (← mkEqRefl rhs) ty)

/-- Definitions the evaluation of a rule does not unfold: the operations on extended reals and
reals, the operand reads, and the state updates. -/
meta def ruleOpaque : List Name :=
  [``PTX.Assumption.mulEReal, ``PTX.Assumption.addEReal, ``PTX.Assumption.erealValue,
   ``PTX.Assumption.erealCompare, ``PTX.Assumption.readFinite, ``PTX.Assumption.readERealOpnd,
   ``PTX.Assumption.readERealPair, ``PTX.Assumption.readEReal, ``PTX.Assumption.bindRead,
   ``PTX.next, ``PTX.setReg]

/-- The rule of assumption `a` at the state `t` for `op`, unfolded up to the operations of
`ruleOpaque`: `none` when the assumption names no rule for `op`. -/
meta def ruleBody (a L g t op : Expr) : MetaM Expr := do
  let e ← mkAppM ``PTX.Assumption.localRule #[a, L, g, t, op]
  withCanUnfoldPred (fun _ ci => pure !(ruleOpaque.contains ci.name)) (whnfD e)

/-- Hypotheses in context about reals and comparisons of them, restated as facts about the reals
(`erealCompare` of two reals as the comparison, Booleans as propositions): what the evaluation of
a rule may use to decide its conditions. Returns the names of the restated hypotheses. -/
meta def realFacts : TacticM (Array Ident) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    -- register facts are not facts about reals
    if ty.isAppOf ``PTX.Proof.Holds then continue
    let mentions := (ty.find? fun e => e.isConstOf ``Real || e.isConstOf ``EReal ||
      e.isConstOf ``PTX.Assumption.erealCompare).isSome
    unless mentions do continue
    if ty.approxDepth.toNat > 40 then continue
    let n := mkIdent (← mkFreshUserName `hr)
    let saved ← saveState
    -- an equation with a numeral on the left (`0 = x`, a role's case split) is restated as
    -- `x = 0`: as a simp lemma it must rewrite the recorded real, not every numeral
    let flip := match ty.eq? with
      | some (_, a, _) => a.isAppOfArity ``OfNat.ofNat 3 || a.isRawNatLit
      | none => false
    try
      if flip then
        evalTactic (← `(tactic| have $n:ident := Eq.symm $(← Term.exprToSyntax d.toExpr)))
      else
        evalTactic (← `(tactic| have $n:ident := $(← Term.exprToSyntax d.toExpr)))
      evalTactic (← `(tactic| try simp only [PTX.Flow.erealCompare_coe_eq,
        PTX.Flow.erealCompare_coe_ne, PTX.Flow.erealCompare_coe_lt, PTX.Flow.erealCompare_coe_lo,
        PTX.Flow.erealCompare_coe_le, PTX.Flow.erealCompare_coe_ls, PTX.Flow.erealCompare_coe_gt,
        PTX.Flow.erealCompare_coe_hi, PTX.Flow.erealCompare_coe_ge, PTX.Flow.erealCompare_coe_hs,
        decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true, ne_eq, not_not] at $n:ident))
      out := out.push n
    catch _ => saved.restore
  return out

/-- `rule_simp`: a role's extension of `rule_step`'s simplification of a rule's body (lemmas about
its recorded values, say), run after the library's. By default it fails (and is skipped); a role
adds `scoped macro_rules | `(tactic| rule_simp) => `(tactic| simp only [...])`. -/
syntax "rule_simp" : tactic
macro_rules | `(tactic| rule_simp) => `(tactic| fail "rule_simp")

/-- Close `body = some (.ok (next (setReg t d ?v)))` (or prove `body = none`) by evaluating the
rule with the operand reads `reads` (terms) and the real facts `facts`. -/
meta def ruleSimp (reads : Array Term) (facts : Array Ident) : TacticM Unit := do
  let mut args : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for r in reads do args := args.push (← `(Lean.Parser.Tactic.simpLemma| $r:term))
  for f in facts do args := args.push (← `(Lean.Parser.Tactic.simpLemma| $f:ident))
  let base : Array Ident := #[``PTX.Flow.bindRead_some_ok, ``PTX.Flow.bindRead_some_error,
    ``PTX.Flow.readEReal_float_self, ``PTX.Flow.pairRead_float, ``PTX.Flow.joinValue_float,
    ``PTX.Flow.readERealOpnd_f32imm, ``PTX.Assumption.readFinite,
    ``PTX.Flow.ereal_coe_eq_top_or_bot, ``EReal.toReal_coe, ``PTX.Flow.mulEReal_coe,
    ``PTX.Flow.addEReal_coe, ``PTX.Flow.addEReal_coe_neg, ``PTX.Flow.mulEReal_bot_pos,
    ``PTX.Flow.mulEReal_bot_neg, ``PTX.Flow.mulEReal_top_pos, ``PTX.Flow.mulEReal_top_neg,
    ``PTX.Flow.addEReal_bot_coe, ``PTX.Flow.addEReal_top_coe, ``PTX.Flow.neg_coe_ereal,
    ``PTX.Flow.coe_max, ``PTX.Flow.coe_min_ereal, ``PTX.Flow.erealValue_coe, ``Rat.cast_ofNat,
    ``Rat.cast_one, ``Rat.cast_zero, ``Rat.cast_div, ``Rat.cast_neg, ``Rat.cast_natCast,
    ``one_div, ``Option.map_some, ``Option.bind_some, ``pure, ``Except.pure, ``ite_true,
    ``ite_false, ``true_and, ``and_true, ``not_false_eq_true, ``ne_eq,
    ``not_true_eq_false, ``one_ne_zero, ``zero_ne_one, ``inv_one, ``div_one, ``mul_one,
    ``one_mul].map mkIdent
  for n in base do args := args.push (← `(Lean.Parser.Tactic.simpLemma| $n:ident))
  args := args.push (← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte))
  args := args.push (← `(Lean.Parser.Tactic.simpLemma| PTX.Flow.readEReal_lit))
  evalTactic (← `(tactic| simp only [$args,*]))
  -- a product or sum with an infinite operand: its sign by the finite operand's (a numeral's
  -- or a recorded real's by `positivity` or the hypotheses in context)
  evalTactic (← `(tactic| try simp (disch := first | assumption | positivity) only
    [PTX.Flow.coe_add_bot, PTX.Flow.coe_add_top, PTX.Flow.addEReal_coe_bot,
      PTX.Flow.addEReal_coe_top, PTX.Flow.mulEReal_bot_pos, PTX.Flow.mulEReal_bot_neg,
      PTX.Flow.mulEReal_top_pos, PTX.Flow.mulEReal_top_neg, PTX.Flow.erealValue_f32_bot,
      PTX.Flow.erealValue_f32_top, PTX.Flow.readEReal_f32_ninf, PTX.Flow.readEReal_f32_pinf,
      PTX.Flow.bindRead_some_ok, Option.map_some, Option.bind_some, ite_true, ite_false]))
  -- the role's lemmas (`rule_simp`)
  evalTactic (← `(tactic| try rule_simp))

/-- `rule_core`: the step by Core's rule of a floating instruction that every assumption declines
on these operands (`rule_step` reaches it with the goal `execLocal L g t op = .ok (next …)`).
The library's own rule (`rule_core_lg2`: `lg2.approx` of a payload that a hypothesis makes zero,
Core's table `-inf`, `coreFloat_lg2_eq_zero`) is tried first; a role adds rules with `scoped
macro_rules`. -/
syntax "rule_core" : tactic
macro_rules | `(tactic| rule_core) => `(tactic| fail "rule_core: no Core rule")

/-- The library's Core rule: `lg2.approx` of a payload that a hypothesis makes zero. -/
macro "rule_core_lg2" : tactic => `(tactic| first
  -- inside `first` a failing step throws (no error recovery that would admit a goal)
  | (refine (PTX.Flow.execLocal_lg2_regs (v := ?val) ?hr).trans ?_
     case hr => assumption
     -- a fact's value may be written through the role's abbreviation (`fun x => .float .f32 x`)
     beta_reduce
     rw [PTX.Flow.coreFloat_lg2_eq_zero]
     · rfl
     · first | assumption | (symm; assumption) | linarith | fail "no zero")
  | fail "rule_core_lg2: not lg2.approx of a zero payload")

/-- Decide the conditions a rule's body still branches on (`if 0 < x then …`, the kernel's
`lg2` rule on a recorded real) from the hypotheses in context: a condition is shown by
`assumption` or `linarith`, its negation likewise, and the branch is taken (`ite_eq_left`,
`ite_eq_right` and their `dite` forms). A condition neither decides is left (the caller reports
it). -/
meta def ruleDecideConds : TacticM Unit := do
  for _ in [0:8] do
    let some g := (← getGoals).head? | return
    let ty ← instantiateMVars (← g.getType)
    let some it := ty.find? (fun e => (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) &&
        !(e.getArg! 1).hasLooseBVars && !(e.getArg! 1).hasMVar) | return
    let cE := it.getArg! 1
    -- a proof of `c` or `¬ c` on a goal of its own (a failed `by` inside a term would be logged,
    -- not thrown)
    let prove (ty : Expr) : TacticM (Option Expr) := do
      let mv ← mkFreshExprMVar ty
      let s ← saveState
      try
        let gs ← Tactic.run mv.mvarId! (withoutRecover (evalTactic (← `(tactic|
          first | assumption | linarith | (intro; linarith) | fail "undecided"))))
        if gs.isEmpty then return some (← instantiateMVars mv) else s.restore; return none
      catch _ => s.restore; return none
    let dep := it.isAppOfArity ``dite 5
    if let some pf ← prove cE then
      let tpf ← Term.exprToSyntax pf
      if dep then evalTactic (← `(tactic| rw [dite_eq_left $tpf]))
      else evalTactic (← `(tactic| rw [ite_eq_left $tpf]))
    else if let some pf ← prove (mkNot cE) then
      let tpf ← Term.exprToSyntax pf
      if dep then evalTactic (← `(tactic| rw [dite_eq_right $tpf]))
      else evalTactic (← `(tactic| rw [ite_eq_right $tpf]))
    else return
    evalTactic (← `(tactic| try simp only [PTX.Flow.bindRead_some_ok, Option.map_some,
      Option.bind_some, pure, Except.pure]))

/-- `sym_rule`: prove the conditions an assumption's rule leaves after the rule's own evaluation
(`ruleSimp` on the operand reads, `ruleDecideConds` on its conditions), so that the rule applies
under the facts at hand. The walk judges a rule by comparing its value with the fact's value
(`cheapDefEq`), so a rule whose premise is a *hypothesis* rather than a computation — that a pair is
finite, that a scale byte is not the NaN patterns, FlashMLA's `ChunkOk` decomposition — is not
taken unless the role proves the premise. Kernels extend it with `macro_rules`; it fails by
default. -/
syntax "sym_rule" : tactic
macro_rules | `(tactic| sym_rule) => `(tactic| fail "sym_rule: no rule premise")

/-- The step of the local instruction `op` at `q` from every state with the facts `F`, writing
register `d`: `(v, proof of ∀ R cf, Holds R F → execLocalA A L g ⟨q, R, cf, 0, [], none⟩ op =
.ok (next (setReg ⟨…⟩ d v)))`. The rule is that of the first assumption of `A` that selects
`op`; `srcs` are the registers `op` reads. -/
meta def ruleStepProof (A L g : Expr) (q : Nat) (op : Expr) (d : Nat) (F : Expr)
    (srcs : Array Nat) : TacticM (Expr × Expr) := withMainContext do
  let regsTy ← mkArrow (mkConst ``Nat) (← mkAppM ``Option #[mkConst ``PTX.Value])
  let cfTy ← mkAppM ``Option #[mkConst ``Bool]
  let vM ← mkFreshExprMVar (mkConst ``PTX.Value)
  let goalTy ← withLocalDeclD `R regsTy fun R => withLocalDeclD `cf cfTy fun cf => do
    let hTy ← mkAppM ``PTX.Proof.Holds #[R, F]
    withLocalDeclD `hR hTy fun hR => do
      let none' ← mkAppOptM ``Option.none #[mkConst ``PTX.Fault]
      let nilV ← mkAppOptM ``List.nil #[mkConst ``PTX.Value]
      let t := mkAppN (mkConst ``PTX.TState.mk) #[mkNatLit q, R, cf, mkNatLit 0, nilV, none']
      let lhs ← mkAppM ``PTX.execLocalA #[A, L, g, t, op]
      let rhs ← mkAppM ``PTX.next #[← mkAppM ``PTX.setReg #[t, mkNatLit d, vM]]
      let okE ← mkAppOptM ``Except.ok #[mkConst ``PTX.Fault, none, rhs]
      mkForallFVars #[R, cf, hR] (← mkEq lhs okE)
  let m ← mkFreshExprSyntheticOpaqueMVar goalTy
  let saved ← getGoals
  setGoals [m.mvarId!]
  let (fvs, g0) ← m.mvarId!.introN 3 [`R, `cf, `hR]
  setGoals [g0]
  -- the facts about reals in context, restated on this goal only (they stay out of the caller's
  -- goal, whose context would otherwise grow with every rule step)
  let facts ← realFacts
  g0.withContext do
    let none' ← mkAppOptM ``Option.none #[mkConst ``PTX.Fault]
    let nilV ← mkAppOptM ``List.nil #[mkConst ``PTX.Value]
    let t := mkAppN (mkConst ``PTX.TState.mk)
      #[mkNatLit q, mkFVar fvs[0]!, mkFVar fvs[1]!, mkNatLit 0, nilV, none']
    let thR ← Term.exprToSyntax (mkFVar fvs[2]!)
    -- the operand reads, from the facts
    let mut reads : Array Term := #[]
    let (ex, tbl) ← splitFacts F
    for r in srcs do
      let mut val? : Option Expr := none
      -- the position of an explicit fact (its membership by `mem_idx`)
      let mut idx? : Option Nat := none
      for i in [0:ex.size] do
        let q' ← whnfD ex[i]!
        if q'.isAppOfArity ``Prod.mk 4 && regLit? (← whnfD (q'.getArg! 2)) == some r then
          val? := some (q'.getArg! 3)
          idx? := some i
          break
      if val?.isNone then
        if let some (_, vf) := tbl then val? := some (← evalTable (mkApp vf (mkNatLit r)))
      let some val := val? | continue
      let tr := Syntax.mkNumLit (toString r)
      let tv ← Term.exprToSyntax (← ruleValue val)
      let h := mkIdent (← mkFreshUserName `hreg)
      let mem ← match idx? with
        | some i => `(term| PTX.Flow.mem_idx $(Syntax.mkNumLit (toString i)) rfl)
        | none => `(term| by fact_mem)
      evalTactic (← `(tactic|
        have $h:ident : _ = some $tv := PTX.Proof.holds_mem (r := $tr) $thR $mem))
      let nv ← whnfR (← ruleValue val)
      if nv.isAppOfArity ``PTX.Value.float 2 then
        reads := reads.push (← `(PTX.Flow.readERealOpnd_regs_float $h))
      else if nv.isAppOfArity ``PTX.Value.pair 2 &&
          (← whnfR (nv.getArg! 0)).isAppOfArity ``PTX.Value.float 2 &&
          (← whnfR (nv.getArg! 1)).isAppOfArity ``PTX.Value.float 2 then
        reads := reads.push (← `(PTX.Flow.readERealPair_regs_float $h))
      else if let some pr ← pairReadProof? (← ruleValue val) then
        let tpr ← Term.exprToSyntax pr
        reads := reads.push (← `(PTX.Flow.readERealPair_regs_read $h $tpr))
      else if let some (_, pr) ← erealRead? (← ruleValue val) then
        -- a value that reads as an extended real: a conditional, a written infinity, …
        let tpr ← Term.exprToSyntax pr
        reads := reads.push (← `(PTX.Flow.readERealOpnd_regs_read $h $tpr))
        reads := reads.push (← `(PTX.Flow.readERealPair_regs $h))
      else
        reads := reads.push (← `(PTX.Flow.readERealOpnd_regs $h))
        reads := reads.push (← `(PTX.Flow.readERealPair_regs $h))
    let tq := Syntax.mkNumLit (toString q)
    evalTactic (← `(tactic|
      refine (PTX.Assumption.SegFreePc.exec (pc := $tq) (by sym_seg_free) rfl).trans ?_))
    -- the assumptions before the selected one give no rule
    let mut lst ← whnfD A
    let mut found := false
    while lst.isAppOfArity ``List.cons 3 do
      let a := lst.getArg! 1
      let body ← ruleBody a L g t op
      let tail := lst.getArg! 2
      let goal ← getMainGoal
      let ty ← instantiateMVars (← goal.getType)
      let some (_, _, rhs) := ty.eq? | throwError "rule_step: goal {ty}"
      let lhs' ← mkAppM ``PTX.execLocalRule #[lst, L, g, t, op]
      replaceMainGoal [← goal.change (← mkEq lhs' rhs)]
      if body.isAppOfArity ``Option.none 1 then
        evalTactic (← `(tactic| refine PTX.Flow.execLocalRule_cons_none rfl ?_))
        lst ← whnfD tail
        continue
      -- the rule of `a`: evaluate it; it may still decline on these operands
      let s ← saveState
      try
        evalTactic (← `(tactic| refine PTX.Flow.execLocalRule_cons_some ?_))
        let g' ← getMainGoal
        let ty' ← instantiateMVars (← g'.getType)
        let some (_, _, rhs') := ty'.eq? | throwError "rule_step: goal {ty'}"
        replaceMainGoal [← g'.change (← mkEq body rhs')]
        ruleSimp reads facts
        ruleDecideConds
        if (← getGoals).isEmpty then
          found := true
          break
        -- the role's `sym_rule`: the rule applies under these facts, its remaining conditions
        -- being a premise the role proves
        let s3 ← saveState
        try
          withoutRecover (evalTactic (← `(tactic| sym_rule)))
          unless (← getGoals).isEmpty do throwError "sym_rule left goals"
          found := true
          break
        catch _ => s3.restore
        if (← IO.getEnv "RULE_STEP_REPORT").isSome then
          for gg in ← getGoals do
            IO.eprintln s!"rule_step {q}: {← ppExpr (← instantiateMVars (← gg.getType))}"
        let gty ← instantiateMVars (← (← getMainGoal).getType)
        -- a value may be a conditional (of a floating `selp`); a condition of the rule itself
        -- leaves the goal open
        let s1 ← saveState
        try evalTactic (← `(tactic| with_reducible rfl))
        catch _ =>
          s1.restore
          if let some (_, lhs, _) := gty.eq? then
            if let some it := lhs.find? (fun e => e.isAppOfArity ``ite 5 ||
                e.isAppOfArity ``dite 5) then
              throwError "the rule depends on the condition {it.getArg! 1}, which no \
                hypothesis in context decides"
          evalTactic (← `(tactic| rfl))
        found := true
        break
      catch ex =>
        let msg ← ex.toMessageData.toString
        s.restore
        -- a rule that declines given the facts
        let s2 ← saveState
        try
          evalTactic (← `(tactic| refine PTX.Flow.execLocalRule_cons_none ?_ ?_))
          let gs ← getGoals
          setGoals [gs[0]!]
          let g' ← getMainGoal
          let ty' ← instantiateMVars (← g'.getType)
          let some (_, _, rhs') := ty'.eq? | throwError "rule_step: goal {ty'}"
          replaceMainGoal [← g'.change (← mkEq body rhs')]
          ruleSimp reads facts
          ruleDecideConds
          unless (← getGoals).isEmpty do throwError "rule_step: not none"
          setGoals gs.tail
          lst ← whnfD tail
        catch _ =>
          s2.restore
          throwError "rule_step: the rule for the instruction at {q} does not evaluate: {msg}"
    -- every assumption declines on these operands: Core's rule (`rule_core`)
    let mut coreMsg : MessageData := m!""
    unless found do
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine (PTX.execLocalRule_of_none (fun _ h => (List.not_mem_nil h).elim)).trans ?_))
        let s1 ← saveState
        try withoutRecover (evalTactic (← `(tactic| rule_core_lg2)))
        catch e1 =>
          s1.restore
          try withoutRecover (evalTactic (← `(tactic| rule_core)))
          catch e2 => throwError "{e1.toMessageData}; {e2.toMessageData}"
        unless (← getGoals).isEmpty do throwError "rule_core left goals"
        found := true
      catch e =>
        coreMsg := e.toMessageData
        s.restore
    unless found do
      throwError "rule_step: no assumption gives the instruction at {q} a rule, and Core's rule \
        (`rule_core`) does not apply: {coreMsg}"
  setGoals saved
  let v ← instantiateMVars vM
  if v.hasMVar then throwError "rule_step: the value written at {q} is not determined: {v}"
  return (v, ← instantiateMVars m)

/-- Whether an assumption of `A` gives the local instruction `op` a rule at the state `t`. -/
meta def hasRule (A L g t op : Expr) : MetaM Bool := do
  let mut lst ← whnfD A
  while lst.isAppOfArity ``List.cons 3 do
    let body ← ruleBody (lst.getArg! 1) L g t op
    unless body.isAppOfArity ``Option.none 1 do return true
    lst ← whnfD (lst.getArg! 2)
  return false

end PTX.Flow
