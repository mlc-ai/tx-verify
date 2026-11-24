-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAFlow
public import Lemmas.Flow.Step.SiteIte
public import Lemmas.Flow.Step.StopReason

@[expose] public section

/-! # The prologue as a code machine, and what `site_cases` needs of it

`code` is the region as a code machine. Its obligations are proved by `site_cases`
(`ProASteps*`) with the tactics of this file, which give what the generic evaluation does not know
of this role:

* `word_subst` (the role's `seg_pre`): a loaded word that the machine records as a number
  (`word32 v = some x`) is written `b32 x`, the form the table states;
* `pred_facts` / `pred_split`: a guard of the segment on a table predicate (`%p40`, `%p59`, the
  row-validity predicates) gets its literal value from a hypothesis of the case, or from a case
  split, so that the evaluation skips or runs the guarded instruction;
* `pa_close`: a computed value equals the table's, by evaluation, or (a masked query load's zero)
  by the invariant's `qz`;
* `pa_inv`, `pa_guard`: the successor's invariant and the guard of the site's instruction. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The data of the first state: the inherited registers, no word loaded, no query value, no
received word. -/
def Dat.start (P : Inh) (w : Value := b32 P.tm) : Dat :=
  ⟨P, 0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => qZero, fun _ => false, b32 0, b32 0, b32 0, w⟩

/-- The first state: at `setmaxnreg.inc` (pc 27). -/
def D.start (P : Inh) (w : Value := b32 P.tm) : D := ⟨.sMax, Dat.start P w⟩

/-- The prologue as a code machine from its `setmaxnreg.inc`, with the registers `P`. -/
@[reducible] def code (L : Launch) (g : Nat) (P : Inh) : Flow.Code kernel asms L g where
  D := D
  init := D.start P
  pc := (·.site.pc)
  facts := facts L g
  sub := sub
  acc := acc
  inv := Inv L g
  next := next L g

/-- Why the machine stops: the election after a broadcast whose received word has no bits
(`PelDead`), or a base word without an outcome of the add at pc 319 (`addOk`). -/
def Stop (L : Launch) (g : Nat) (d : D) (_ : Event) : Prop :=
  PelDead d ∨ addOk d.dt.w = false ∨ (d.site = .bar2 ∧ div182 L g d.dt = false)

theorem ite_mk {c : Prop} [Decidable c] (a b : Site) (dt : Dat) :
    (⟨if c then a else b, dt⟩ : D) = if c then ⟨a, dt⟩ else ⟨b, dt⟩ := by
  split <;> rfl

/-- A predicate fact of known value in front of the start facts. -/
theorem seg_pred {n s b N : Nat} {F G : List (Nat × Value)} {c c' : Bool}
    (hp : (N, Value.pred c) ∈ F) (hc : c = c')
    (h : Seg kernel asms L g n s ((N, .pred c') :: F) b G) : Seg kernel asms L g n s F b G :=
  h.weaken_start fun _ hR => ⟨hc ▸ holds_mem hR hp, hR⟩

/-- The invariant after the query load `k`, which returned a two-byte value. -/
theorem Inv.q {s s' : Site} {dt : Dat} {k : Nat} {v : Value} (hi : Inv L g ⟨s, dt⟩)
    (hk : s.qIdx = k) (hv : v.bytes = 2) (hk' : k < s'.qIdx)
    (hg : guardVal L g (qUpd dt k v) s' = true) :
    Inv L g ⟨s', qUpd dt k v⟩ := by
  refine ⟨hi.args, hg, fun j hj => ?_, fun j => ?_⟩
  · simp only [qUpd, Function.update_of_ne (show j ≠ k by simp only at hj; omega)]
    exact hi.qz j (by simp only at hj ⊢; omega)
  · by_cases hj : j = k
    · subst hj; simpa [qUpd] using hv
    · simp only [qUpd, Function.update_of_ne hj]; exact hi.qb j

open Lean Elab Tactic Meta

/-- `word_subst`: a loaded word recorded as the number `x` (`word32 v = some x`) is `b32 x`. -/
elab "word_subst" : tactic => withMainContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    if let some (_, lhs, _) := ty.eq? then
      if lhs.isAppOfArity ``word32 1 && lhs.appArg!.isFVar then
        let h ← Term.exprToSyntax ld.toExpr
        Term.withoutErrToSorry <| evalTactic (← `(tactic|
          (obtain ⟨hh, -⟩ := word32_spec $h; subst hh)))
        return

macro_rules | `(tactic| seg_pre) => `(tactic| word_subst)

/-- The register of a predicate of the table: `v_pN` is `%pN`, register `N`. -/
meta def predReg? (e : Expr) : Option Nat := do
  let some n := e.getAppFn.constName? | none
  let s := Name.lastComponentAsString n
  unless String.startsWith s "v_p" do none
  String.toNat? (String.drop s 3).toString

/-- `pred_facts`: in front of the start facts of a segment, the literal value of each table
predicate that a hypothesis decides (`v_pN … = b` or `¬ v_pN … = true`). -/
elab "pred_facts" : tactic => withMainContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    let h ← Term.exprToSyntax ld.toExpr
    let (lhs?, lit?, neg) := match ty.eq? with
      | some (_, l, r) => (some l, if r.isConstOf ``Bool.true then some true
          else if r.isConstOf ``Bool.false then some false else none, false)
      | none =>
        if ty.isAppOfArity ``Not 1 then match ty.appArg!.eq? with
          | some (_, l, r) => (some l, if r.isConstOf ``Bool.true then some false else none, true)
          | none => (none, none, false)
        else (none, none, false)
    let some lhs := lhs? | continue
    let some lit := lit? | continue
    let some N := predReg? lhs | continue
    let tN := Syntax.mkNumLit (toString N)
    let tc ← Term.exprToSyntax lhs
    let tl := mkIdent (if lit then ``Bool.true else ``Bool.false)
    let pf ← if neg then `(Bool.eq_false_iff.mpr $h) else pure h
    Term.withoutErrToSorry <| evalTactic (← `(tactic| first
      | (refine seg_pred (N := $tN) (c := $tc) (c' := $tl) ?hp $pf ?_
         case hp => (fact_mem; done))
      | skip))

/-- `pred_split N`: split on the table value of `%pN` at the data of the start facts. -/
elab "pred_split " n:num : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let args ← match ty.find? (·.isAppOfArity ``valueOf 3) with
    | some v => pure v.getAppArgs
    | none => match ty.find? (·.isAppOfArity ``factsAt 4) with
      | some v => pure #[v.getArg! 0, v.getArg! 1, v.getArg! 3]
      | none => throwError "pred_split: no table"
  let c ← mkAppM (Name.mkStr (``valueOf).getPrefix s!"v_p{n.getNat}") args
  let tc ← Term.exprToSyntax c
  Term.withoutErrToSorry <| evalTactic (← `(tactic| by_cases hps : $tc = true))

/-- `inv_qz`: a query value of the start that the invariant in context makes the zero `qZero`. -/
elab "inv_qz" : tactic => withMainContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars ld.type)
    if ty.isAppOfArity ``Inv 3 then
      let h ← Term.exprToSyntax ld.toExpr
      Term.withoutErrToSorry <| evalTactic (← `(tactic| (
        have hqz := ($h).qz
        dsimp only at hqz
        simp (disch := decide) [qUpd, Function.update_apply, qZero, v_rs18, hqz]
        done)))
      return
  throwError "inv_qz: no invariant"

/-- A computed value of a segment equals the table's. -/
macro "pa_close" : tactic => `(tactic| (
  try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none]
  all_goals (try dsimp only [qZero, v_rs18, wCta, wSmem, wAdd32, wSub32, wMulLo32, wMadLo32,
    wMaxS32, wMinS32, wMinU32, wShrU32, wShrS32, wShl32, wShl64, wShl16, wAnd32, wOr32, wXor32,
    wNot32, wOr16, wAdd16, wCvt16of32, wCvt32of16, wMulHiU16, wBfeU32, wAdd64, wMulWideU32,
    wMulWideS32, wMadWideU32, wMadWideS32, wDivS32, pLtU32, pGtS32, pEqB32, pNeB32,
    kind_s_beq_s, kind_u_beq_s, kind_b_beq_s])
  all_goals first
    | rfl
    | assumption
    | (simp; done)
    | (simp [qZero]; done)
    | inv_qz
    | fail "pa_close"))

/-- A segment: with the decided predicates in front, else split on `%p40` or `%p59` (the guards
of the copies and initializations after an election). -/
macro "pa_seg1" : tactic => `(tactic| (pred_facts; intro t h; seg_fp h using pa_close))

macro "pa_seg" : tactic => `(tactic| first
  | pa_seg1
  | (pred_split 40 <;> pa_seg1)
  | (pred_split 59 <;> pa_seg1)
  | fail "pa_seg")

/-- The successor's invariant: the data keep their query values (`Inv.mv`), or the query load
recorded a two-byte value (`Inv.q`). -/
macro "pa_inv1" hi:ident : tactic => `(tactic| exact Inv.mv $hi _ _ rfl
    (by first | rfl | assumption | simpa [guardVal] using ($hi).guard)
    (fun j hj => ($hi).qz j (le_trans (by dsimp only; decide) hj)) ($hi).qb)

macro "pa_inv2" hi:ident : tactic => `(tactic|
  exact Inv.q $hi rfl (by assumption) (by decide)
    (by first | exact ($hi).guard | assumption | simpa [guardVal] using ($hi).guard))

macro "pa_inv" : tactic => `(tactic| (intro hi; first
  | pa_inv1 hi
  | pa_inv2 hi
  | ((repeat' split) <;> first | pa_inv1 hi | pa_inv2 hi | fail "pa_inv")
  | fail "pa_inv"))

/-- The guard of the site's instruction: true in the table (an election's predicate), or the
invariant's `guard`. -/
macro "pa_guard" : tactic => `(tactic| first
  | rfl
  | (rename_i hi; exact congrArg Value.pred hi.guard)
  | (rename_i hi; simpa [valueOf, table, PTX.Flow.lookupLit, guardVal] using hi.guard)
  | fail "pa_guard")

/-- `pro_steps s`: the obligations of the sites `s` ranges over (`site_cases` with this role's
transition lemmas and tactics), except the given overrides. -/
syntax "pro_steps " ident (" except " "[" siteOverride,* "]")? " skip_by " "(" tacticSeq ")" :
  tactic
macro_rules
  | `(tactic| pro_steps $s $[except [$ovs,*]]? skip_by ($skip)) => do
    let ovs := (ovs.map (·.getElems)).getD #[]
    `(tactic| site_cases $s except [$ovs,*] skip_by ($skip)
      trans [next, qSite, ite_mk, beq_self_eq_true, beq_eq_decide, decide_false, decide_true,
        Bool.and_true, Bool.and_false]
      seg_by (pa_seg) inv_by (pa_inv) guard_by (pa_guard))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
