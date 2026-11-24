-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym
public import Lemmas.Flow.IssueNext
public import Lemmas.Flow.Step.LoadVec
public import Lemmas.Flow.Step.Record
public import Mathlib.Tactic.FinCases
public meta import Lean
public meta import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Site obligations by case analysis

A proof tool for the obligations `C.StepAt d` of a site machine whose sites form an inductive
type with `Fin`, `Bool` and enumeration parameters only. Nothing here is specific to a kernel:
the machine is read through `C.pc`, `C.facts`, `C.next`, `C.inv`, and the code through the
kernel's generated lookups `Flow.code_<pc>`.

* `code_lookup` closes `K.code[i]? = some ?ins` with the generated lookup of the numeral that
  `i` evaluates to.
* `advances` proves that an event instruction continues at the next instruction.
* `site_norm` reduces the machine's projections in the goal and evaluates the closed terms of a
  site type (a role's successor function applied to literals) to constructors, with `Fin`
  values as literals, and closed `Nat`/`Bool` terms built from `Fin` literals to literals.
* `next_simp [lemmas]` evaluates a transition of the machine with the role's transition
  lemmas and determines the successor by unification.
* `seg_auto using tac` and `seg_sym using tac` (`Step/SegSym.lean`) prove the segments
  `∃ n, Seg K A L g n s F b G`, the second through control on symbolic predicates.
* `site_step` discharges one site: its event instruction and guard, then the combinator of
  `Step/Combinators.lean` that its instruction selects, the successors by `next_simp`, their
  segments by `seg_auto`, else `seg_sym`, and their invariants by the role's tactic. Where a
  class has two combinators, the specific one is tried first (`step_stop` before `step_issue`,
  `step_shfl` before `step_shfl_rec` before `step_shfl_sel`, `step_load` before
  `step_load_sel` before `step_load_ext` (a `.local` load with an extension) before
  `step_ldv_mid_sel` before `step_ldv_last_sel` (the elements of a vector load; the `_sel` forms
  find their successors by splitting the transition's value), `step_load_sel` before
  `step_load_dead` (a load after which the thread may die), `step_arrive` before
  `step_arrive_sel` (an arrival whose successor is any outcome), `step_allocWr` before
  `step_alloc` (the two sub-steps of `tcgen05.alloc`; a file with allocation sites imports
  `Lemmas/Flow/Step/Alloc.lean`, which this module does not, to keep `Flow.allocT` out of other
  kernels' scope), `step_vec_mid` before `step_vec_last`).
  A `.nc` load (`step_nc_sel`, the two elements `step_nc_first`, `step_nc_last_sel`) and a
  shuffle that writes its validity predicate (`step_shfl_valid`) are classes of their own, read
  off the instruction, so the other loads' and shuffles' combinators are not tried first. The
  hook `seg_pre` (a role's preparation of a segment goal, by default nothing) runs before the
  segment tactic of a dead outcome.
* `site_cases x y … except [site => proof, …] skip_by (…) trans […] seg_by (…) inv_by (…)
  guard_by (…)`
  splits the site variables (a site type, `Fin` or `Bool`) into all their values and runs
  `site_step` at every site that no override names. An override gives the `StepOk` or the
  `StepAt` proof of its site; a pattern such as `.mma _ _` names a family of sites. `skip_by`
  closes the sites that a hypothesis of the theorem excludes, so that the sites of one machine
  can be split over several theorems, which are checked in parallel.

The role gives four things once: its transition lemmas (`trans`), the tactic that closes a
segment `Seg … n …` (`seg_by`, usually `seg_fp` with the role's value lemmas), the tactic that
proves a successor's invariant from the site's (`inv_by`), and the tactic that proves the value
of a guard predicate in the site's table (`guard_by`). -/

namespace PTX.Flow
open PTX PTX.Proof
open Lean Meta Elab Tactic

/-- `advances`: an event instruction whose only continuation is the next instruction. -/
macro "advances" : tactic => `(tactic| first
  | exact fun hf => PTX.Flow.fires_next (by exact trivial) hf
  | exact fun hf => PTX.Flow.fires_async_next (by exact trivial) hf
  | exact fun hf => PTX.Flow.fires_tcMma (by simp) hf
  | exact fun hf => PTX.Flow.fires_tcMmaTs hf
  | exact fun hf => PTX.Flow.fires_tcCommit hf
  | exact fun hf => PTX.Flow.fires_clcTryCancel hf
  | exact fun hf => PTX.Flow.fires_barSyncN_next hf
  | exact fun hf => PTX.Flow.fires_tcRelinquish_next hf
  | exact fun hf => PTX.Flow.fires_tcDealloc_next hf
  | exact fun hf => PTX.Flow.fires_cpAsync_next hf
  | exact fun hf => PTX.Flow.fires_cpAsyncCommit_next hf
  | exact fun hf => PTX.Flow.fires_cpAsyncArrive_next hf
  | fail "advances: the instruction does not continue at the next instruction only")

/-- An inductive type without parameters whose constructors take no arguments: a finite
enumeration. -/
meta def isEnumType (ty : Expr) : MetaM Bool := do
  let some n := (← whnfR ty).getAppFn.constName? | return false
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  if iv.numParams != 0 || iv.numIndices != 0 || iv.isRec then return false
  iv.ctors.allM fun c => do
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    return ci.numFields == 0

/-- An inductive type without parameters whose constructors take `Fin`, `Bool` and enumeration
values only: the shape of a site type. -/
meta def isSiteType (ty : Expr) : MetaM Bool := do
  let some n := (← whnfR ty).getAppFn.constName? | return false
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  if iv.numParams != 0 || iv.numIndices != 0 || iv.isRec || iv.ctors.length < 2 then
    return false
  iv.ctors.allM fun c => do
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    forallTelescope ci.type fun xs _ => xs.allM fun x => do
      let t ← whnfR (← inferType x)
      return t.isAppOfArity ``Fin 1 || t.isConstOf ``Bool || (← isEnumType t)

/-- The projections of a site machine. -/
meta def codeProjs : List Name :=
  [``Code.pc, ``Code.facts, ``Code.next, ``Code.inv, ``Code.sub, ``Code.acc]

/-- `site_norm`: reduce the machine's projections (`C.pc d` to the role's site table) and
evaluate the closed terms of a site type; `Fin` values become literals. A closed `Nat` or `Bool`
term built from a `Fin` literal (`elPc i` at a literal `i`, `k.val == 63`) becomes its literal when
it reduces to one. -/
elab "site_norm" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let cache ← IO.mkRef (∅ : Std.HashMap Name Bool)
  let siteTy (e : Expr) : MetaM Bool := do
    let t ← whnfR (← inferType e)
    let some n := t.getAppFn.constName? | return false
    if let some b := (← cache.get)[n]? then return b
    let b ← isSiteType t
    cache.modify (·.insert n b)
    return b
  let ty' ← Meta.transform ty (pre := fun e => do
    let f := e.getAppFn
    let some n := f.constName? | return .continue
    if codeProjs.contains n then
      let e' ← whnfR e
      if e' != e then return .visit e'
      return .continue
    if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
    if (← getEnv).isConstructor n then return .continue
    if ← siteTy e then
      return .done (← Meta.reduce e (skipProofs := true) (skipTypes := true))
    -- a closed number or Boolean built from a `Fin` literal (a pc table read at a family's
    -- index, a test of the index): its value, when it reduces to a literal
    -- (only an application with a `Fin` literal among its own arguments: a cheap test, since
    -- this runs at every closed subterm of the goal)
    unless e.getAppArgs.any (fun x => x.isAppOf ``Fin.mk ||
        (x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 0).isAppOfArity ``Fin 1)) do
      return .continue
    let t ← whnfR (← inferType e)
    unless t.isConstOf ``Nat || t.isConstOf ``Bool do return .continue
    let r ← Meta.reduce e (skipProofs := true) (skipTypes := true)
    if let some k := r.rawNatLit? then return .done (mkNatLit k)
    if let some k := r.nat? then return .done (mkNatLit k)
    if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then return .done r
    return .continue)
  -- a change whose check runs away (a free word's arithmetic unfolded) is skipped
  if ty' != ty then
    let s0 ← saveState
    tryCatchRuntimeEx (replaceMainGoal [← goal.change ty']) fun _ => s0.restore
  evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))

/-- `rfl_assign`: close `a = b` by unification, assigning the named holes of `site_step`. -/
elab "rfl_assign" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, a, b) := ty.eq? | throwError "rfl_assign: expected an equation, got {ty}"
  -- a unification that runs away (through the conditions of a successor) counts as a failure
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 })
      (withCurrHeartbeats (withAssignableSyntheticOpaque (isDefEq a b))))
    (fun _ => pure false)
  unless ok do
    throwError "rfl_assign: {a} and {b} do not unify"
  goal.assign (← mkEqRefl a)
  replaceMainGoal []

/-- `next_simp [lemmas]`: evaluate the machine's transition in an equation `C.next d e = …`
with the role's transition lemmas; the successor is then fixed by unification. -/
syntax "next_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| next_simp [$ls,*]) => `(tactic| (
      site_norm
      try simp only [↓reduceIte, eq_self_iff_true, ne_eq,
        not_false_eq_true, Bool.false_eq_true, reduceCtorEq, Option.some.injEq, $ls,*]
      try rfl_assign))

/-- `drop_norm`: write the facts `dropReg r F` of a load (`step_load_sel`) whose `F` unfolds to
`factsFrom live val` as `factsFrom (live.filter (· != r)) val`, the form `seg_fp` reads. -/
elab "drop_norm" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ty' ← Meta.transform ty (pre := fun e => do
    unless e.isAppOfArity ``PTX.Flow.Code.dropReg 2 do return .continue
    let mut f := e.getArg! 1
    for _ in [0:16] do
      if f.isAppOfArity ``PTX.Flow.factsFrom 2 then break
      match ← unfoldDefinition? f with
      | some f' => f := f'.headBeta
      | none => break
    unless f.isAppOfArity ``PTX.Flow.factsFrom 2 do return .continue
    return .done (← mkAppM ``PTX.Flow.Code.dropReg #[e.getArg! 0, f]))
  unless (ty'.find? fun e => e.isAppOfArity ``PTX.Flow.Code.dropReg 2).isSome do return
  if ty' != ty then replaceMainGoal [← goal.change ty']
  evalTactic (← `(tactic| simp only [PTX.Flow.Code.dropReg_factsFrom]))

/-- The successor obligations of a combinator: the segment (`seg`), sub-step and accumulator,
and the invariant (`inv`). -/
syntax "lands_auto " "(" tacticSeq ")" "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| lands_auto ($seg) ($inv)) => `(tactic| (
      sym_mark "lands: start"
      intros
      refine ⟨?seg, ?sub, ?acc, ?inv⟩
      case sub => first | rfl | ((repeat' split) <;> rfl)
      case acc => first | rfl | ((repeat' split) <;> rfl)
      case seg =>
        sym_mark "lands: sub, acc"
        intro _
        site_norm
        sym_mark "lands: site_norm"
        try dsimp only [PTX.Flow.Code.electFacts]
        try drop_norm
        sym_mark "lands: drop_norm"
        -- the walk decides the segment's length, or where it must be cut, before any
        -- evaluation: no evaluation is started that a symbolic branch would stop
        first
          | seg_sym using $seg
          | seg_auto using $seg
      case inv =>
        sym_mark "lands: inv"
        site_norm
        ($inv)
        sym_mark "lands: done"))

theorem not_mem_of_elem {r : Nat} {l : List Nat} (h : l.elem r = false) : r ∉ l :=
  fun hm => by rw [List.elem_eq_true_of_mem hm] at h; cases h

/-- `lit_not_mem`: `r ∉ l` for a numeral `r` and a list that evaluates to a literal, by the
kernel's evaluation of `List.elem` (no auxiliary declaration, unlike `decide +kernel`, so the
proofs of a file stay checked in parallel). -/
elab "lit_not_mem" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  let mem := if ty.isAppOfArity ``Not 1 then ty.appArg!.consumeMData else ty
  unless mem.isAppOfArity ``Membership.mem 5 do throwError "lit_not_mem: expected r ∉ l"
  let some r := regLit? (← whnfD (mem.getArg! 4)) | throwError "lit_not_mem: not a numeral"
  let l ← regList (mem.getArg! 3)
  if l.contains r then throwError "lit_not_mem: {r} is in the list"
  let lE ← mkRegList l
  let pf := mkApp3 (mkConst ``not_mem_of_elem) (mkNatLit r) lE
    (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.false))
  goal.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

/-- A register outside the live set of the site's facts. -/
macro "fact_free" : tactic =>
  `(tactic| (site_norm; exact PTX.Flow.not_mem_factsFrom (by lit_not_mem)))

/-- The event instruction of a site and its guard: `guard` closes the value equation of a
guard predicate in the site's table. -/
syntax "site_guard " "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| site_guard ($gd)) => `(tactic| first
      | trivial
      | exact PTX.Flow.Code.guardTrue_factsFrom (by lit_mem) (by $gd))

/-- The `site` field of `StepAt`: the site is an event instruction whose guard holds. -/
syntax "site_event " "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| site_event ($gd)) => `(tactic| (
      intro _
      refine ⟨?ins, ?hc, ?hloc, ?hg⟩
      case hc => code_lookup
      case hloc => rfl
      case hg => site_guard ($gd)))

namespace Code
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An arrival without a state register whose successor `o` does not depend on the event and may
be any outcome: a state (`Lands`), no followed state, or a dead thread (`DeadFrom` at the next
instruction). -/
theorem step_arrive_sel {d : C.D} {o : Option (Option C.D)} {gd : Option (Nat × Bool)}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster release : Bool} {scope : MbarScope}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarArrive base off tx count cluster release scope none⟩)
    (hn : ∀ e, C.next d e = o) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hdead : o = none → DeadFrom K A L g (C.pc d + 1) (C.facts d))
    (hl : ∀ d', o = some (some d') → C.Lands d (C.pc d + 1) (C.facts d) d') : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := fires_arrive_next hf
  have hu := At.next (at_of_atD h hs ha)
  exact cont_sel hi (hn _) hu (fun hx => hdead hx _ hu) hl

/-- `step_arrive_sel` with the successor written as the machine's transition on a fixed event (an
arrival's successor does not depend on the event): `site_step` unifies `hn` by `rfl` and splits
the transition's `if`s, where a successor found by unification would be a `Bool.rec` that `split`
cannot open. -/
theorem step_arrive_fix {d : C.D} {gd : Option (Nat × Bool)}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster release : Bool} {scope : MbarScope}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarArrive base off tx count cluster release scope none⟩)
    (hn : ∀ e, C.next d e = C.next d ⟨0, .exit⟩) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hdead : C.next d ⟨0, .exit⟩ = none → DeadFrom K A L g (C.pc d + 1) (C.facts d))
    (hl : ∀ d', C.next d ⟨0, .exit⟩ = some (some d') → C.Lands d (C.pc d + 1) (C.facts d) d') :
    C.StepOk d :=
  step_arrive_sel hc0 hn hs ha hdead hl

end Code

/-- The classes of event instructions, by the combinator that discharges them. -/
inductive StepClass
  | issue | wait | elect | shfl | shflValid | load | nc | store | vote | exit | alloc

/-- The class of the event instruction at `pc`. -/
meta def stepClass (K code : Expr) (pc : Nat) : MetaM StepClass := do
  let some ins ← instrAt K code pc | throwError "site_step: no instruction at {pc}"
  let ins ← whnfD ins
  let op ← whnfD (ins.getArg! 1)
  let some c := op.getAppFn.constName? | return .issue
  if c == ``PTX.Op.mbarWait then return .wait
  if c == ``PTX.Op.ret || c == ``PTX.Op.exit then return .exit
  if c == ``PTX.Op.tcAlloc then return .alloc
  if c == ``PTX.Op.mem then
    let k ← whnfD (← mkAppM ``PTX.MemAccess.kind #[op.appArg!])
    if k.isConstOf ``PTX.MemKind.load then
      let nc ← whnfD (← mkAppM ``PTX.MemAccess.nc #[op.appArg!])
      if nc.isConstOf ``Bool.true then return .nc
      return .load
    if k.isConstOf ``PTX.MemKind.store then return .store
    return .issue
  if c == ``PTX.Op.warp then
    let kind ← whnfD (← mkAppM ``PTX.WarpInstr.kind #[op.appArg!])
    match kind.getAppFn.constName? with
    | some ``PTX.WarpKind.elect => return .elect
    | some ``PTX.WarpKind.shfl =>
      -- a second destination is the validity predicate
      let ds ← whnfD (← mkAppM ``PTX.WarpInstr.dsts #[op.appArg!])
      if ds.isAppOfArity ``List.cons 3 then
        let tl ← whnfD ds.appArg!
        if tl.isAppOfArity ``List.cons 3 then
          let p ← whnfD (tl.getArg! 1)
          if p.isAppOfArity ``Option.some 2 then return .shflValid
      return .shfl
    | some ``PTX.WarpKind.vote => return .vote
    | _ => return .issue
  return .issue

/-- The site of the goal `C.StepAt d`: its program counter. -/
meta def stepAtPc (ty : Expr) : MetaM (Expr × Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isAppOfArity ``Code.StepAt 6 do throwError "site_step: expected C.StepAt d, got {ty}"
  let C := ty.getArg! 4
  let d := ty.getArg! 5
  let pc ← natValue (← mkAppM ``Code.pc #[C, d])
  let K := ty.getArg! 0
  return (K, pc)

/-- `seg_pre`: a role's preparation of a segment goal before `seg_auto` (a value it records in
another form, say). By default it does nothing. A role extends it with `scoped macro_rules` in
its own namespace, so that its rule is tried only where that namespace is open: a global rule is
tried in every file that imports it, the most recently imported first, and a rule that never
fails then shadows the rules of other roles (Inkling's `word_subst` before `mma_pre`). The same
holds for a role's rules of `lands_auto`. -/
syntax "seg_pre" : tactic
macro_rules | `(tactic| seg_pre) => `(tactic| skip)

/-- `site_dead (seg)`: a role's proof of a dead outcome (`DeadFrom …`) of a site, tried before
`seg_sym` and, at a `.nc` pair, before the transition is unfolded by the role's lemmas (a cut at a
division after the loop's branches, `dead_cut`). By default it fails. A role extends it with
`scoped macro_rules` in its namespace (as `seg_pre`). -/
syntax "site_dead " "(" tacticSeq ")" : tactic
macro_rules | `(tactic| site_dead ($_)) => `(tactic| fail "site_dead")

/-- A dead outcome (`DeadFrom …`): the role's `site_dead`, else `seg_sym` after `seg_pre`. The
branch hypotheses a `split` leaves as `¬ (b = true)` are put as `b = false` (the form `seg_sym`
decides a predicate by), and the start facts `(r, v) :: dropReg r (C.facts d)` of a load's death
are reduced to a literal list as for a successor (`drop_norm`). -/
macro "dead_close " "(" seg:tacticSeq ")" : tactic => `(tactic| first
  | site_dead ($seg)
  | (site_norm
     try simp only [Bool.not_eq_true] at *
     try drop_norm
     seg_pre
     seg_sym using $seg))

/-- The access conditions of a `.nc` load whose instruction the lookup gives (`NcLoad`). -/
macro "nc_load_ok" : tactic =>
  `(tactic| exact ⟨rfl, rfl, rfl, rfl, ⟨_, _, rfl⟩, rfl, by site_norm; decide +kernel⟩)

/-- `first_report | tac | …`: the first alternative that succeeds, each run without error recovery
(a failing step throws instead of being logged and admitted); when all fail, the error names every
alternative's failure, so that the one meant for the site is visible. -/
syntax (name := firstReport) "first_report "
  withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

elab_rules : tactic
  | `(tactic| first_report $[| $tacs]*) => do
    let mut errs : Array MessageData := #[]
    for t in tacs do
      let s ← saveState
      try
        withoutRecover (evalTactic t)
        return
      catch e =>
        errs := errs.push e.toMessageData
        s.restore
    throwError "every alternative failed:{indentD (MessageData.joinSep errs.toList
      (Format.line ++ "---" ++ Format.line))}"

/-- `site_step trans [lemmas] seg_by (tac) inv_by (tac) guard_by (tac)`: the obligation
`C.StepAt d` of a literal site. -/
syntax "site_step " "trans " "[" Lean.Parser.Tactic.simpLemma,* "]"
  (" dead_trans " "[" Lean.Parser.Tactic.simpLemma,* "]")?
  " seg_by " "(" tacticSeq ")" " inv_by " "(" tacticSeq ")" " guard_by " "(" tacticSeq ")" :
  tactic

elab_rules : tactic
  | `(tactic| site_step trans [$ls,*] $[dead_trans [$lds?,*]]? seg_by ($seg:tacticSeq)
      inv_by ($inv:tacticSeq) guard_by ($gd:tacticSeq)) => withMainContext do
    -- the lemmas that unfold the transition in a dead outcome: `dead_trans` if the role gives
    -- it (a role whose `site_dead` needs part of the transition folded), else `trans`
    let lds := lds?.getD ls
    let (K, pc) ← stepAtPc (← getMainTarget)
    let code ← mkAppM ``PTX.Kernel.code #[K]
    evalTactic (← `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event ($gd))))
    let tac ← match ← stepClass K code pc with
      | .issue => `(tactic| first_report
        | try_rt (
          refine PTX.Flow.Code.step_stop ?hn
          intro e; next_simp [$ls,*]; done)
        | try_rt (
          refine' (PTX.Flow.Code.step_issue (dn := ?dn) ?hc ?hadv ?hn ?hs ?ha
            ?hl)
          case hc => code_lookup
          case hadv => advances
          case hs => rfl
          case ha => rfl
          case hn => intro e; next_simp [$ls,*]
          case hl => lands_auto ($seg) ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_arrive (dn := ?dn) ?hc ?hst ?hn ?hs ?ha ?hl)
          case hc => code_lookup
          case hst => intro r hr; cases hr; fact_free
          case hs => rfl
          case ha => rfl
          case hn => intro e; next_simp [$ls,*]
          case hl => lands_auto ($seg) ($inv))
        | try_rt (
          -- the instruction first, as a goal of its own (a failed `by` inside the term would be
          -- logged and abort, which hides the next alternative's error)
          refine' PTX.Flow.Code.step_arrive_fix ?hc (fun _ => rfl) rfl rfl ?_ ?_
          case hc => code_lookup
          · intro hv
            first
              | (site_dead ($seg))
              | (try simp only [$lds,*, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true,
                   Bool.true_eq_false] at hv
                 (try split_ifs at hv) <;> (repeat' split at hv) <;>
                   first
                   | (cases hv; done)
                   | contradiction
                   | dead_close ($seg))
          · intro d' hv
            try simp only [$ls,*, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true,
              Bool.true_eq_false] at hv
            (try split_ifs at hv) <;> (repeat' split at hv) <;>
              first
              | (cases hv; done)
              | contradiction
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 lands_auto ($seg) ($inv))))
      | .store => `(tactic| first_report
        | try_rt (
          refine' (PTX.Flow.Code.step_vec_mid (dn := ?dn) ?hc ?hk ?hsub ?hn ?hpc ?hs ?ha ?hF
            ?hinv)
          case hc => code_lookup
          case hk => rfl
          case hsub => exact of_decide_eq_true rfl
          case hn => intro e; next_simp [$ls,*]
          case hpc => rfl
          case hs => rfl
          case ha => rfl
          case hF => rfl
          case hinv => site_norm; ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_vec_last (dn := ?dn) ?hc ?hk ?hsub ?hn ?ha ?hl)
          case hc => code_lookup
          case hk => rfl
          case hsub => exact of_decide_eq_false rfl
          case hn => intro e; next_simp [$ls,*]
          case ha => rfl
          case hl => lands_auto ($seg) ($inv)))
      | .wait => `(tactic| (
          refine' (PTX.Flow.Code.step_wait (dok := ?dok) (dfail := ?dfail)
            ?hc ?hp ?hok ?hfail ?hs ?ha ?hlok ?hlfail)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hp => fact_free
          case hok => intro m q a s; next_simp [$ls,*]
          case hfail => intro m q a s; next_simp [$ls,*]
          case hlok => lands_auto ($seg) ($inv)
          case hlfail => lands_auto ($seg) ($inv)))
      | .elect => `(tactic| (
          refine' (PTX.Flow.Code.step_elect (dl := ?dl) (ds := ?ds)
            ?hc ?hp ?hd ?hnl ?hns ?hs ?ha ?hll ?hls)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hp => fact_free
          case hd =>
            intro r hr
            first | (cases hr; done) | (cases hr; exact ⟨by fact_free, by decide⟩)
          case hnl => intro mk inst ld hld; next_simp [hld, $ls,*]
          case hns => intro mk inst ld hld; next_simp [hld, $ls,*]
          case hll => lands_auto ($seg) ($inv)
          case hls => lands_auto ($seg) ($inv)))
      | .shfl => `(tactic| first_report
        | try_rt (
          refine' (PTX.Flow.Code.step_shfl (dok := ?dok) (v := ?v)
            ?hc ?hr ?hn ?hs ?ha ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hn => intro m av bv cv recv ok; next_simp [$ls,*]
          case hl => lands_auto ($seg) ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_shfl_rec (dok := ?dok)
            ?hc ?hr ?hn ?hs ?ha ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hn => intro m av bv cv recv ok; next_simp [$ls,*]; done
          case hl => lands_auto ($seg) ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_shfl_sel (nv := ?nv)
            ?hc ?hr ?hn ?hs ?ha ?hnn ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hn => intro m av bv cv recv ok; next_simp [$ls,*]; done
          case hnn => intro v; beta_reduce; (repeat' split) <;> simp
          case hl =>
            intro v d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv)))
        | try_rt (
          refine' (PTX.Flow.Code.step_shfl_dead (nv := ?nv)
            ?hc ?hr ?hn ?hs ?ha ?hl ?hdead)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hn => intro m av bv cv recv ok; next_simp [$ls,*]; done
          case hl =>
            intro v d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv))
          case hdead =>
            intro v hv _
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (change PTX.Flow.DeadFrom _ _ _ _ _ _
                 dead_close ($seg))))
      | .shflValid => `(tactic| (
          refine' (PTX.Flow.Code.step_shfl_valid (nv := ?nv) ?hc ?hr ?hp ?hrp ?hn ?hs ?ha ?hdead
            ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hp => fact_free
          case hrp => decide
          case hn => intro m av bv cv recv ok; next_simp [$ls,*]; done
          case hdead =>
            intro v ok u hv
            beta_reduce at hv
            (repeat' split at hv) <;> first | (cases hv; done) | simp at hv
          case hl =>
            intro v ok d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (cases hv; done)
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv))))
      | .load => `(tactic| first_report
        | try_rt (
          refine' (PTX.Flow.Code.step_load (dok := ?dok) ?hc ?hk ?hnc ?he
            ?hregs ?hr ?hok ?herr ?hs ?ha ?hl)
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case he => rfl
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr => intro x bs f hv; next_simp [hv, $ls,*]; done
          case hl => lands_auto ($seg) ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_load_sel (nv := ?nv) ?hc ?hk ?hnc ?he
            ?hregs ?hok ?herr ?hs ?ha ?hnn ?hl)
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case he => rfl
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hnn => intro v; beta_reduce; (repeat' split) <;> simp
          case hl =>
            intro v d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv)))
        | try_rt (
          refine' (PTX.Flow.Code.step_load_dead (nv := ?nv) ?hc ?hk ?hnc ?he
            ?hregs ?hok ?herr ?hs ?ha ?hl ?hdead)
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case he => rfl
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hl =>
            intro v d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv))
          case hdead =>
            intro v hv _
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (change PTX.Flow.DeadFrom _ _ _ _ _ _
                 dead_close ($seg)))
        | try_rt (
          refine' (PTX.Flow.Code.step_load_ext (nv := ?nv) ?hc ?hk ?hnc ?hsp
            ?hregs ?hok ?herr ?hs ?ha ?hnn ?hext ?hl)
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case hsp => rfl
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hnn => intro v; beta_reduce; (repeat' split) <;> simp
          case hext =>
            intro v f d' hv
            beta_reduce
            (repeat' split) <;>
              first
              | (simp; done)
              | (rw [PTX.Flow.Code.extendLoaded_bits (by decide)] at hv; cases hv)
          case hl =>
            intro v v' d' hv hx
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 rw [PTX.Flow.Code.extendLoaded_bits (by decide)] at hx
                 cases hx
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv)))
        | try_rt (
          refine' (PTX.Flow.Code.step_ldv_mid_sel (nv := ?nv) ?hc ?hk ?hnc ?he ?hsub ?hok
            ?herr ?hnn ?hmid)
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case he => rfl
          case hsub => exact of_decide_eq_true rfl
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hnn => intro v; beta_reduce; (repeat' split) <;> simp
          case hmid =>
            intro v d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (exfalso; simp_all; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 refine ⟨rfl, rfl, rfl, rfl, ?_⟩
                 site_norm
                 ($inv)))
        | try_rt (
          refine' (PTX.Flow.Code.step_ldv_last_sel (nv := ?nv) ?hc ?hk ?hnc ?he ?hsub ?hnd
            ?hok ?herr ?hnn ?hl)
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case he => rfl
          case hsub => exact of_decide_eq_false rfl
          case hnd => decide
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hnn => intro v; beta_reduce; (repeat' split) <;> simp
          case hl =>
            intro v d' hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (simp at hv; done)
              | (exfalso; simp_all; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 vec_facts_norm
                 lands_auto ($seg) ($inv))))
      | .nc => `(tactic| first_report
        | try_rt (
          refine' (PTX.Flow.Code.step_nc_sel (nv := ?nv) ?hc ?hnc ?hregs ?hr ?hok ?herr ?hs ?ha
            ?hdead ?hl)
          case hc => code_lookup
          case hnc => nc_load_ok
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hr => fact_free
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hdead =>
            intro v u _ hv hu
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (cases hv; done)
              | (simp at hv; done)
              | (refine (show PTX.Flow.DeadFrom _ _ _ _ _ _ from ?_) u hu
                 dead_close ($seg))
          case hl =>
            intro v d' _ hv
            beta_reduce at hv
            (repeat' split at hv) <;>
              first
              | (cases hv; done)
              | (simp at hv; done)
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 try simp only [$ls,*]
                 lands_auto ($seg) ($inv)))
        | try_rt (
          refine' (PTX.Flow.Code.step_nc_first (dn := ?dn) ?hc ?hnc ?hregs ?hok ?herr ?hs ?ha
            ?hpc ?hsub ?hacc ?hF ?hinv)
          case hc => code_lookup
          case hnc => nc_load_ok
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hpc => intro v; rfl
          case hsub => intro v; rfl
          case hacc => intro v; rfl
          case hF => intro v; rfl
          case hinv => intro v _; site_norm; ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_nc_last_sel (nv := ?nv) ?hc ?hnc ?hregs ?hr0 ?hr1 ?h01
            ?hok ?herr ?hs ?ha ?hdead ?hl)
          case hc => code_lookup
          case hnc => nc_load_ok
          case hregs => rfl
          case hs => rfl
          case ha => rfl
          case hr0 => fact_free
          case hr1 => fact_free
          case h01 => decide
          case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
          case herr =>
            intro x bs f hv
            first | (left; next_simp [hv, $ls,*]; done) | (right; next_simp [hv, $ls,*]; done)
          case hdead =>
            intro v u _ hv hu
            beta_reduce at hv
            (repeat' split at hv)
            -- the role's dead outcome while the transition is still folded, then unfolded
            all_goals first
              | (cases hv; done)
              | contradiction
              | (refine (show PTX.Flow.DeadFrom _ _ _ _ _ _ from ?_) u hu
                 site_dead ($seg))
              | (try simp only [$lds,*, ↓reduceIte, ite_true, ite_false] at hv
                 (repeat' split at hv)
                 all_goals try simp only [$lds,*, ↓reduceIte, ite_true, ite_false] at hv
                 all_goals (repeat' split at hv)
                 all_goals first
                   | (cases hv; done)
                   | contradiction
                   | (refine (show PTX.Flow.DeadFrom _ _ _ _ _ _ from ?_) u hu
                      dead_close ($seg)))
          case hl =>
            intro v d' _ hv
            beta_reduce at hv
            try simp only [$ls,*] at hv
            (repeat' split at hv)
            all_goals try simp only [$ls,*] at hv
            all_goals (repeat' split at hv)
            all_goals first
              | (cases hv; done)
              | contradiction
              | (have hd := Option.some.inj (Option.some.inj hv)
                 subst hd
                 lands_auto ($seg) ($inv))))
      | .vote => `(tactic| (
          refine' (PTX.Flow.Code.step_vote (dok := ?dok) ?hc ?hpv ?hr ?hn
            ?hs ?ha ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hpv => site_norm; exact PTX.Flow.mem_factsFrom (by lit_mem)
          case hr => fact_free
          case hn => intro m b; next_simp [$ls,*]
          case hl => lands_auto ($seg) ($inv)))
      | .alloc => `(tactic| first_report
        | try_rt (
          refine' (PTX.Flow.Code.step_allocWr (dn := ?dn) ?hc ?hs ?ha ?hn ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hn => intro e; next_simp [$ls,*]
          case hl => lands_auto ($seg) ($inv))
        | try_rt (
          refine' (PTX.Flow.Code.step_alloc (dw := ?dw) (dn := ?dn) ?hc ?hs ?ha ?hw ?hn ?hwpc
            ?hwsub ?hwacc ?hwf ?hwinv ?hl)
          case hc => code_lookup
          case hs => rfl
          case ha => rfl
          case hw => intro h0 e; next_simp [h0, $ls,*]
          case hn => intro h0 e; next_simp [h0, $ls,*]
          case hwpc => rfl
          case hwsub => rfl
          case hwacc => rfl
          case hwf => rfl
          case hwinv => site_norm; ($inv)
          case hl => lands_auto ($seg) ($inv)))
      | .exit => `(tactic| (
          refine' (PTX.Flow.Code.step_exit ?hc ?hop)
          case hc => code_lookup
          case hop => first | exact .inl rfl | exact .inr rfl))
    evalTactic tac

/-- The issue branch of `site_step` with the continuation lemma `adv` given. -/
syntax "issue_step " term " trans " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " seg_by " "(" tacticSeq ")" " inv_by " "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| issue_step $adv trans [$ls,*] seg_by ($seg) inv_by ($inv)) => `(tactic| (
      refine' (PTX.Flow.Code.step_issue (dn := ?dn) ?hc ?hadv ?hn ?hs ?ha ?hl)
      case hc => code_lookup
      case hadv => exact fun hf => $adv hf
      case hs => rfl
      case ha => rfl
      case hn => intro e; next_simp [$ls,*]
      case hl => lands_auto ($seg) ($inv)))

declare_syntax_cat siteOverride
syntax term " => " term : siteOverride

/-- The site of a goal `C.StepAt ⟨site, …⟩`: its first subterm that applies a constructor of a
site type. -/
meta def goalSite (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let env ← getEnv
  let r ← IO.mkRef (none : Option Expr)
  Meta.forEachExpr ty fun e => do
    if (← r.get).isSome then return
    let some n := e.getAppFn.constName? | return
    let some (.ctorInfo ci) := env.find? n | return
    if e.getAppNumArgs != ci.numFields then return
    if ← isSiteType (← inferType e) then r.set (some e)
  r.get

/-- Split every variable of `xs` (a site type, `Fin` or `Bool`) and the `Fin`, `Bool` and
enumeration fields of the site constructors into all their values. -/
meta partial def splitSites (g : MVarId) (xs : List FVarId) : MetaM (List MVarId) := do
  match xs with
  | [] => return [g]
  | x :: rest =>
    g.withContext do
    let ty ← whnfR (← instantiateMVars (← x.getType))
    if ty.isAppOfArity ``Fin 1 || ty.isConstOf ``Bool then
      let gs ← Lean.Elab.Tactic.finCasesAt g x
      return (← gs.mapM fun g => splitSites g rest).flatten
    if ← isSiteType ty then
      let subs ← g.cases x
      let mut out := []
      for sg in subs do
        let fs := sg.fields.toList.filterMap fun e => if e.isFVar then some e.fvarId! else none
        out := out ++ (← splitSites sg.mvarId (fs ++ rest))
      return out
    throwError "site_cases: {Expr.fvar x} is neither a site, a Fin nor a Bool"

/-- A family entry `.c x y => proof` (also `Site.c x y`): the constructor's last name and the
names its fields receive (`_` keeps a field anonymous). -/
meta def familyKey (stx : Syntax) : MetaM (Name × Array Name) := do
  let (hd, args) :=
    if stx.getKind == ``Lean.Parser.Term.app then (stx[0], stx[1].getArgs) else (stx, #[])
  let c ← match hd with
    | .ident .. => pure hd.getId
    | _ =>
      if hd.getKind == ``Lean.Parser.Term.dotIdent then pure hd[1].getId
      else throwError "families: expected a constructor applied to names, got {stx}"
  let names ← args.mapM fun a => do
    if a.isIdent then return a.getId
    if a.getKind == ``Lean.Parser.Term.hole then return Name.anonymous
    throwError "families: a field is named by an identifier or _, got {a}"
  return (c, names)

/-- `splitSites` that keeps the fields of the constructors named in `fams` whole: such a goal is
returned with the index of its entry and its fields renamed as the entry says, so that one proof
covers the whole family. -/
meta partial def splitSitesFam (fams : Array (Name × Array Name)) (g : MVarId)
    (xs : List FVarId) : MetaM (List (MVarId × Option Nat)) := do
  match xs with
  | [] => return [(g, none)]
  | x :: rest =>
    g.withContext do
    let ty ← whnfR (← instantiateMVars (← x.getType))
    if ty.isAppOfArity ``Fin 1 || ty.isConstOf ``Bool then
      let gs ← Lean.Elab.Tactic.finCasesAt g x
      return (← gs.mapM fun g => splitSitesFam fams g rest).flatten
    if ← isSiteType ty then
      let subs ← g.cases x
      let mut out := []
      for sg in subs do
        let fs := sg.fields.toList.filterMap fun e => if e.isFVar then some e.fvarId! else none
        match fams.findIdx? (fun (c, _) => c.isSuffixOf (sg.ctorName.getD .anonymous)) with
        | some i =>
          let names := fams[i]!.2
          unless names.size == fs.length do
            throwError "families: {sg.ctorName} has {fs.length} fields, {names.size} named"
          let mut mv := sg.mvarId
          for (f, n) in fs.zip names.toList do
            unless n.isAnonymous do mv ← mv.rename f n
          out := out ++ (← splitSitesFam fams mv rest).map fun (g', _) => (g', some i)
        | none => out := out ++ (← splitSitesFam fams sg.mvarId (fs ++ rest))
      return out
    throwError "site_cases: {Expr.fvar x} is neither a site, a Fin nor a Bool"

/-- A site variable that a hypothesis of the context fixes by an equation (`hs : s = .tiles
false`) is substituted, so that the site is literal and the split produces the theorem's one site
instead of one goal per constructor of the site type (Loader's 566, Correction's 263): the goal then
goes to `site_step`/`site_shape_step` directly, and the `skip` tactic finds nothing to close.
Returns the variables still to split, and the goal. -/
meta def substSiteEqs (g : MVarId) (fvs : List FVarId) : MetaM (List FVarId × MVarId) := do
  let mut g := g
  let mut keep : List FVarId := []
  for fv in fvs do
    -- a hypothesis whose type is `x = t` or `t = x`, `x` this site variable and `t` free of it
    let found ← g.withContext do
      let mut out : Option FVarId := none
      for ldecl in (← getLCtx) do
        if out.isNone && !ldecl.isImplementationDetail then
          let ty ← instantiateMVars ldecl.type
          if let some (_, a, b) := ty.eq? then
            let a ← whnfR a
            let b ← whnfR b
            if a.isFVar && a.fvarId! == fv && !b.hasAnyFVar (· == fv) then
              out := some ldecl.fvarId
            else if b.isFVar && b.fvarId! == fv && !a.hasAnyFVar (· == fv) then
              out := some ldecl.fvarId
      return out
    let mut done := false
    if let some h := found then
      if let some g' ← Lean.Meta.subst? g h then
        g := g'
        done := true
    unless done do keep := keep ++ [fv]
  return (keep, g)

/-- Split the site variables `xs`, keeping the families `fms` whole, and close each family's
goal with `close` applied to its proof (after `skip`, as at a site). Returns the goals of the
single sites and what the families' proofs leave. -/
meta def familySites (fms : Option (Syntax.TSepArray `siteOverride ","))
    (skip : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (g : MVarId) (xs : List FVarId)
    (close : TSyntax `term → TacticM Unit) : TacticM (List MVarId × List MVarId) := do
  -- a site the context fixes by an equation is literal before the split: no enumeration of the
  -- site type's other constructors, no `skip` per discarded goal
  let (xs, g) ← substSiteEqs g xs
  replaceMainGoal [g]
  let fms : Array (Syntax × TSyntax `term) := match fms with
    | some o => o.getElems.map fun ov => (ov.raw[0], ⟨ov.raw[2]⟩)
    | none => #[]
  let keys ← fms.mapM fun (k, _) => familyKey k
  let gs0 ← splitSitesFam keys g xs
  let mut sites := []
  let mut out := []
  let mut used : Array Bool := fms.map fun _ => false
  for (g, fam?) in gs0 do
    if fam?.isNone then
      sites := sites ++ [g]
      continue
    let i := fam?.getD 0
    used := used.set! i true
    setGoals [g]
    evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))
    if let some skip := skip then
      evalTactic (← `(tactic| try (($skip); done)))
      if (← getUnsolvedGoals).isEmpty then continue
    try close fms[i]!.2
    catch e => throwError "at the family {fms[i]!.1}: {e.toMessageData}"
    out := out ++ (← getUnsolvedGoals)
  for (u, (k, _)) in used.zip fms do
    unless u do throwError "families: no site of {k}"
  return (sites, out)

/-- `site_cases x … except [site => proof, …] families [.c x … => proof, …] skip_by (tac)
trans [lemmas] seg_by (tac) inv_by (tac) guard_by (tac)`. `skip_by` closes the sites that the
theorem's hypotheses exclude (a theorem about part of the sites). A `families` entry keeps the
`Fin`, `Bool` and enumeration fields of its constructor unsplit, names them as written, and closes
the one goal of the whole family with its proof, which may mention the names. -/
syntax "site_cases " (ppSpace colGt ident)+ (" except " "[" siteOverride,* "]")?
  (" families " "[" siteOverride,* "]")?
  (" skip_by " "(" tacticSeq ")")? " trans " "[" Lean.Parser.Tactic.simpLemma,* "]"
  (" dead_trans " "[" Lean.Parser.Tactic.simpLemma,* "]")?
  " seg_by " "(" tacticSeq ")" " inv_by " "(" tacticSeq ")" " guard_by " "(" tacticSeq ")" : tactic

elab_rules : tactic
  | `(tactic| site_cases $xs* $[except [$ovs,*]]? $[families [$fms,*]]?
      $[skip_by ($skip:tacticSeq)]? trans [$ls,*] $[dead_trans [$lds?,*]]? seg_by ($seg:tacticSeq)
      inv_by ($inv:tacticSeq) guard_by ($gd:tacticSeq)) => withMainContext do
    let lds := lds?.getD ls
    let fvs ← xs.toList.mapM fun x => do return (← getLocalDeclFromUserName x.getId).fvarId
    let (gs, famOut) ← familySites fms skip (← getMainGoal) fvs fun prf => do
      evalTactic (← `(tactic| first
        | exact $prf
        | (refine PTX.Flow.Code.StepAt.of ?site $prf
           case site => site_event ($gd))))
    let ovs : Array (TSyntax `term × TSyntax `term) := match ovs with
      | some o => o.getElems.map fun ov => (⟨ov.raw[0]⟩, ⟨ov.raw[2]⟩)
      | none => #[]
    let mut unused := ovs.map (·.1)
    let mut out := []
    for g in gs do
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))
      if let some skip := skip then
        evalTactic (← `(tactic| try (($skip); done)))
        if (← getUnsolvedGoals).isEmpty then continue
      let g ← getMainGoal
      let site ← g.withContext do goalSite (← g.getType)
      let mut chosen := none
      if let some site := site then
        for (p, prf) in ovs do
          let hit ← g.withContext do withNewMCtxDepth do
            let pe ← Term.elabTerm p (← inferType site)
            Term.synthesizeSyntheticMVarsNoPostponing
            isDefEq pe site
          if hit then
            chosen := some prf
            unused := unused.filter (· != p)
            break
      try
        match chosen with
        | some prf =>
          evalTactic (← `(tactic| first
            | exact $prf
            | (refine PTX.Flow.Code.StepAt.of ?site $prf
               case site => site_event ($gd))))
        | none =>
          evalTactic (← `(tactic|
            site_step trans [$ls,*] dead_trans [$lds,*] seg_by ($seg) inv_by ($inv)
              guard_by ($gd)))
      catch e =>
        throwError "site_cases: at {site}: {e.toMessageData}"
      out := out ++ (← getUnsolvedGoals)
    unless unused.isEmpty do throwError "site_cases: overrides of no site: {unused}"
    setGoals (out ++ famOut)

end PTX.Flow
