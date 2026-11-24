-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # Why a site machine stops

A proof tool, generic over `Flow.Code` (promoted from Inkling's proof). `Code.StepAt d`
allows a fired event to leave the machine without a successor (`next d e = none`) when the thread
is dead after it, but it does not say why the machine stopped. `StopsFor C R d` says it: at a
fired event of `d`, `next d e = none` only when `R d e` holds. The role chooses `R` (a received
word without bits, a base word without an outcome, …); `next_ne_none` is the use: an event fired
at a state where `R` fails has a successor or a `some none`.

`StopsFor` is a fact about the machine's function at the events an instruction can fire, so it is
proved per site without the segments of `StepAt`:

* `stops_any`: an instruction whose events are not inverted (an issue, a store), from
  `next d e = none → R d e` for every event;
* `stops_wait`, `stops_elect`, `stops_shfl`, `stops_load`, `stops_vote`: the events of the class
  (`fires_wait`, `fires_elect`, `fires_shfl`, `fires_load`, `fires_vote`);
* `stops_exit`: `ret` and `exit` fire no continuing event.

`stops_cases x … trans [lemmas] stop_by (tac)` splits the sites as `site_cases` does and picks the
lemma by the class of the site's instruction (`stepClass`). It evaluates `next` with the role's
transition lemmas and splits the conditions that remain; a case whose `next` is not `none` closes
by `simp`, the others by the role's `tac`, which proves `R d e` from the case's hypotheses. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- At a fired event of `d`, the machine stops (`next d e = none`) only for the reason `R d e`. -/
structure StopsFor (C : Code K A L g) (R : C.D → Event → Prop) (d : C.D) : Prop where
  stop : ∀ {t e u} ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
    Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) → C.next d e = none → R d e

variable {R : C.D → Event → Prop} {d : C.D}

/-- **An event fired at a state where the reason fails does not stop the machine.** -/
theorem next_ne_none (hR : C.StopsFor R d) {t u : TState} {e : Event} {ins : Instr}
    (h : C.AtD d t) (hi : C.inv d) (hc : K.code[C.pc d]? = some ins)
    (hf : Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u)) (hn : ¬ R d e) :
    C.next d e ≠ none :=
  fun h0 => hn (hR.stop ins h hi hc hf h0)

/-- Every event that stops the machine at `d` has the reason. -/
theorem stops_any (h : ∀ e, C.next d e = none → R d e) : C.StopsFor R d :=
  ⟨fun _ _ _ _ _ hn => h _ hn⟩

theorem stops_wait {gd : Option (Nat × Bool)} {p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarWait p base off par acq sc⟩)
    (h : ∀ m q ok s, C.next d ⟨C.pc d, .wait m q ok acq s⟩ = none →
      R d ⟨C.pc d, .wait m q ok acq s⟩) : C.StopsFor R d := by
  refine ⟨fun {t e u} ins => ?_⟩
  intro ht _ hc hf hn
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  rw [← ht.1] at hf
  obtain ⟨m, q, ok, s, rfl, -⟩ := fires_wait hf
  rw [ht.1] at hn ⊢
  exact h m q ok s hn

theorem stops_elect {gd : Option (Nat × Bool)} {ty : Option DType} {dst : Option Nat} {p : Nat}
    {mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.elect, ty, [dst, some p], [], some mask⟩⟩)
    (h : ∀ mk inst ld, C.next d ⟨C.pc d, .elect mk inst ld⟩ = none →
      R d ⟨C.pc d, .elect mk inst ld⟩) : C.StopsFor R d := by
  refine ⟨fun {t e u} ins => ?_⟩
  intro _ _ hc hf hn
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf
  exact h mk inst ld hn

theorem stops_shfl {gd : Option (Nat × Bool)} {mode : ShflMode} {ty : Option DType} {r : Nat}
    {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.shfl mode, ty, [some r], [a, b, c], some mask⟩⟩)
    (h : ∀ av bv cv recv ok, C.next d ⟨C.pc d, .shfl mode av bv cv recv ok⟩ = none →
      R d ⟨C.pc d, .shfl mode av bv cv recv ok⟩) : C.StopsFor R d := by
  refine ⟨fun {t e u} ins => ?_⟩
  intro _ _ hc hf hn
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨av, bv, cv, recv, ok, rfl, -⟩ := fires_shfl (p := none) hf
  exact h av bv cv recv ok hn

theorem stops_load {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same)
    (h : ∀ x bs, C.next d ⟨C.pc d, .rd x bs⟩ = none → R d ⟨C.pc d, .rd x bs⟩) :
    C.StopsFor R d := by
  refine ⟨fun {t e u} ins => ?_⟩
  intro _ _ hc hf hn
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, -⟩ := fires_load hk hnc hf he
  exact h x bs hn

theorem stops_vote {gd : Option (Nat × Bool)} {ty : Option DType} {dv p : Nat} {neg pv : Bool}
    {mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.vote .ballot neg, ty, [some dv], [.reg p],
      some mask⟩⟩)
    (hpv : (p, .pred pv) ∈ C.facts d)
    (h : ∀ m b, C.next d ⟨C.pc d, .vote m (pv != neg) b⟩ = none →
      R d ⟨C.pc d, .vote m (pv != neg) b⟩) : C.StopsFor R d := by
  refine ⟨fun {t e u} ins => ?_⟩
  intro ht _ hc hf hn
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have hp : readPred L g t (.reg p) = .ok pv := by
    have hm := holds_mem ht.2.2.2.2 hpv
    simp [readPred, readReg, hm, bind, Except.bind, pure, Except.pure]
  obtain ⟨m, b, rfl, -⟩ := fires_vote hp hf
  exact h m b hn

theorem stops_exit {gd : Option (Nat × Bool)} {op : Op} (hc0 : K.code[C.pc d]? = some ⟨gd, op⟩)
    (hop : op = .ret ∨ op = .exit) : C.StopsFor R d := by
  refine ⟨fun {t e u} ins => ?_⟩
  intro _ _ hc hf _
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  rcases hop with rfl | rfl <;> simp [eventTmpl, Fires] at hf

end
end PTX.Flow.Code

namespace PTX.Flow
open PTX PTX.Proof
open Lean Meta Elab Tactic

/-- The site of the goal `C.StopsFor R d`: its kernel and program counter. -/
meta def stopsForPc (ty : Expr) : MetaM (Expr × Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isAppOfArity ``Code.StopsFor 7 do
    throwError "stops_cases: expected C.StopsFor R d, got {ty}"
  let C := ty.getArg! 4
  let d := ty.getArg! 6
  let pc ← natValue (← mkAppM ``Code.pc #[C, d])
  return (ty.getArg! 0, pc)

/-- The cases of `next d e = none → R d e` after the evaluation: a case whose `next` is not
`none` closes by `simp`, the others by the role's tactic. -/
syntax "stop_close " "[" Lean.Parser.Tactic.simpLemma,* "]" " (" tacticSeq ")" : tactic
macro_rules
  | `(tactic| stop_close [$ls,*] ($stop)) => `(tactic| (
      site_norm
      simp only [↓reduceIte, reduceCtorEq, false_implies, imp_self, Option.some.injEq, $ls,*]
      all_goals (repeat' split)
      all_goals first
        | (simp only [reduceCtorEq, false_implies, imp_self]; done)
        | (intro _; ($stop))))

/-- `stops_site trans [lemmas] stop_by (tac)`: the obligation `C.StopsFor R d` of a literal
site. -/
syntax "stops_site " "trans " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " stop_by " "(" tacticSeq ")" : tactic

elab_rules : tactic
  | `(tactic| stops_site trans [$ls,*] stop_by ($stop:tacticSeq)) => withMainContext do
    let (K, pc) ← stopsForPc (← getMainTarget)
    let code ← mkAppM ``PTX.Kernel.code #[K]
    let tac ← match ← stepClass K code pc with
      | .issue | .store | .alloc | .nc => `(tactic| (
          refine PTX.Flow.Code.stops_any ?_
          intro _
          stop_close [$ls,*] ($stop)))
      | .wait => `(tactic| (
          refine' PTX.Flow.Code.stops_wait ?hc ?_
          case hc => code_lookup
          intro _ _ _ _
          stop_close [$ls,*] ($stop)))
      | .elect => `(tactic| (
          refine' PTX.Flow.Code.stops_elect ?hc ?_
          case hc => code_lookup
          intro _ _ _
          stop_close [$ls,*] ($stop)))
      | .shfl | .shflValid => `(tactic| (
          refine' PTX.Flow.Code.stops_shfl ?hc ?_
          case hc => code_lookup
          intro _ _ _ _ _
          stop_close [$ls,*] ($stop)))
      | .load => `(tactic| (
          refine' PTX.Flow.Code.stops_load ?hc ?hk ?hnc ?he ?_
          case hc => code_lookup
          case hk => rfl
          case hnc => rfl
          case he => rfl
          intro _ _
          stop_close [$ls,*] ($stop)))
      | .vote => `(tactic| (
          refine' PTX.Flow.Code.stops_vote ?hc ?hpv ?_
          case hc => code_lookup
          case hpv => site_norm; exact PTX.Flow.mem_factsFrom (by lit_mem)
          intro _ _
          stop_close [$ls,*] ($stop)))
      | .exit => `(tactic| (
          refine' PTX.Flow.Code.stops_exit ?hc ?hop
          case hc => code_lookup
          case hop => first | exact .inl rfl | exact .inr rfl))
    evalTactic tac

/-- `stops_cases x … skip_by (tac) trans [lemmas] stop_by (tac)`: `C.StopsFor R d` at every site,
the site variables split as by `site_cases`. -/
syntax "stops_cases " (ppSpace colGt ident)+ (" skip_by " "(" tacticSeq ")")?
  " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" " stop_by " "(" tacticSeq ")" : tactic

elab_rules : tactic
  | `(tactic| stops_cases $xs* $[skip_by ($skip:tacticSeq)]? trans [$ls,*]
      stop_by ($stop:tacticSeq)) => withMainContext do
    let fvs ← xs.toList.mapM fun x => do return (← getLocalDeclFromUserName x.getId).fvarId
    let gs ← splitSites (← getMainGoal) fvs
    let mut out := []
    for g in gs do
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only [Fin.reduceFinMk, Fin.isValue]))
      if let some skip := skip then
        evalTactic (← `(tactic| try (($skip); done)))
        if (← getUnsolvedGoals).isEmpty then continue
      let g ← getMainGoal
      let site ← g.withContext do goalSite (← g.getType)
      try
        evalTactic (← `(tactic| stops_site trans [$ls,*] stop_by ($stop)))
      catch e =>
        throwError "stops_cases: at {site}: {e.toMessageData}"
      out := out ++ (← getUnsolvedGoals)
    setGoals out

end PTX.Flow
