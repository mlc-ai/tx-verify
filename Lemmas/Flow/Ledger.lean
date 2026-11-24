-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.ArriveCount
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.Final
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.NotArrive
public import Lemmas.Flow.Polls

@[expose] public section

/-! # Event shapes and count ledgers of site machines

A proof tool. A role states once which event the site of each abstract state fires: its kind,
object and operands as functions of the state, a table `Ev : D → Event → Prop` (`Code.Shape`:
every event fired at a state's site, continuing or not, has the state's shape). Every later fact
about the role's events reads the table instead of the instruction and the registers:

* a count of the events of one kind on one object along the run (the role's ledger) moves at a
  step by what the step's shape gives, so each count is arithmetic on the table, one case per
  site (`shape_cases`);
* a table whose shapes are no undefined behaviour shows that no site's template is undefined
  behaviour (`Code.Shape.not_ub`).

Two inversions the tables use: an event instruction whose template is neither undefined
behaviour nor an exit continues the thread (`fires_some_of_ok`), and an arrival names the object,
byte count and arrival count its operands evaluate to, whatever its state destination
(`fires_arrive_kind`). -/

namespace PTX.Flow
open PTX PTX.Proof
open Lean Meta Elab Tactic

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The event-shape table of a code machine**: every event fired at the site of a state, with
the state's facts and invariant, has the state's shape. -/
def Code.Shape (C : Code K A L g) (Ev : C.D → Event → Prop) : Prop :=
  ∀ {d : C.D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}, C.AtD d t → C.inv d →
    K.code[C.pc d]? = some ins → Fires (C.pc d) (eventTmpl A L g t ins.op) e o → Ev d e

/-- A shape table none of whose shapes is undefined behaviour: no site's template is undefined
behaviour. -/
theorem Code.Shape.not_ub {C : Code K A L g} {Ev : C.D → Event → Prop} (hS : C.Shape Ev)
    (hub : ∀ d e f, Ev d e → e.kind ≠ .ub f) {d : C.D} {t : TState} {ins : Instr}
    (hat : C.AtD d t) (hi : C.inv d) (hc : K.code[C.pc d]? = some ins) (f : Fault) :
    eventTmpl A L g t ins.op ≠ .ub f :=
  not_ub_of_fires (fun f hf => hub d _ f (hS hat hi hc hf) rfl) f

/-- An event instruction other than `ret` and `exit` whose template is not undefined behaviour
continues the thread after its event. -/
theorem fires_some_of_ok {t : TState} {op : Op} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hok : ∀ f, eventTmpl A L g t op ≠ .ub f)
    (hop : op ≠ .ret ∧ op ≠ .exit) : ∃ u, o = some u := by
  rcases o with _ | u
  · exfalso
    rcases fires_none_ends hf with ⟨f, hk⟩ | hk
    · obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      cases hm : eventTmpl A L g t op <;> rw [hm] at hf <;> simp only [Fires] at hf <;>
        first | exact hok _ hm | simp_all
    · rcases fires_exit_op hf hk with h | h
      · exact hop.1 h
      · exact hop.2 h
  · exact ⟨u, rfl⟩

/-- An arrival names the object, byte count and arrival count its operands evaluate to,
whatever its state destination. -/
theorem fires_arrive_kind {t : TState} {base : Nat} {off : Int} {tx count : Opnd} {rel : Bool}
    {sc : MbarScope} {st : Option Nat} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    {b n : BitVec 64} (hm : mbarLoc L g t base off = .ok m) (hb : readBits L g t 32 tx = .ok b)
    (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count false rel sc st)) e o) :
    ∃ rel' sc', e.kind = .arrive m b.toNat n.toNat rel' sc' := by
  simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hb, hn, bind, Except.bind,
    pure, Except.pure, ofExec] at hf
  cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  · rw [hf.1]
    exact ⟨_, _, rfl⟩
/-- A fired poll at a site where no assumption widens the scope keeps the instruction's acquire
flag and scope. -/
theorem fires_wait_exact {t : TState} {p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} {pc : Nat} {e : Event} {o : Option TState} {m : Loc} {q : BitVec 64}
    (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hm : mbarLoc L g t base off = .ok m) (hq : readBits L g t 32 par = .ok q)
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off par acq sc)) e o) :
    ∃ ok, e.kind = .wait m (q.toNat % 2) ok acq sc := by
  simp only [eventTmpl, widenMbarScope, hA, Bool.false_eq_true, ↓reduceIte, tmaTmpl, hm, hq,
    bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
  obtain ⟨ok, hk, -⟩ := hf
  exact ⟨ok, by rw [hk]⟩

/-- An arrival at a site where no assumption widens the scope names the object, byte count,
arrival count, release flag and scope of the instruction. -/
theorem fires_arrive_exact {t : TState} {base : Nat} {off : Int} {tx count : Opnd} {rel : Bool}
    {sc : MbarScope} {st : Option Nat} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    {b n : BitVec 64} (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hm : mbarLoc L g t base off = .ok m) (hb : readBits L g t 32 tx = .ok b)
    (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count false rel sc st)) e o) :
    e.kind = .arrive m b.toNat n.toNat rel sc := by
  simp only [eventTmpl, widenMbarScope, hA, Bool.false_eq_true, ↓reduceIte, tmaTmpl, hm, hb, hn,
    bind, Except.bind, pure, Except.pure, ofExec] at hf
  simp only [Fires] at hf
  rw [hf.1]

/-- An event fired at a state of a code machine with a shape table has the state's shape. -/
theorem Code.Shape.fired {C : Code K A L g} {Ev : C.D → Event → Prop} (hS : C.Shape Ev)
    (hC : ∀ d, C.StepAt d) {d : C.D} {e : Event} {o : Option TState}
    (hf : C.toMachine.Fired (some d) e o) : Ev d e ∧ C.inv d := by
  obtain ⟨t, ⟨hat, hi⟩, hf⟩ := hf
  obtain ⟨ins, hc, -, -⟩ := (hC d).site hi
  change Fires t.pc (C.tmpl (some d) t) e o at hf
  simp only [Code.tmpl, hc] at hf
  rw [hat.1] at hf
  exact ⟨hS hat hi hc hf, hi⟩

/-- An event fired at a state of a code machine sits at the state's site. -/
theorem Code.fired_pc {C : Code K A L g} {d : C.D} {e : Event} {o : Option TState}
    (hf : C.toMachine.Fired (some d) e o) : e.pc = C.pc d := by
  obtain ⟨t, ⟨hat, -⟩, hf⟩ := hf
  rw [fires_pc hf, hat.1]

/-- An event fired at a state of a code machine fires from a concrete state of it, at its site's
instruction. -/
theorem Code.fired_tmpl {C : Code K A L g} (hC : ∀ d, C.StepAt d) {d : C.D} {e : Event}
    {o : Option TState} (hf : C.toMachine.Fired (some d) e o) :
    ∃ t ins, C.AtD d t ∧ C.inv d ∧ K.code[C.pc d]? = some ins ∧
      Fires (C.pc d) (eventTmpl A L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, hi⟩, hf⟩ := hf
  obtain ⟨ins, hc, -, -⟩ := (hC d).site hi
  change Fires t.pc (C.tmpl (some d) t) e o at hf
  simp only [Code.tmpl, hc] at hf
  rw [hat.1] at hf
  exact ⟨t, ins, hat, hi, hc, hf⟩

/-- An instruction at a literal site is not an mbarrier operation: it is neither an
`mbarrier.arrive` nor an `mbarrier.try_wait` (`arriveOp`, `waitOp`), the fact a ledger needs at
the other sites (`Code.fired_notMbar`). -/
def NotMbarAt (K : Kernel) (pc : Nat) : Prop :=
  ∀ ins, K.code[pc]? = some ins → arriveOp ins.op = false ∧ waitOp ins.op = false

/-- **No shape is needed at a site that is not an mbarrier operation**: an event fired at a site
whose instruction is neither an `mbarrier.arrive` nor an `mbarrier.try_wait` is neither an
arrival nor a successful poll on any object, so a ledger of arrivals and polls takes no step
there without the site's shape. -/
theorem Code.fired_notMbar {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {C : Code K A L g} (hC : ∀ d, C.StepAt d) {d : C.D} {e : Event} {o : Option TState}
    (hf : C.toMachine.Fired (some d) e o) {ins : Instr} (hc : K.code[C.pc d]? = some ins)
    (ha : arriveOp ins.op = false) (hw : waitOp ins.op = false) (m : Loc) :
    arrivesOn m e = false ∧ okPoll m e = false := by
  obtain ⟨t, ins', hat, hi, hc', hfire⟩ := C.fired_tmpl hC hf
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  exact ⟨arrivesOn_of_arriveOp ha hfire, okPoll_of_waitOp hw hfire⟩

/-- **No shape is needed at a site whose pc no instruction family names** (`NotMbarAt`). -/
theorem Code.fired_notMbar_at {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {C : Code K A L g} (hC : ∀ d, C.StepAt d) {d : C.D} {e : Event} {o : Option TState}
    (hf : C.toMachine.Fired (some d) e o) {pc : Nat} (hpc : C.pc d = pc) (hK : NotMbarAt K pc)
    (m : Loc) : arrivesOn m e = false ∧ okPoll m e = false := by
  obtain ⟨t, ins, hat, hi, hc, hfire⟩ := C.fired_tmpl hC hf
  obtain ⟨ha, hw⟩ := hK ins (hpc ▸ hc)
  exact ⟨arrivesOn_of_arriveOp ha hfire, okPoll_of_waitOp hw hfire⟩

/-- **The ledger of a run of a code machine**: a count of the events that satisfy `P` grows at a
step by what the step's event gives, so along a run from `d0` it is the count function `cnt` of
the state reached, less its value at `d0` (one arithmetic fact per step, `hstep`). -/
theorem Code.count_after {C : Code K A L g} {Ev : C.D → Event → Prop} (hS : C.Shape Ev)
    (hC : ∀ d, C.StepAt d) (cnt : C.D → Nat) (P : Event → Bool)
    (hstep : ∀ d e d', C.inv d → Ev d e → C.next d e = some (some d') →
      cnt d' = cnt d + (if P e then 1 else 0))
    {d0 : C.D} {es : List Event} (h : C.toMachine.Trace (some d0) es) :
    ∀ (j : Nat) (d : C.D), C.toMachine.after (some d0) (es.take j) = some (some d) →
      cnt d = cnt d0 + (es.take j).countP P := by
  intro j
  induction j with
  | zero => intro d ha; cases ha; simp
  | succ j ih =>
    intro d ha
    by_cases hj : j < es.length
    · have hget : es[j]? = some es[j] := List.getElem?_eq_getElem hj
      rw [List.take_add_one, hget, Option.toList_some,
        Machine.after_snoc (M := C.toMachine) (some d0)] at ha
      rcases h.fired hget with ⟨τ, o, hτ, hf⟩ | ⟨hτ, -⟩
      · rw [hτ] at ha
        cases τ with
        | none => cases (show C.toMachine.next none es[j] = some none from rfl) ▸ ha
        | some dj =>
          obtain ⟨hev, hi⟩ := hS.fired hC hf
          change C.next dj es[j] = some (some d) at ha
          rw [List.take_add_one, hget, Option.toList_some, List.countP_append,
            hstep dj _ d hi hev ha, ih dj hτ]
          simp [List.countP_cons]
          omega
      · rw [hτ] at ha; cases ha
    · have h1 : es.take (j + 1) = es.take j := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [h1] at ha ⊢
      exact ih d ha

end

/-- `shape_cases x … at hev hn unfolding [shape] trans [lemmas]`: the steps of a site machine by
the shape of their event. The site variables `x …` (of a site type, `Fin`, `Bool` or an
enumeration) are split into all their values. At each, the shape hypothesis `hev : Ev d e` is
unfolded with `shape` and destructed: the event's kind (a variable; the event is destructed into
its position and kind first) is fixed and the shape's remaining facts are named `hev`. The
transition `hn : next d e = some (some d')` is evaluated with the role's transition lemmas and
split on its conditions, and the successor and the variables the conditions fix are substituted.
Cases whose transition is not a step are closed. -/
syntax "shape_cases " (ident)* " at " ident ident
  " unfolding " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
elab_rules : tactic
  | `(tactic| shape_cases $xs* at $hev $hn unfolding [$us,*] trans [$ls,*]) => do
    let fvs ← withMainContext do
      xs.toList.mapM fun x => do return (← getLocalDeclFromUserName x.getId).fvarId
    let gs ← splitSites (← getMainGoal) fvs
    setGoals gs
    evalTactic (← `(tactic| (
      all_goals try dsimp only [Fin.reduceFinMk, Fin.isValue] at *
      all_goals simp only [$us,*] at $hev:ident
      all_goals repeat' first
        | (obtain rfl := $hev:ident)
        | (obtain ⟨rfl, $hev:ident⟩ := $hev:ident)
        | (obtain ⟨_, $hev:ident⟩ := $hev:ident)
      all_goals simp only [$ls,*] at $hn:ident
      all_goals repeat' split at $hn:ident
      all_goals try simp only [Option.some.injEq, reduceCtorEq] at $hn:ident
      all_goals try subst $hn:ident
      all_goals try simp only [Bool.not_eq_true] at *
      all_goals try subst_vars)))

end PTX.Flow
