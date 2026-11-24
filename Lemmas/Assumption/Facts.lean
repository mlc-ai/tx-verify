-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal
public import Assumption.ApproxExact
public import Assumption.ClusterScopeMbar
public import Lemmas.Flow.Hooks
public import Lemmas.Isa.Rule

@[expose] public section

/-! # Facts about the assumption constructors of `Assumption/`

A proof tool. The ideal-real, approximate-as-exact and cluster-scope constructors add no execution
conditions and no undefined behaviour, and select no site of the other hooks (segments, implicit
`wait::ld`, commit order); a scoped ideal-real assumption at the head of a list decides the local
rule of the forms it names where the ideal rule applies (`execLocalA_idealReal`, `IdealFor`) and
leaves every other operation, and an operation whose operands make the ideal rule decline, to the
rest of the list; every successful floating MMA evaluation of a `kind::f16` kind it names is a
`.float output` value (`TcMma.eval_f16`). -/

namespace PTX.Assumption
open PTX

variable {name why : String}

@[simp] theorem idealReal_wf {s : IdealScope} (L : Launch) (mem0 : Mem0) (X : Execution) :
    (idealReal name s why).wf L mem0 X := trivial
@[simp] theorem idealReal_ub {s : IdealScope} (L : Launch) (mem0 : Mem0) (X : Execution) :
    ¬ (idealReal name s why).ub L mem0 X := not_false
@[simp] theorem idealReal_clusterScopeMbar {s : IdealScope} (pc : Nat) :
    (idealReal name s why).clusterScopeMbar pc = false := rfl
@[simp] theorem idealReal_ncLoads {s : IdealScope} (pc : Nat) :
    (idealReal name s why).ncLoads pc = false := rfl
@[simp] theorem approxExact_wf {fs : List ApproxForm} (L : Launch) (mem0 : Mem0)
    (X : Execution) : (approxExact name fs why).wf L mem0 X := trivial
@[simp] theorem approxExact_ub {fs : List ApproxForm} (L : Launch) (mem0 : Mem0)
    (X : Execution) : ¬ (approxExact name fs why).ub L mem0 X := not_false
@[simp] theorem approxExact_clusterScopeMbar {fs : List ApproxForm} (pc : Nat) :
    (approxExact name fs why).clusterScopeMbar pc = false := rfl
@[simp] theorem approxExact_ncLoads {fs : List ApproxForm} (pc : Nat) :
    (approxExact name fs why).ncLoads pc = false := rfl

/-! The constructors that do not use a hook leave it at its default. -/

@[simp] theorem idealReal_segmentRule {s : IdealScope} :
    (idealReal name s why).segmentRule = fun _ _ _ => none := rfl
@[simp] theorem idealReal_tcLdWait {s : IdealScope} (pc : Nat) :
    (idealReal name s why).tcLdWait pc = false := rfl
@[simp] theorem idealReal_commitInOrder {s : IdealScope} (pc : Nat) :
    (idealReal name s why).commitInOrder pc = false := rfl
@[simp] theorem approxExact_segmentRule {fs : List ApproxForm} :
    (approxExact name fs why).segmentRule = fun _ _ _ => none := rfl
@[simp] theorem approxExact_tcLdWait {fs : List ApproxForm} (pc : Nat) :
    (approxExact name fs why).tcLdWait pc = false := rfl
@[simp] theorem approxExact_commitInOrder {fs : List ApproxForm} (pc : Nat) :
    (approxExact name fs why).commitInOrder pc = false := rfl
@[simp] theorem clusterScopeMbarAt_segmentRule {sites : List Nat} :
    (clusterScopeMbarAt name sites why).segmentRule = fun _ _ _ => none := rfl
@[simp] theorem clusterScopeMbarAt_tcLdWait {sites : List Nat} (pc : Nat) :
    (clusterScopeMbarAt name sites why).tcLdWait pc = false := rfl
@[simp] theorem clusterScopeMbarAt_commitInOrder {sites : List Nat} (pc : Nat) :
    (clusterScopeMbarAt name sites why).commitInOrder pc = false := rfl

@[simp] theorem clusterScopeMbarAt_wf {sites : List Nat} (L : Launch) (mem0 : Mem0)
    (X : Execution) : (clusterScopeMbarAt name sites why).wf L mem0 X := trivial
@[simp] theorem clusterScopeMbarAt_ub {sites : List Nat} (L : Launch) (mem0 : Mem0)
    (X : Execution) : ¬ (clusterScopeMbarAt name sites why).ub L mem0 X := not_false

/-- A form the ideal-real assumption names is executed by the ideal rule. -/
theorem idealReal_localRule_of {s : IdealScope} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {f : FloatForm} (hf : FloatForm.ofOp op = some f) (hs : f ∈ s.float) :
    (idealReal name s why).localRule L g t op = execIdealFloat L g t op := by
  simp [idealReal, hf, hs]

/-- An operation that is no form the ideal-real assumption names gets no rule from it. -/
theorem idealReal_localRule_none {s : IdealScope} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (h : ∀ f, FloatForm.ofOp op = some f → f ∉ s.float) :
    (idealReal name s why).localRule L g t op = none := by
  simp only [idealReal]
  cases hf : FloatForm.ofOp op with
  | none => rfl
  | some f => simp [h f hf]

/-- A form the approximate-as-exact assumption names is executed by its exact function. -/
theorem approxExact_localRule_of {fs : List ApproxForm} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {f : ApproxForm} (hf : ApproxForm.ofOp op = some f) (hs : f ∈ fs) :
    (approxExact name fs why).localRule L g t op = execApproxExact t op := by
  simp [approxExact, hf, hs]

/-- An operation that is no form the approximate-as-exact assumption names gets no rule from
it. -/
theorem approxExact_localRule_none {fs : List ApproxForm} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (h : ∀ f, ApproxForm.ofOp op = some f → f ∉ fs) :
    (approxExact name fs why).localRule L g t op = none := by
  simp only [approxExact]
  cases hf : ApproxForm.ofOp op with
  | none => rfl
  | some f => simp [h f hf]

/-- A head ideal-real assumption decides the local rule of a form it names, when no assumption
of the list takes a segment at the state and the ideal rule does not decline the operands. -/
theorem execLocalA_idealReal {s : IdealScope} {A' : List Assumption} {L : Launch} {g : Nat}
    {t : TState} {op : Op} {f : FloatForm} (hf : FloatForm.ofOp op = some f)
    (hs : f ∈ s.float) (hA' : SegFreePc A' t.pc := by seg_free) {e : Exec TState}
    (he : execIdealFloat L g t op = some e) :
    execLocalA (idealReal name s why :: A') L g t op = e := by
  have hA : SegFreeAt (idealReal name s why :: A') L g t := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rfl
    · exact hA' a ha L g t rfl
  rw [hA.exec]
  simp only [execLocalRule, List.findSome?_cons, idealReal_localRule_of hf hs, he]

/-- `A` reads the floating form `f` as exact real arithmetic: where the ideal rule applies, the
local step is its outcome (an operand that makes it decline, a NaN or `∞ - ∞` or `0 · ∞`, keeps
the core rule). -/
def IdealFor (A : List Assumption) (f : FloatForm) : Prop :=
  ∀ L g t op, FloatForm.ofOp op = some f → ∀ e, execIdealFloat L g t op = some e →
    execLocalA A L g t op = e

/-- A head ideal-real assumption reads every form it names as exact real arithmetic, when no
assumption of the list takes a segment. -/
theorem idealFor_head {s : IdealScope} {A' : List Assumption} {f : FloatForm}
    (hs : f ∈ s.float) (hA' : NoSegments A' := by hooks_off) :
    IdealFor (idealReal name s why :: A') f :=
  fun _ _ _ _ hf _ he => execLocalA_idealReal hf hs hA'.segFreePc he

/-- `A` reads the floating form `f` as exact real arithmetic at the state `t`. -/
def IdealAt (A : List Assumption) (f : FloatForm) (L : Launch) (g : Nat) (t : TState) : Prop :=
  ∀ op, FloatForm.ofOp op = some f → ∀ e, execIdealFloat L g t op = some e →
    execLocalA A L g t op = e

theorem IdealFor.at {A : List Assumption} {f : FloatForm} (h : IdealFor A f) {L : Launch}
    {g : Nat} {t : TState} : IdealAt A f L g t :=
  fun op hf e he => h L g t op hf e he

/-- A head ideal-real assumption reads every form it names as exact real arithmetic at a state
where no assumption of the list takes a segment. -/
theorem idealAt_head {s : IdealScope} {A' : List Assumption} {f : FloatForm} {L : Launch}
    {g : Nat} {t : TState} (hs : f ∈ s.float) (hA' : SegFreePc A' t.pc := by seg_free) :
    IdealAt (idealReal name s why :: A') f L g t :=
  fun _ hf _ he => execLocalA_idealReal hf hs hA' he

/-- `A` leaves an operation of the floating form `f` whose operands make the ideal rule decline (a
NaN, `∞ - ∞` or `0 · ∞`) to the Core rule. -/
def DeclineCore (A : List Assumption) (f : FloatForm) : Prop :=
  ∀ L g t op, FloatForm.ofOp op = some f → execIdealFloat L g t op = none →
    execLocalA A L g t op = execLocal L g t op

/-- A head ideal-real assumption leaves a declined operation to the Core rule, when no assumption
of the list takes a segment or names the form. -/
theorem declineCore_head {s : IdealScope} {A' : List Assumption} {f : FloatForm}
    (hL : ∀ a ∈ A', ∀ L g t op, FloatForm.ofOp op = some f → a.localRule L g t op = none)
    (hA' : NoSegments A' := by hooks_off) :
    DeclineCore (idealReal name s why :: A') f := by
  intro L g t op hf hn
  have hS : SegFreeAt (idealReal name s why :: A') L g t := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rfl
    · exact hA' a ha L g t
  rw [hS.exec, execLocalRule_of_none]
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp only [idealReal, hf]
    split_ifs
    · exact hn
    · rfl
  · exact hL a ha L g t op hf

end PTX.Assumption

namespace PTX.TcMma
open PTX

/-- **An ideal `kind::f16` MMA result is a float of its output format.** -/
theorem eval_f16 {name why : String} {s : Assumption.IdealScope} {rest : List Assumption}
    {d : Descriptor} {input output : FloatFmt}
    (hk : d.kind = .f16 input output) (hs : d.kind ∈ s.mma) {acc : Bool}
    {a b : List (Option Byte)} {old : Option Value} {row col : Nat} {v : Value}
    (h : eval (Assumption.idealReal name s why :: rest) d acc a b old row col = .ok v) :
    ∃ r, v = .float output r := by
  have hr : (Assumption.idealReal name s why).mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumption.idealReal, hs]
  simp only [eval, hk, List.findSome?, hr, Option.getD_some, Assumption.execIdealMma] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨_, rfl⟩) | cases h

end PTX.TcMma
