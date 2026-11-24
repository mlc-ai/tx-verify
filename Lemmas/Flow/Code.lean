-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine
public import Lemmas.Flow.Regs
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # Site machines read off the code

A proof tool. Most abstract states of a thread are "about to execute the event
instruction at `pc d`, with register facts `facts d`". For such states the template is
the instruction's own `eventTmpl`, so `out` agrees with it by one generic argument
(`site_out`), and a kernel supplies only:

* `site`: the instruction at `pc d` performs an event and its guard holds by the facts;
* `step`: after the event fires, local steps reach a concrete state of the successor.

The abstract state `none` is any state that performs an event: a machine uses it after
events whose continuation it does not follow (a value that only another thread's behaviour
determines), leaving those cases to facts about the whole execution. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

/-- Abstract states described by a program counter and register facts. -/
structure Code (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) where
  D : Type
  init : D
  pc : D → Nat
  facts : D → List (Nat × Value)
  /-- The sub-step and accumulator: nonzero only between the events of one instruction. -/
  sub : D → Nat := fun _ => 0
  acc : D → List Value := fun _ => []
  inv : D → Prop
  /-- Successor after event `e`: `some none` is a pending fault. -/
  next : D → Event → Option (Option D)

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} (C : Code K A L g)

/-- A concrete state of the abstract state `d`. With the default `sub` and `acc` this is
`At t (C.pc d) (C.facts d)`. -/
def AtD (d : C.D) (t : TState) : Prop :=
  t.pc = C.pc d ∧ t.sub = C.sub d ∧ t.acc = C.acc d ∧ t.fault = none ∧ Holds t.regs (C.facts d)

/-- The guard of an instruction holds whenever the facts hold. -/
def GuardTrue (F : List (Nat × Value)) : Option (Nat × Bool) → Prop
  | none => True
  | some (p, neg) => (p, Value.pred (!neg)) ∈ F

def Good : Option C.D → TState → Prop
  | none, t => ∃ m, out K A L g t = .ev m
  | some d, t => C.AtD d t ∧ C.inv d

def tmpl : Option C.D → TState → Tmpl
  | none, t => match out K A L g t with
    | .ev m => m
    | .tau _ => .ub .noRule
  | some d, t => match K.code[C.pc d]? with
    | some ins => eventTmpl A L g t ins.op
    | none => .ub .pcOutOfRange

def toMachine : Machine K A L g where
  St := Option C.D
  init := some C.init
  Good := C.Good
  tmpl := C.tmpl
  next := fun σ e => match σ with
    | none => some none
    | some d => C.next d e

/-- The obligations of one abstract state: it sits at an event instruction whose guard
holds, and every continuing event reaches a concrete state of its successor, or a dead
state, where the machine stops. -/
structure StepAt (d : C.D) : Prop where
  site : C.inv d → ∃ ins, K.code[C.pc d]? = some ins ∧ ins.op.isLocal = false ∧
    GuardTrue (C.facts d) ins.guard
  step : ∀ {t e u} ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
    Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) →
    (C.next d e = some none ∨
      ∃ d' t', C.next d e = some (some d') ∧ Relation.ReflTransGen (Tau K A L g) u t' ∧
        C.Good (some d') t') ∨
    (C.next d e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u)

/-- The obligations of a code machine. Role files prove `StepAt` for their own states. -/
structure Sound : Prop where
  start : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ C.AtD C.init t ∧
    C.inv C.init
  steps : ∀ d, C.StepAt d

variable {C}


theorem guardHolds_of {t : TState} {F : List (Nat × Value)} {gd : Option (Nat × Bool)}
    (hF : Holds t.regs F) (h : GuardTrue F gd) : guardHolds t gd = .ok true := by
  cases gd with
  | none => rfl
  | some pn =>
    obtain ⟨p, neg⟩ := pn
    have hr := holds_mem hF h
    simp [guardHolds, readReg, hr, bind, Except.bind, pure, Except.pure]

theorem site_out_steps (hS : ∀ d, C.StepAt d) {d : C.D} {t : TState} (h : C.Good (some d) t) :
    out K A L g t = .ev (C.tmpl (some d) t) := by
  obtain ⟨ha, hinv⟩ := h
  obtain ⟨ins, hc, hl, hg⟩ := (hS d).site hinv
  have hc' : K.code[t.pc]? = some ins := by rw [ha.1]; exact hc
  rw [out_event ha.2.2.2.1 hc' (guardHolds_of ha.2.2.2.2 hg) hl]
  simp only [tmpl, hc]

theorem site_out (hC : C.Sound) {d : C.D} {t : TState} (h : C.Good (some d) t) :
    out K A L g t = .ev (C.tmpl (some d) t) :=
  site_out_steps hC.steps h

theorem out_eq_steps (hS : ∀ d, C.StepAt d) {σ : Option C.D} {t : TState} (h : C.Good σ t) :
    out K A L g t = .ev (C.tmpl σ t) := by
  cases σ with
  | none =>
    obtain ⟨m, hm⟩ := h
    show out K A L g t = .ev (C.tmpl none t)
    simp only [tmpl, hm]
  | some d => exact site_out_steps hS h

theorem out_eq_of (hC : C.Sound) {σ : Option C.D} {t : TState} (h : C.Good σ t) :
    out K A L g t = .ev (C.tmpl σ t) :=
  out_eq_steps hC.steps h

/-- The step obligation of the machine of a code machine, from the states' obligations. -/
theorem machine_step (hS : ∀ d, C.StepAt d) {σ : Option C.D} {t : TState} {e : Event}
    {u : TState} (h : C.Good σ t) (hf : Fires t.pc (C.tmpl σ t) e (some u)) :
    (∃ σ', C.toMachine.next σ e = some σ' ∧ C.toMachine.Reach σ' u) ∨
      (C.toMachine.next σ e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u) := by
  cases σ with
  | none => exact .inl ⟨none, rfl, fun t1 _ hs => hs⟩
  | some d =>
    obtain ⟨ha, hinv⟩ := h
    obtain ⟨ins, hc, -, -⟩ := (hS d).site hinv
    change Fires t.pc (C.tmpl (some d) t) e (some u) at hf
    simp only [tmpl, hc, ha.1] at hf
    rcases (hS d).step ins ha hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
    · exact .inl ⟨none, by simp [toMachine, hn], fun t1 _ hs => hs⟩
    · exact .inl ⟨some d', by simp [toMachine, hn],
        Machine.reach_of (M := C.toMachine) (fun h => out_eq_steps hS h) hl hg⟩
    · exact .inr ⟨by simp [toMachine, hn], hd⟩

theorem Sound.machine (hC : C.Sound) : C.toMachine.Sound where
  start := by
    obtain ⟨t, hl, ha, hi⟩ := hC.start
    exact ⟨t, hl, ha, hi⟩
  out_eq := fun h => out_eq_of hC h
  step := fun h hf => machine_step hC.steps h hf

/-- **A run from a state whose local steps reach a concrete state of `σ` is a run of the
machine from `σ`**, by the states' obligations alone: a role machine that starts after other
events of its thread (a prologue's) is followed from the hand-off. -/
theorem trace_from_steps (hS : ∀ d, C.StepAt d) {σ : Option C.D} {t u : TState}
    (hl : Relation.ReflTransGen (Tau K A L g) t u) (hg : C.Good σ u) {es : List Event}
    {o : Option TState} (hr : Run K A L g t es o) : C.toMachine.Trace σ es :=
  Machine.trace_from_of (M := C.toMachine) (fun h => out_eq_steps hS h)
    (fun h hf => machine_step hS h hf)
    (Machine.reach_of (M := C.toMachine) (fun h => out_eq_steps hS h) hl hg) hr

end Code
end
end PTX.Flow
