-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Flow.SegFree

@[expose] public section

/-! # One instruction's step, proved once per program counter

A proof tool for the segments of site machines. A state's local step (`out`) first reads the
instruction at the state's `pc` from the code, evaluates its guard and asks every assumption for a
segment, and only then runs the instruction's local rule (`execLocalRule`: an assumption's rule
for it, else Core's). A segment proof by evaluation (`seg_fp`) repeats all of it for every
instruction of every segment.

`PcLocal K A L g pc ins` states, for one program counter, that a state at `pc` without a fault
steps by `stepIns` of the literal instruction `ins` (its guard, then its local rule): the
instruction at `pc` is `ins`, local, and no assumption of `A` takes a segment there. A generator
(`Tools/step_gen.py`) reads the decoded program and writes one such lemma per local instruction
(`step_<pc>`), proved once from the code lemma `code_<pc>` (`PcLocal.of_code`).

A segment is then a chain of steps (`run_succ_local`): each step is the lemma of its `pc` and
`stepIns` evaluated on the state, `stepIns A L g t ins = some t'`; the code and the assumptions'
segments are no longer read. `seg_fp` builds this chain when every program counter of a piece has
its lemma (`Flow.step_<pc>` next to the kernel's `Flow.code_<pc>`), and evaluates the piece as
before otherwise. -/

namespace PTX.Flow
open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The local step of the instruction `ins` at a state, without reading the code or asking for a
segment: a guard that fails skips it, one that holds runs its local rule. -/
def stepIns (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (ins : Instr) :
    Option TState :=
  match guardHolds t ins.guard with
  | .error _ => none
  | .ok false => some (skip t)
  | .ok true => (execLocalRule A L g t ins.op).toOption

/-- The instruction at `pc` is the local `ins`, and no assumption of `A` takes a segment at `pc`: a
state at `pc` without a fault steps by `stepIns`. -/
def PcLocal (K : Kernel) (A : List Assumption) (L : Launch) (g pc : Nat) (ins : Instr) : Prop :=
  ∀ t : TState, t.pc = pc → t.fault = none → tauStep K A L g t = stepIns A L g t ins

/-- **A step lemma from the code lemma**: the instruction, its locality, and no segment at
`pc`. -/
theorem PcLocal.of_code {pc : Nat} {ins : Instr} (hc : K.code[pc]? = some ins)
    (hl : ins.op.isLocal = true) (hs : Assumption.SegFreePc A pc) : PcLocal K A L g pc ins := by
  intro t ht hf
  simp only [tauStep, out, hf, ht, hc, stepIns]
  rcases guardHolds t ins.guard with e | (_ | _)
  · rfl
  · rfl
  · simp only [hl, ↓reduceIte, hs.exec ht]
    cases execLocalRule A L g t ins.op <;> rfl

/-- **A step of a segment by its program counter's lemma**: the state at the lemma's `pc`, without
a fault, steps to `t'` when `stepIns` gives `t'`. -/
theorem run_succ_local {pc n : Nat} {ins : Instr} {t t' u : TState} (h : PcLocal K A L g pc ins)
    (hpc : t.pc = pc) (hf : t.fault = none) (he : stepIns A L g t ins = some t')
    (hr : run K A L g n t' = some u) : run K A L g (n + 1) t = some u := by
  simp only [run, h t hpc hf, he, Option.bind_some, hr]

end
end PTX.Flow
