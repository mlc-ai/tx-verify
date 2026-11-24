-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Tmpl
public import Lemmas.Flow.Async
public import Lemmas.Flow.Widen
public import Lemmas.Flow.Footprint

@[expose] public section

/-! # Continuations of a step

The continuation of a step of the machine: a concrete state of the successor, reached by local
steps, or a dead state where the machine stops. A concrete state of an abstract state without a
pending vector element is a state `At` its site's program counter with its facts (`atD_of`).
The value-table reduction (`rms_values`) closes a segment's equations. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The continuation of a step: a concrete state of the successor, or a dead state where the
machine stops. -/
abbrev Cont (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  (∃ d' t', next P g d e = some (some d') ∧ Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧
      (code P L g).AtD d' t' ∧ Inv P g d') ∨
    (next P g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u)

/-- A concrete state of an abstract state without a pending vector element. -/
theorem atD_of {d : D} {t : TState} (hs : d.sub = 0) (ha : d.acc = [])
    (h : At t d.site.pc (facts P g d)) : (code P L g).AtD d t :=
  ⟨h.1, by rw [h.2.1]; exact hs.symm, by rw [h.2.2.1]; exact ha.symm, h.2.2.2.1, h.2.2.2.2⟩

theorem at_of_atD {d : D} {t : TState} (hs : d.sub = 0) (ha : d.acc = [])
    (h : (code P L g).AtD d t) : At t d.site.pc (facts P g d) :=
  ⟨h.1, h.2.1.trans hs, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩

/-- No register is live at the exit. -/
theorem holds_exit {R : Nat → Option Value} {d : D} (hs : d.site = .exit) : Holds R (facts P g d) :=
    by
  show Holds R (factsFrom (Flow.live d.site.pc) _)
  rw [hs, show Flow.live Site.exit.pc = [] by table_decide]
  trivial

/-- The launch's bounds, in the context of a segment's proof (for `omega`). -/
macro "rms_hyps" hpre:term : tactic => `(tactic| (
  have := ($hpre).hyp.block; have := ($hpre).hyp.shared; have := ($hpre).hyp.batch
  have := ($hpre).hyp.sharedEnd; have := ($hpre).hyp.sharedAlign; have := ($hpre).hyp.inEnd
  have := ($hpre).hyp.outEnd; have := ($hpre).hyp.wEnd; have := ($hpre).hyp.inAlign
  have := ($hpre).hyp.outAlign; have := ($hpre).hyp.wAlign))

/-- The invariant of a successor, field by field: `simp` with the site's predicates, then
`omega`. -/
macro "inv_tac" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ <;>
    (try simp_all [Site.vec, Site.vload, Site.inRow, row, b32, Value.bytes]) <;> omega))

/-- The value-table reduction used after evaluating a segment. -/
macro "rms_values" : tactic =>
  `(tactic| simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

end
end PTX.Kernels.RmsNorm.Proof
