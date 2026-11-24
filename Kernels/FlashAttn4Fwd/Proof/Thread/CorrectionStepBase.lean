-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Correction
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Async
public import Lemmas.Flow.Bar
public import Lemmas.Flow.Next
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of the correction warps' step lemmas: the conclusion of a step
(`Step`), its construction from a run to a state at an instruction's first sub-step
(`step_of_run`), and the segment tactic `corr_seg`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The conclusion of a step of this role, for any assumption list: the thread leaves the
role, steps to `d'` at a concrete state of it reached by local steps, or is dead. -/
def Step (A : List Assumption) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) :
    Prop :=
  (next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel A L g) u t' ∧
    (t'.pc = d'.site.pc ∧ t'.sub = d'.site.sub ∧ t'.acc = [] ∧ t'.fault = none ∧
      Holds t'.regs (facts L g d')) ∧ Inv L g d') ∨
  (next L g d e = none ∧ Machine.Dead (K := kernel) (A := A) (L := L) (g := g) u)

/-- A step whose event continues at `u` and whose segment from `u` reaches `d'`, a state at
the first sub-step of its instruction. -/
theorem step_of_run {A : List Assumption} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    {u : TState} (hn : next L g d e = some (some d')) (hi : Inv L g d')
    (hsub : d'.site.sub = 0)
    (hr : ∃ k t', run kernel A L g k u = some t' ∧ At t' d'.site.pc (facts L g d')) :
    Step A L g d e u := by
  obtain ⟨k, t', hr, ht'⟩ := hr
  exact .inl (.inr ⟨d', t', hn, run_rtg hr,
    ⟨ht'.1, ht'.2.1.trans hsub.symm, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩, hi⟩)

/-- The invariant of a state whose item, trip and readings are those of an invariant state,
at a site of the same kind. -/
theorem inv_same {L : Launch} {g : Nat} {d : D} (s : Site) (hi : Inv L g d)
    (hit : s.inItem = d.site.inItem) (hpre : s.inItem = true ∨ d.i = items L g ∨
      d.i = 0 ∧ (s = .setMaxReg ∨ s = .bar0 ∨ ∃ st, s = .free st))
    (htr : s.inTrip = true → d.site.inTrip = true)
    (hal : s.rescale = true → d.site.rescale = true)
    (hst : (s = .setMaxReg ∨ s = .bar0 ∨ ∃ st, s = .free st) →
      d.site = .setMaxReg ∨ d.site = .bar0 ∨ ∃ st, d.site = .free st) :
    Inv L g { d with site := s } where
  item h := hi.item (hit ▸ h)
  tail h h1 h2 h3 := by
    rcases hpre with hp | hp | ⟨_, hp⟩
    · simp_all
    · exact hp
    · rcases hp with rfl | rfl | ⟨st, rfl⟩
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact absurd rfl (h3 st)
  start h := hi.start (hst h)
  trip h := hi.trip (htr h)
  alpha h := hi.alpha (hal h)

/-- The value of `r` in state `d`, with the registers of `ex` valued as given (predicates
and intermediate values at a checkpoint inside a segment). -/
def valueX (L : Launch) (g : Nat) (d : D) (ex : List (Nat × Value)) (r : Nat) : Value :=
  (ex.lookup r).getD (valueOf L g d r)

/-- The facts at `pc` under `valueX`. -/
def factsX (L : Launch) (g pc : Nat) (d : D) (ex : List (Nat × Value)) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueX L g d ex)

/-- Evaluate a correction segment from `h` and close the facts of its end state: by unfolding
the code's terms (`rfl`) or the normal form of integer values (shared addresses, bounded by
`Pre.sharedRange`). -/
syntax "corr_seg" term:max term:max : tactic
macro_rules
  | `(tactic| corr_seg $h $hpre) => `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [valueX, valueOf, values, chunkValues, loadValues, fcPair, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none]
        all_goals first
          | seg_close [neg32]
          | (simp only [fl, joinValue]; done)))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
