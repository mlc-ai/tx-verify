-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProANext
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The conclusion of a step and the generic parts of the step lemmas

`Step L g d e u` is what an event `e` at state `d`, after which the thread is in `u`, owes: the
machine leaves it (`some none`), or the thread reaches by local steps a concrete state of the
successor `d'`, which satisfies the invariant. The step lemmas of the sites state their facts at
the program counter after the event (`at_next_live`, `at_load`, `at_elect`) and continue with the
local segments of `ProASeg*`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A concrete state of the abstract state `d`: its program counter, sub-step, accumulator and
register facts. -/
def AtS (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = sub d ∧ t.acc = acc d ∧ t.fault = none ∧ Holds t.regs (facts L g d)

/-- The conclusion of a step. -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ AtS L g d' t' ∧ Inv L g d'

variable {L : Launch} {g : Nat} {d d' : D} {t u : TState} {e : Event} {ins : Instr}

/-- A step that continues by a local segment from the facts `F` at `pc` to the successor's. -/
theorem step_of_seg {pc : Nat} {F : List (Nat × Value)}
    (hn : next L g d e = some (some d')) (hi : Inv L g d') (hs0 : sub d' = 0)
    (hU : At u pc F)
    (hs : ∃ n, Seg kernel asms L g n pc F d'.site.pc (facts L g d')) : Step L g d e u := by
  obtain ⟨n, hs⟩ := hs
  obtain ⟨t', hr, ht'⟩ := hs u hU
  exact .inr ⟨d', t', hn, run_rtg hr,
    ⟨ht'.1, hs0 ▸ ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩, hi⟩

/-- The facts after an instruction that writes no register. -/
theorem at_next_live {pc : Nat} {dt : Dat} (h : At t pc (factsAt L g pc dt))
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ Flow.live pc) :
    At (PTX.next t) (pc + 1) (factsAt L g (pc + 1) dt) :=
  (At.next h).mono (holds_factsFrom_mono h.2.2.2.2 hl)

/-! ### Conditional branches on a predicate register

A `@p bra` (taken when `p` holds) or `@!p bra` (taken when it does not) reads the predicate's
fact; every register live at the target is live at the branch. -/

theorem run_bra_at {pc target p : Nat} {neg uni : Bool} {dt : Dat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, neg), .bra target uni⟩)
    (hp : valueOf L g dt p = .pred pick) (hl : p ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc) (t : TState) (h : At t pc (factsAt L g pc dt)) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (if (pick != neg) then target else pc + 1) (factsAt L g pc dt) := by
  have hr : t.regs p = some (.pred pick) := hp ▸ holds_mem h.2.2.2.2 (mem_factsFrom hl)
  cases neg with
  | false =>
    cases pick with
    | true =>
      refine ⟨{ t with pc := target }, ?_, rfl, h.2⟩
      simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hr, bind, Except.bind,
        pure, Except.pure, (Assumption.SegFreePc.of_eq h.1 hsf).exec,
        execLocalRule_of_none (asms_localRule_bra (t := t)), execLocal, Op.rule, execBranch,
        Op.isLocal]
    | false =>
      refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
      simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hr, bind, Except.bind,
        pure, Except.pure]
  | true =>
    cases pick with
    | false =>
      refine ⟨{ t with pc := target }, ?_, rfl, h.2⟩
      simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hr, bind, Except.bind,
        pure, Except.pure, (Assumption.SegFreePc.of_eq h.1 hsf).exec,
        execLocalRule_of_none (asms_localRule_bra (t := t)), execLocal, Op.rule, execBranch,
        Op.isLocal]
    | true =>
      refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
      simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hr, bind, Except.bind,
        pure, Except.pure]

/-- The branch is taken: one step to the target. -/
theorem seg_bra_taken {pc target p : Nat} {neg uni : Bool} {dt : Dat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, neg), .bra target uni⟩)
    (hp : valueOf L g dt p = .pred pick) (hl : p ∈ Flow.live pc) (hpick : (pick != neg) = true)
    (hlive : ∀ r ∈ Flow.live target, r ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc := by asms_free) :
    Seg kernel asms L g 1 pc (factsAt L g pc dt) target (factsAt L g target dt) := by
  intro t h
  obtain ⟨u, hr, hu⟩ := run_bra_at hc hp hl hsf t h
  rw [hpick] at hu
  exact ⟨u, hr, hu.mono (holds_factsFrom_mono hu.2.2.2.2 hlive)⟩

/-- The branch is not taken: one step to the next instruction. -/
theorem seg_bra_fall {pc target p : Nat} {neg uni : Bool} {dt : Dat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, neg), .bra target uni⟩)
    (hp : valueOf L g dt p = .pred pick) (hl : p ∈ Flow.live pc) (hpick : (pick != neg) = false)
    (hlive : ∀ r ∈ Flow.live (pc + 1), r ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc := by asms_free) :
    Seg kernel asms L g 1 pc (factsAt L g pc dt) (pc + 1) (factsAt L g (pc + 1) dt) := by
  intro t h
  obtain ⟨u, hr, hu⟩ := run_bra_at hc hp hl hsf t h
  rw [hpick] at hu
  exact ⟨u, hr, hu.mono (holds_factsFrom_mono hu.2.2.2.2 hlive)⟩

/-- A register's value in the facts of a program counter where it is live. -/
theorem mem_facts {pc r : Nat} {dt : Dat} {v : Value} (hl : r ∈ Flow.live pc)
    (hv : valueOf L g dt r = v) : (r, v) ∈ factsAt L g pc dt :=
  hv ▸ Flow.mem_factsFrom hl

/-- Two explicit facts that the table's facts hold, in front of them. -/
theorem at_ex2 {pc r1 r2 : Nat} {dt : Dat} {v1 v2 : Value} (h : At t pc (factsAt L g pc dt))
    (h1 : (r1, v1) ∈ factsAt L g pc dt) (h2 : (r2, v2) ∈ factsAt L g pc dt) :
    At t pc ((r1, v1) :: (r2, v2) :: factsAt L g pc dt) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_mem h.2.2.2.2 h1, holds_mem h.2.2.2.2 h2,
    h.2.2.2.2⟩

theorem AtS.at (h : AtS L g d t) (hs : sub d = 0) (ha : acc d = []) :
    At t d.site.pc (facts L g d) :=
  ⟨h.1, hs ▸ h.2.1, ha ▸ h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The invariant at another site, with other data of the same inherited registers. -/
theorem Inv.mv {s : Site} {dt : Dat} (hi : Inv L g ⟨s, dt⟩) (s' : Site) (dt' : Dat)
    (hp : dt'.pro = dt.pro)
    (hg : guardVal L g dt' s' = true) (hq : ∀ j, s'.qIdx ≤ j → dt'.q j = qZero)
    (hb : ∀ j, (dt'.q j).bytes = 2) : Inv L g ⟨s', dt'⟩ :=
  ⟨hp ▸ hi.args, hg, hq, hb⟩

/-- The invariant's lower bound on the query values, from a site of a smaller index. -/
macro "qle " h:term:max : term => `(le_trans (by dsimp only; decide) $h)

/-- The index of a site bounds the queries it is at (`hj : Site.qIdx ≤ j` as a number). -/
macro "qlt " h:ident : term => `(by simp only [Site.qIdx] at $h:ident; omega)

/-- The query values from index 0 are zero at a site whose index is 0. -/
macro "qz0 " hi:term:max : term => `(fun j _ => ($hi).qz j (by simp [Site.qIdx]))

/-- The invariant at the successor site when the data keep their query values and inherited
registers, and the words are `WordsOk` where the site needs them (from the old site, or none). -/
macro "inv_to " hi:term:max : term =>
  `(Inv.mv $hi _ _ rfl
    (by first | rfl | assumption)
    (fun j hj => ($hi).qz j (le_trans (by dsimp only; decide) hj)) ($hi).qb)

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
