-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerSound
public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # The idle role

A worker whose role byte is 2 (warps 4 and 5) is sent by `brx.idx` to pc 2333. It lowers its
register budget (`setmaxnreg.dec 24`), waits twice at the named barrier 1 (pc 2334, 2335: the
default partition's two barrier arrivals that bracket its write of the role table), raises the
budget again (`setmaxnreg.inc 256`, pc 2336) and falls into the dispatch loop's head (pc 2337),
which is `Worker.Site.loop`. So the role's machine ends at its last event (the successor of
`inc` is `some none`); `stepAt` is proved by `site_cases`, and `return_loop` turns the facts
after it into the worker's facts at the loop. `entry` turns the worker's facts at the idle entry
into the role's first state.

The role reads and writes no register: its registers are the worker's (`Worker.valueOf`), so
a state is the site and the inherited registers `P`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker.Idle
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)
open PTX.Kernels.InklingRelDecode.Proof.Worker (asms valueOf)

noncomputable section
set_option maxRecDepth 100000

/-- The event instructions of the idle role. -/
inductive Site where
  | dec | bar0 | bar1 | inc
  deriving DecidableEq

def Site.pc : Site → Nat
  | .dec => Flow.setMaxReg_2
  | .bar0 => Flow.bar_25
  | .bar1 => Flow.bar_26
  | .inc => Flow.setMaxReg_3

/-- An idle state: the next event and the inherited registers. -/
structure D where
  site : Site
  P : Pro

/-- The first state of the role. -/
def D.start (P : Pro) : D := ⟨.dec, P⟩

/-- The registers live at `pc`, with the worker's values. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g ⟨.loop, d.P⟩)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- The abstract successor: the next event, and after the last the role ends. -/
def next (d : D) (_ : Event) : Option (Option D) :=
  match d.site with
  | .dec => some (some ⟨.bar0, d.P⟩)
  | .bar0 => some (some ⟨.bar1, d.P⟩)
  | .bar1 => some (some ⟨.inc, d.P⟩)
  | .inc => some none

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The idle role as a code machine, from its `setmaxnreg.dec`. -/
@[reducible] def code (L : Launch) (g : Nat) (P : Pro) : Flow.Code kernel asms L g where
  D := D
  init := D.start P
  pc := (·.site.pc)
  facts := facts L g
  inv := fun _ => True
  next := next

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Every idle state satisfies the code machine's obligation: each site is an unguarded event
that only advances, and after the last one the role ends. -/
theorem stepAt (P : Pro) (d : D) : (code L g P).StepAt d := by
  obtain ⟨s, P'⟩ := d
  site_cases s trans [next] seg_by (intro t h; seg_fp h using first | rfl | fail "idle")
    inv_by (intro _; trivial) guard_by (first | rfl | fail "idle")

/-- **The idle role's entry**: the worker's facts at the role's first instruction are the
role's first state's. -/
theorem entry {P : Pro} {s : TState}
    (h : At s Worker.Site.toIdle.pc (Worker.facts L g ⟨.toIdle, P⟩)) :
    At s Site.dec.pc (facts L g (D.start P)) := h

/-- **The idle role's return**: after its last event (`setmaxnreg.inc 256` at pc 2336, whose
successor is the dispatch loop's head) the thread is at the worker's loop state with the same
inherited registers. -/
theorem return_loop {P : Pro} {s : TState}
    (h : At s (Site.inc.pc + 1) (facts L g ⟨.inc, P⟩)) :
    At s Worker.Site.loop.pc (Worker.facts L g ⟨.loop, Worker.bumpPro P⟩) := by
  rw [Worker.facts_bumpPro_loop]
  refine At.mono h ?_
  have hl : ∀ r ∈ Flow.live Worker.Site.loop.pc, r ∈ Flow.live Site.inc.pc := by
    dsimp only [Worker.Site.pc, Site.pc]
    table_decide
  exact holds_factsFrom_mono h.2.2.2.2 hl

end
end PTX.Kernels.InklingRelDecode.Proof.Worker.Idle
