-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueSteps

@[expose] public section

/-! # The idle warp

Warp 15 lowers its register count (`setmaxnreg.dec 72`, line 248), passes every later role test
and returns. Its registers are the prologue's, for warp 15. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Idle
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

inductive Site where
  | setMaxReg | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_0
  | .exit => Flow.exit_0

/-- An idle state: the next event. -/
structure D where
  site : Site

/-- The idle warp's first state. -/
def start : D := ⟨.setMaxReg⟩

/-- The registers live at the site, with the prologue's values for warp 15. -/
abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Prologue.factsAt L g 15 (rankOf L g) d.site.pc

/-- The idle warp is warp 15. -/
def Inv (L : Launch) (g : Nat) (_ : D) : Prop := warpOf L g = 15

def next (d : D) (_ : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some ⟨.exit⟩)
  | .exit => none

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr}

/-- Each idle site is an unguarded event instruction. -/
theorem site_ok (d : D) : ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
    ins.guard = none := by
  obtain ⟨s⟩ := d
  cases s
  · exact ⟨_, Flow.code_setMaxReg_0, rfl, rfl⟩
  · exact ⟨_, Flow.code_exit_0, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- Lowering the register count, then the role tests to the exit. -/
theorem step_setMaxReg (hpre : Pre P L mem0) (hs : d.site = .setMaxReg)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ d' t', next d e = some (some d') ∧ Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' d'.site.pc (facts L g d') := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg false 72) from trivial) hf
  have h1 := At.next h
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 10 (PTX.next t) = some t2 ∧
      At t2 Site.exit.pc (facts L g ⟨.exit⟩) := by
    pro_seg h1 hpre
  exact ⟨⟨.exit⟩, t2, rfl, run_rtg hr2, h2⟩

/-- The return has no continuing event. -/
theorem exit_no_step (hs : d.site = .exit) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : False := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  simp [eventTmpl, Fires] at hf

/-- The idle warp's entry: the prologue's facts at its `setmaxnreg` are its own. -/
theorem entry (hw : warpOf L g = 15)
    (h : At t RoleKind.idle.entry
      (Prologue.factsAt L g (warpOf L g) (rankOf L g) RoleKind.idle.entry)) :
    At t start.site.pc (facts L g start) := by
  rw [hw] at h
  exact h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Idle
