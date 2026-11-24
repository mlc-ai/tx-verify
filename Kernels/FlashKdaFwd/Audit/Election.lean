-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Elect
import Mathlib.Tactic.IntervalCases

/-! # A full-mask warp election can select lane one under the shared PTX rules

All 32 lanes of the recurrence kernel's load warp participate. This checks the election
contract itself. Reaching the subsequent breakpoint also depends on the actual program guards.
-/
@[expose] public section
namespace FlashKda.Election
open PTX
noncomputable section

def launch : Launch := { grid := 1, block := 192, params := fun _ => none }
def mask : Nat := 0xffffffff
def choice : Execution :=
  { tr := fun g => if 128 ≤ g ∧ g < 160 then [⟨0, .elect mask 0 1⟩] else []
    rf := fun _ _ => none }

theorem participants (g : ℕ) (h : 128 ≤ g ∧ g < 160) :
    choice.Elect (g,0) 0 mask 0 1 := by
  simp [Execution.Elect, Execution.get, choice, h]

theorem event_shape {g j pc m inst leader : ℕ}
    (e : choice.Elect (g,j) pc m inst leader) :
    128 ≤ g ∧ g < 160 ∧ j = 0 ∧ pc = 0 ∧ m = mask ∧ inst = 0 ∧ leader = 1 := by
  by_cases hw : 128 ≤ g ∧ g < 160
  · cases j with
    | zero =>
      have h := e
      simp [Execution.Elect, Execution.get, choice, hw, Event.mk.injEq, Kind.elect.injEq] at h
      exact ⟨hw.1, hw.2, rfl, h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
    | succ j => simp [Execution.Elect, Execution.get, choice, hw] at e
  · simp [Execution.Elect, Execution.get, choice, hw] at e

theorem legal : ElectOk launch choice := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨g,j⟩ pc m inst leader e
    obtain ⟨lo, hi, rfl, rfl, rfl, rfl, rfl⟩ := event_shape e
    have hm : ∀ i : Fin 32, electMember mask i := by decide +kernel
    exact ⟨by change g < 192; omega, hm ⟨laneOf launch g, Nat.mod_lt _ (by decide)⟩, by decide⟩
  · intro ⟨g,j⟩ ⟨g',j'⟩ pc pc' m m' inst ld ld' e f _
    obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩ := event_shape e
    obtain ⟨_, _, rfl, rfl, rfl, _, rfl⟩ := event_shape f
    simp
  · intro ⟨g,j⟩ ⟨g',j'⟩ pc pc' m inst inst' ld ld' e f _
    exact (event_shape e).2.2.2.2.2.2.trans (event_shape f).2.2.2.2.2.2.symm

/-- On the elected producer, CUTLASS checks the index modulo 32 against zero. -/
theorem nonzero_elected :
    ElectOk launch choice ∧ choice.Elect (129,0) 0 mask 0 1 ∧ laneOf launch 129 ≠ 0 :=
  ⟨legal, participants 129 (by decide), by decide⟩

end
end FlashKda.Election
