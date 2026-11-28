-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ShflReg
public import Lemmas.Flow.Next

@[expose] public section

/-! # A shuffle of a register sends the register's value

A proof tool, generic over the kernel. A `shfl.sync` whose first operand is register `r` that fires
a shuffle event and returns a state `u`: `r` holds a value in the state before, the event sends
that value, and `u` is the next state with the destination (and predicate) set. -/

namespace PTX.Flow
open PTX

/-- **A shuffle of register `r` that fires sends the value `r` holds.** -/
theorem fires_shfl_src {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {mode : ShflMode} {d r : Nat} {p : Option Nat} {b c mask : Opnd} {pc : Nat} {e : Event}
    {ty : Option DType}
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.shfl mode, ty, some d :: (p.map some).toList, [.reg r, b, c], some mask⟩)) e
      (some u)) :
    ∃ v bv cv recv ok, t.regs r = some v ∧ e = ⟨pc, .shfl mode v bv cv recv ok⟩ ∧
      u = next (p.elim (setReg t d recv) fun p => setReg (setReg t d recv) p (.pred ok)) := by
  obtain ⟨av, bv, cv, recv, ok, he, hu⟩ := fires_shfl hf
  rcases hr : t.regs r with _ | v
  · exfalso
    have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
    simp only [eventTmpl] at hf
    rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := mode) (ty := ty) (d := d)
      (ps := (p.map some).toList) (a := .reg r) (b := b) (c := c) (mask := mask) with
      h | h <;> rw [h] at hf
    · rw [hp] at hf
      simp only [shflTmpl, readValue, readReg, hr] at hf
      repeat' (split at hf)
      all_goals simp_all [Fires]
    · obtain ⟨epc, ek⟩ := e
      simp_all [Fires]
  · have hs : Execution.isShfl e = true := by rw [he]; rfl
    obtain ⟨bv', cv', recv', ok', he'⟩ := fires_shfl_regv hr hf hs
    rw [he] at he'
    simp only [Event.mk.injEq, Kind.shfl.injEq, true_and] at he'
    obtain ⟨rfl, -⟩ := he'
    exact ⟨av, bv, cv, recv, ok, rfl, he, hu⟩

end PTX.Flow
