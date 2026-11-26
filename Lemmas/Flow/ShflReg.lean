-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotShfl

@[expose] public section

/-! # A shuffle from a register sends the register's value

`fires_shfl_regv`: a `shfl.sync` whose first operand is register `r` fires a shuffle event whose
operand is the value of `r` (`fires_shfl_idx` for any mode and any lane operands). -/

namespace PTX.Flow
open PTX

/-- **A shuffle of register `r` sends its value.** -/
theorem fires_shfl_regv {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {d r : Nat}
    {p : Option Nat} {ty : Option DType} {mode : ShflMode} {b c mask : Opnd} {pc : Nat}
    {e : Event} {o : Option TState} {v : Value} (hr : t.regs r = some v)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl mode, ty, some d :: (p.map some).toList,
      [.reg r, b, c], some mask⟩)) e o)
    (hs : Execution.isShfl e = true) :
    ∃ bv cv recv ok, e = ⟨pc, .shfl mode v bv cv recv ok⟩ := by
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := mode) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := .reg r) (b := b) (c := c) (mask := mask) with
    h | h <;> rw [h] at hf
  swap
  · obtain ⟨epc, ek⟩ := e
    simp_all [Fires, Execution.isShfl]
  rw [hp] at hf
  simp only [shflTmpl, readValue, readReg, hr] at hf
  repeat' (split at hf)
  all_goals simp_all [Fires, pure, Except.pure, Execution.isShfl]
  all_goals subst_vars
  all_goals aesop

end PTX.Flow
