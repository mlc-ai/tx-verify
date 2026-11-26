-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ShflReg

@[expose] public section

/-! # A shuffle from a register by immediate lane operands

`fires_shfl_regimm` is `fires_shfl_regv` (`Lemmas/Flow/ShflReg.lean`) with the lane and clamp
operands' values: for the immediates `bi`, `ci` the event records their 32-bit words. -/

namespace PTX.Flow
open PTX

/-- **A shuffle of register `r` by immediate lane operands sends its value and them.** -/
theorem fires_shfl_regimm {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {d r : Nat}
    {p : Option Nat} {ty : Option DType} {mode : ShflMode} {bi ci : Int}
    {mask : Opnd} {pc : Nat}
    {e : Event} {o : Option TState} {v : Value} (hr : t.regs r = some v)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl mode, ty, some d :: (p.map some).toList,
      [.reg r, .imm bi, .imm ci], some mask⟩)) e o)
    (hs : Execution.isShfl e = true) :
    ∃ recv ok, e = ⟨pc, .shfl mode v (truncBits 32 (BitVec.ofInt 64 bi)).toNat
      (truncBits 32 (BitVec.ofInt 64 ci)).toNat recv ok⟩ := by
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := mode) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := .reg r) (b := .imm bi) (c := .imm ci) (mask := mask) with
    h | h <;> rw [h] at hf
  swap
  · obtain ⟨epc, ek⟩ := e
    simp_all [Fires, Execution.isShfl]
  rw [hp] at hf
  simp only [shflTmpl, readValue, readReg, hr] at hf
  repeat' (split at hf)
  all_goals simp_all [Fires, pure, Except.pure, Execution.isShfl]
  all_goals (try simp only [readBits, pure, Except.pure, Except.ok.injEq] at *)
  all_goals subst_vars
  all_goals aesop

end PTX.Flow
