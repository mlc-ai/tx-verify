-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-! # The bits a register value reads as

A proof tool. `Value.regBits v` is the 64-bit pattern a register holding `v` reads as through
`readBits` before truncation: the integer itself, the bit pattern of a value that has one, and
none for a pointer or a value without one. A register read as bits succeeds exactly when its
value has a pattern (`readBits_regBits`, `readBits_regBits_none`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- The bits a register holding `v` reads as (`readBits` of a register, before truncation). -/
def _root_.PTX.Value.regBits : Value → Option (BitVec 64)
  | .bits _ x => some x
  | .ptr .. => none
  | v => v.bitPattern.map (BitVec.ofNat 64)

variable {L : Launch} {g : Nat} {t : TState}

/-- A register whose value has a pattern reads as it. -/
theorem readBits_regBits {w r : Nat} {v : Value} {x : BitVec 64} (hr : t.regs r = some v)
    (hv : v.regBits = some x) : readBits L g t w (.reg r) = .ok (truncBits w x) := by
  cases v with
  | bits w' y =>
    simp only [Value.regBits, Option.some.injEq] at hv
    subst hv
    simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]
  | ptr => simp [Value.regBits] at hv
  | policy => simp [Value.regBits, Value.bitPattern] at hv
  | _ =>
    simp only [Value.regBits] at hv
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hv
    simp only [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]
    rw [hn]

/-- A register whose value has no pattern does not read as bits. -/
theorem readBits_regBits_none {w r : Nat} {v : Value} (hr : t.regs r = some v)
    (hv : v.regBits = none) : ∃ f, readBits L g t w (.reg r) = .error f := by
  cases v with
  | bits => simp [Value.regBits] at hv
  | ptr => exact ⟨_, by simp [readBits, readReg, hr, bind, Except.bind]; rfl⟩
  | policy => exact ⟨_, by simp [readBits, readReg, hr, bind, Except.bind]; rfl⟩
  | _ =>
    simp only [Value.regBits, Option.map_eq_none_iff] at hv
    refine ⟨.typeMismatch, ?_⟩
    simp only [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]
    rw [hv]
    rfl

end
end PTX.Flow
