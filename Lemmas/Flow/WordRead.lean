-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # Integer reads of a register of any kind

A load returns whatever value its bytes rebuild to (`rebuild`): an integer, a floating payload, a
pair, a pointer. An integer instruction reads a register through `readBits`, which takes an
integer's bits, a payload's bit pattern, and has no rule for a pointer, a cache policy or a value
without a bit pattern. `wordOf v` is that reading before truncation, so an integer instruction on
a register holding `v` behaves as on the word `wordOf v` when it is `some`, and faults when it is
`none`. A machine that records the loaded value can therefore follow the thread on every value:
it continues with the word, or the thread dies at the first integer read.

A proof tool, generic over the kernel (promoted from FlashMLA's `Proof/Lib/WordRead.lean`; the
step lemmas of its dequantizer stay there). -/

namespace PTX.Flow
open PTX
noncomputable section

/-- The integer an integer instruction reads from a register holding `v`, before truncation. -/
def wordOf : Value → Option Nat
  | .bits _ x => some x.toNat
  | .ptr .. => none
  | .policy => none
  | v => v.bitPattern

theorem wordOf_bits (w : Nat) (x : BitVec 64) : wordOf (.bits w x) = some x.toNat := rfl

variable {L : Launch} {g : Nat} {t : TState}

/-- An integer read of a register holding a value with a word. -/
theorem readBits_word {w r : Nat} {v : Value} {n : Nat} (hr : t.regs r = some v)
    (hn : wordOf v = some n) :
    readBits L g t w (.reg r) = .ok (truncBits w (BitVec.ofNat 64 n)) := by
  cases v <;> simp_all [readBits, readReg, wordOf, bind, Except.bind, pure, Except.pure]
  subst hn
  simp

/-- An integer read of a register holding a value without a word faults. -/
theorem readBits_noWord {w r : Nat} {v : Value} (hr : t.regs r = some v)
    (hn : wordOf v = none) : ∃ f, readBits L g t w (.reg r) = .error f := by
  cases v <;> simp_all [readBits, readReg, wordOf, bind, Except.bind, pure, Except.pure] <;>
    exact ⟨_, rfl⟩

theorem readBits_imm {w : Nat} {x : Int} :
    readBits L g t w (.imm x) = .ok (truncBits w (BitVec.ofInt 64 x)) := rfl

/-- A value with a word is not a pointer. -/
theorem not_ptr_of_word {v : Value} {n : Nat} (hn : wordOf v = some n) :
    ∀ w gen sp off, v ≠ .ptr w gen sp off := by
  intro w gen sp off h
  subst h
  cases hn

end
end PTX.Flow
