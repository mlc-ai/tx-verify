-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ShapeRegs
import Lemmas.Flow.Step.ShapeAsync

@[expose] public section

/-! # The object an `mbarrier.init` initializes (library candidate)

`fires_mbInit_reg`: an `mbarrier.init [r + off], c` whose address register holds a 32-bit word
`x` with `x + off` 8-aligned (modulo `2 ^ 32`) fires an initialization of the shared object
`smLoc x off` of the thread's CTA, or undefined behaviour. -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState}

/-- **An initialization through an aligned 32-bit address register names the object at that
address.** -/
theorem fires_mbInit_reg {base : Nat} {off : Int} {c : Opnd} {x : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.mbarInit base off c)) e o)
    (hr : t.regs base = some (.bits 32 x))
    (h8 : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0) :
    (∃ n, e.kind = .mbInit (smLoc L g x off) n) ∨ ∃ f, e.kind = .ub f := by
  have hm := mbarLoc_bits (L := L) (g := g) hr h8
  simp only [eventTmpl, tmaTmpl, hm, bind, Except.bind] at hf
  revert hf
  generalize readBits L g t 32 c = rb
  intro hf
  rcases rb with f | n
  · simp only [ofExec, widenMbarScope] at hf
    split_ifs at hf <;> (simp only [Fires] at hf; exact .inr ⟨_, by rw [hf.1]⟩)
  · simp only at hf
    split_ifs at hf
    · simp only [ofExec, pure, Except.pure, widenMbarScope] at hf
      split_ifs at hf <;> (simp only [Fires] at hf; exact .inl ⟨_, by rw [hf.1]⟩)
    · simp only [ofExec, throw, throwThe, MonadExceptOf.throw, widenMbarScope] at hf
      split_ifs at hf <;> (simp only [Fires] at hf; exact .inr ⟨_, by rw [hf.1]⟩)

/-- **The count of such an initialization is its count operand's value.** -/
theorem fires_mbInit_cnt {base : Nat} {off : Int} {c : Opnd} {x n0 : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.mbarInit base off c)) e o)
    (hr : t.regs base = some (.bits 32 x))
    (h8 : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0)
    (hc : readBits L g t 32 c = .ok n0) :
    e.kind = .mbInit (smLoc L g x off) n0.toNat ∨ ∃ f, e.kind = .ub f := by
  have hm := mbarLoc_bits (L := L) (g := g) hr h8
  simp only [eventTmpl, tmaTmpl, hm, hc, bind, Except.bind] at hf
  split_ifs at hf
  · simp only [ofExec, pure, Except.pure, widenMbarScope] at hf
    split_ifs at hf <;> (simp only [Fires] at hf; exact .inl (by rw [hf.1]))
  · simp only [ofExec, throw, throwThe, MonadExceptOf.throw, widenMbarScope] at hf
    split_ifs at hf <;> (simp only [Fires] at hf; exact .inr ⟨_, by rw [hf.1]⟩)

end PTX.Flow
