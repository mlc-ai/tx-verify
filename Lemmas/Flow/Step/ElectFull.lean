-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Next
public import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # An election among the full warp does not fault

A proof tool (promoted from FlashMLA's startup shape, `Proof2/Startup/Shape.lean`, `elect_full`).
`fires_elect_mask` gives an `elect.sync` event of its mask or undefined behaviour; when the mask
reads as all 32 lanes (`0xffffffff`), the thread's lane is a member and the election fires its
event (`fires_elect_full`). -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **An election whose mask reads as the full warp fires its event.** -/
theorem fires_elect_full {t : TState} {dst : Option Nat} {p : Nat} {mask : Opnd}
    {ty : Option DType} {pc : Nat} {e : Event} {o : Option TState} {bits : BitVec 64}
    (hm : readBits L g t 32 mask = .ok bits) (hb : bits.toNat = 2 ^ 32 - 1)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some mask⟩)) e o) :
    ∃ inst ld, e.pc = pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld := by
  rcases fires_elect_mask hm hf with ⟨inst, ld, rfl⟩ | ⟨f, rfl⟩
  · exact ⟨inst, ld, rfl, by rw [hb]⟩
  · exfalso
    have hu := fires_ub hf rfl
    have hl : PTX.laneOf L g < 32 := by simp only [PTX.laneOf]; omega
    have ht : (2 ^ 32 - 1).testBit (PTX.laneOf L g) = true := by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hl
    simp only [eventTmpl, warpTmpl_elect, electTmpl, hm] at hu
    split_ifs at hu with h
    exact h (by simp only [electMember, hb, ht, hl, and_self])

end PTX.Flow
