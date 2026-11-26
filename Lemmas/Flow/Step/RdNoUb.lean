-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ShapeAccAt

@[expose] public section

/-! # A shared load at an aligned address is no fault

`fires_rd_nonub`: a weak shared load through a 32-bit address register whose address is a multiple
of the vector's width (`w / 8 * ds.length`, nonzero) fires a read, never undefined behaviour. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **A weak shared load at an aligned address is no fault.** -/
theorem fires_rd_nonub {t : TState} {w base pc : Nat} {ds : List Nat} {off : Int}
    {x : BitVec 64} {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x))
    (hw : w / 8 ≠ 0)
    (hal : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % (w / 8 * ds.length) = 0)
    (hf : Fires pc (loadTmpl A L g t .shared false w ds base off) e o) :
    ∀ f, e.kind ≠ .ub f := by
  simp only [loadTmpl, effAddr_shared32 hr, elemAcc, bind, Except.bind, Bool.false_eq_true,
    ↓reduceIte] at hf
  have hm : ¬ (w / 8 = 0 ∨
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % (w / 8 * ds.length) ≠ 0) := by
    omega
  simp only [hm, ↓reduceIte, pure, Except.pure, Fires] at hf
  obtain ⟨bs, -, he, -⟩ := hf
  rw [show e.kind = _ from congrArg Event.kind he]
  intro f h
  cases h

end
end PTX.Flow
