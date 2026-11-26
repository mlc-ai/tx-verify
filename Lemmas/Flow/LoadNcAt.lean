-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
import Lemmas.Flow.UbFree

@[expose] public section

/-! # Where a `.nc` global load reads

`fires_ncLoad_at`: a `.nc` global load through a 64-bit register holding the word `x` with offset
`off` fires a `.nc` read of element `t.sub` of the access at `x + off` (Core's `elemAcc`, `w / 8`
bytes), or undefined behaviour. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A `.nc` global load through a 64-bit register reads at the register's word plus the
offset**, plus the element's offset, or faults. -/
theorem fires_ncLoad_at {w base pc : Nat} {off : Int} {ds : List Nat} {x : BitVec 64}
    {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 64 x))
    (hf : Fires pc (loadTmpl A L g t .global true w ds base off) e o) :
    (∃ a bs, e.kind = .nc a bs ∧
      a.loc = (⟨.global, 0, (truncBits 64 x + BitVec.ofInt 64 off).toNat⟩ : Loc).at
        (w / 8 * t.sub) ∧ a.size = w / 8) ∨ ∃ f, e.kind = .ub f := by
  unfold loadTmpl at hf
  rw [effAddr_global_bits hr] at hf
  simp only [bind, Except.bind, elemAcc] at hf
  split_ifs at hf
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · simp only [Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · simp only [pure, Except.pure, Fires] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact .inl ⟨_, bs, congrArg Event.kind he, rfl, rfl⟩
  · simp only [pure, Except.pure, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩

end
end PTX.Flow
