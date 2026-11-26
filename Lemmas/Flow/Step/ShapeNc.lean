-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ShapeRegs

@[expose] public section

/-! # The kind of a `.nc` load's event, and a register's 32-bit read

A proof tool for shape tables: `fires_ncLoad_kind` is `fires_load_kind` for a load with the
`.nc` flag (a non-coherent read, or a fault); `readBits_reg` reads the low 32 bits of a register
that holds a word. -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **A `.nc` load** fires a non-coherent read, or faults. -/
theorem fires_ncLoad_kind {t : TState} {sp : Space} {w : Nat} {ds : List Nat} {base : Nat}
    {off : Int} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (loadTmpl A L g t sp true w ds base off) e o) :
    (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f := by
  unfold loadTmpl at hf
  simp only [↓reduceIte] at hf
  split at hf
  · exact .inr ⟨_, congrArg Event.kind (by simpa only [Fires] using hf.1)⟩
  split at hf
  · obtain ⟨bs, -, he, -⟩ := (by simpa only [Fires] using hf :
      ∃ bs, _ ∧ e = _ ∧ _)
    exact .inl ⟨_, bs, congrArg Event.kind he⟩
  · exact .inr ⟨_, congrArg Event.kind (by simpa only [Fires] using hf.1)⟩

/-- A register holding a word reads its low 32 bits. -/
theorem readBits_reg {t : TState} {r w : Nat} {x : BitVec 64} (h : t.regs r = some (.bits w x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

end PTX.Flow
