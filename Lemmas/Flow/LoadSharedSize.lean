-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LoadShared

@[expose] public section

/-! # The size of a scalar shared load

A proof tool. A 32-bit `ld.shared` at an offset reads four bytes (`fires_ld_shared_size`). -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

/-- A 32-bit shared load at `a + off` reads four bytes. -/
theorem fires_ld_shared_size {d base a off : Nat} {ik : IType} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        addr := ⟨.reg base 32, (off : Int)⟩, dsts := [some d] })) e (some u)) :
    ∀ ac bs, e.kind = .rd ac bs → ac.size = 4 := by
  intro ac bs hk
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl) rfl
    rfl rfl rfl] at hf
  simp only [MemAccess.regs, DType.width, loadTmpl,
    effAddr_b32_off hr ha, bind, Except.bind, elemAcc, hs] at hf
  simp only [Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf
  all_goals first
    | (simp [throw, throwThe, MonadExceptOf.throw, Fires] at hf; done)
    | (exfalso; simp_all; done)
    | (obtain ⟨bs', -, rfl, -⟩ := hf
       simp only [Kind.rd.injEq] at hk
       rw [← hk.1])

end PTX.Flow
