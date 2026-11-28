-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreSrc

@[expose] public section

/-! # A one-source weak store advances

A proof tool. A weak store of one source register under THREAD-ACCESS that continues was at its
first element and leaves the thread at the next instruction with its registers unchanged
(`fires_st_adv`). -/

namespace PTX.Flow
open PTX PTX.Proof

/-- **A one-source weak store that continues advances** and keeps the registers. -/
theorem fires_st_adv {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {a : MemAccess} {sp : Space} {base w src : Nat} {pc : Nat} {e : Event}
    (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hsrc : a.srcs = [.reg src]) (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    t.sub = 0 ∧ u.pc = t.pc + 1 ∧ ∀ r, u.regs r = t.regs r := by
  rw [eventTmpl, memTmpl_store hr hs hb hk hsem] at hf
  have hsub : t.sub = 0 := by
    by_contra h
    have miss : ([Opnd.reg src] : List Opnd)[t.sub]? = none :=
      List.getElem?_eq_none (by simp; omega)
    simp only [storeTmpl, hsrc, miss] at hf
    split at hf <;> simp [Fires] at hf
  refine ⟨hsub, ?_⟩
  simp only [storeTmpl, hsrc] at hf
  split at hf
  · simp [Fires] at hf
  · split at hf
    · simp [Fires] at hf
    · split at hf
      · simp [Fires] at hf
      · simp only [Fires, Option.some.injEq] at hf
        obtain ⟨-, rfl⟩ := hf
        simp [afterStore]

end PTX.Flow
