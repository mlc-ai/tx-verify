-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LoadShared

@[expose] public section

/-! # The location a scalar shared store writes

A proof tool. A scalar `st.shared` whose base register holds the word `a` writes at
`a + off` of the thread's CTA (`fires_st_loc`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A scalar shared store that continues writes at its base plus offset. -/
theorem fires_st_loc {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {w : Nat}
    {base a off : Nat} {src : Opnd} {ik : IType} {pc : Nat} {e : Event}
    (hr : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik w,
        addr := ⟨.reg base 32, (off : Int)⟩, srcs := [src] })) e (some u))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    ∃ acc bs, e.kind = .wr acc bs ∧ acc.loc = ⟨.shared, g / L.block, a + off⟩ := by
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik w, addr := ⟨.reg base 32, (off : Int)⟩,
                                srcs := [src] } = some .threadAccess := by
    rcases hw with rfl | rfl | rfl | rfl <;> cases ik <;> rfl
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)] at hf
  simp only [DType.width, storeTmpl, effAddr_b32_off hr ha, bind, Except.bind, elemAcc, hs,
    Nat.mul_zero] at hf
  split_ifs at hf
  · simp [Fires, throw, throwThe, MonadExceptOf.throw] at hf
  · simp only [pure, Except.pure, List.getElem?_cons_zero] at hf
    rcases hrv : readValue L g t w src with f | v <;> simp only [hrv] at hf
    · exact absurd hf.2 (by simp)
    · by_cases hb : v.bytes = w / 8
      · simp only [storeValue, hb, ↓reduceIte, Fires] at hf
        exact ⟨_, _, by rw [hf.1], by simp [Loc.at]⟩
      · simp only [storeValue, hb, ↓reduceIte] at hf
        repeat' split at hf
        all_goals simp only [Fires] at hf
        all_goals first
          | exact ⟨_, _, by rw [hf.1], by simp [Loc.at]⟩
          | exact absurd hf.2 (by simp)

end
end PTX.Flow
