-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
import Lemmas.Flow.UbFree

@[expose] public section

/-! # Where a weak load reads (library candidate)

`loadTmpl_rd`: a read event of a load template is element `t.sub` of the access at the template's
effective address (Core's `elemAcc`). `ldShared_rd` is the shared form under THREAD-ACCESS: a load
through a 32-bit register holding the word `x` with offset `off` reads at the 32-bit truncation of
`x + off`, plus the element's offset. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A read of a load template is its element at the effective address.** -/
theorem loadTmpl_rd {sp : Space} {nc : Bool} {w base : Nat} {off : Int} {ds : List Nat} {loc : Loc}
    {pc : Nat} {e : Event} {o : Option TState} (hea : effAddr L g t sp base off = .ok loc)
    (hf : Fires pc (loadTmpl A L g t sp nc w ds base off) e o) {acc : Acc}
    {bs : List (Option Byte)}
    (hk : e.kind = .rd acc bs) : acc.loc = loc.at (w / 8 * t.sub) ∧ acc.size = w / 8 := by
  unfold loadTmpl at hf
  rw [hea] at hf
  simp only [bind, Except.bind, elemAcc] at hf
  by_cases hbad : w / 8 = 0 ∨ loc.addr % (w / 8 * ds.length) ≠ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hbad)] at hf
    simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    rw [hf.1] at hk; cases hk
  rw [ite_eq_right_of_eq_false _ _ (eq_false hbad)] at hf
  · simp only [pure, Except.pure] at hf
    split at hf
    · split_ifs at hf
      · simp only [Fires] at hf; obtain ⟨_, _, rfl, _⟩ := hf; cases hk
      · simp only [Fires] at hf; rw [hf.1] at hk; cases hk
    · simp only [Fires] at hf
      obtain ⟨_, _, rfl, _⟩ := hf
      cases hk
      exact ⟨rfl, rfl⟩

/-- **A weak shared load through a 32-bit register reads at the truncated sum of the register's
word and the offset**, plus the element's offset. -/
theorem ldShared_rd {a : MemAccess} {base : Nat} {x : BitVec 64}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .shared)
    (hb : a.addr.base = .reg base 32) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hr : t.regs base = some (.bits 32 x)) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) {acc : Acc} {bs : List (Option Byte)}
    (he : e.kind = .rd acc bs) :
    acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 a.addr.off)).toNat +
        a.elem.width / 8 * t.sub⟩ ∧ acc.size = a.elem.width / 8 := by
  rw [eventTmpl, memTmpl_load hrule hs hb hk hsem] at hf
  obtain ⟨h1, h2⟩ := loadTmpl_rd (effAddr_shared32 hr) hf he
  exact ⟨by rw [h1]; rfl, h2⟩

end

end PTX.Flow
