-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
import Lemmas.Flow.UbFree

@[expose] public section

/-! # Where a weak store writes (library candidate)

`storeTmpl_wr`: a write event of a store template is element `t.sub` of the access at the
template's effective address (Core's `elemAcc`). `stShared_wr` is the shared form under
THREAD-ACCESS: a store through a 32-bit register holding the word `x` with offset `off` writes at
the 32-bit truncation of `x + off`, plus the element's offset. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A write of a store template is its element at the effective address.** -/
theorem storeTmpl_wr {sp : Space} {w base : Nat} {off : Int} {srcs : List Opnd} {loc : Loc}
    {pc : Nat} {e : Event} {o : Option TState} (hea : effAddr L g t sp base off = .ok loc)
    (hf : Fires pc (storeTmpl L g t sp w base off srcs) e o) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) : acc.loc = loc.at (w / 8 * t.sub) ∧ acc.size = w / 8 := by
  unfold storeTmpl at hf
  rw [hea] at hf
  simp only [bind, Except.bind, elemAcc] at hf
  split_ifs at hf
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    rw [hf.1] at hk; cases hk
  · simp only [pure, Except.pure] at hf
    split at hf
    · simp only [Fires] at hf; rw [hf.1] at hk; cases hk
    · split at hf
      · simp only [Fires] at hf; rw [hf.1] at hk; cases hk
      · simp only [Fires] at hf
        rw [hf.1] at hk
        cases hk
        exact ⟨rfl, rfl⟩

/-- **A weak shared store through a 32-bit register writes at the truncated sum of the register's
word and the offset**, plus the element's offset. -/
theorem stShared_wr {a : MemAccess} {base : Nat} {x : BitVec 64}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .shared)
    (hb : a.addr.base = .reg base 32) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hr : t.regs base = some (.bits 32 x)) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) {acc : Acc} {bs : List Byte}
    (he : e.kind = .wr acc bs) :
    acc.loc = ⟨.shared, g / L.block,
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 a.addr.off)).toNat +
        a.elem.width / 8 * t.sub⟩ ∧ acc.size = a.elem.width / 8 := by
  rw [eventTmpl, memTmpl_store hrule hs hb hk hsem] at hf
  obtain ⟨h1, h2⟩ := storeTmpl_wr (effAddr_shared32 hr) hf he
  exact ⟨by rw [h1]; rfl, h2⟩

/-- **A weak global store through a 64-bit register writes in the global space.** -/
theorem stGlobal_wr {a : MemAccess} {base : Nat} {x : BitVec 64}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .global)
    (hb : a.addr.base = .reg base 64) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hr : t.regs base = some (.bits 64 x)) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) {acc : Acc} {bs : List Byte}
    (he : e.kind = .wr acc bs) : acc.loc.space = .global := by
  rw [eventTmpl, memTmpl_store hrule hs hb hk hsem] at hf
  obtain ⟨h1, -⟩ := storeTmpl_wr (effAddr_global_bits hr) hf he
  rw [h1]; rfl

end

end PTX.Flow
