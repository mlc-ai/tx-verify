-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Lemmas.Flow.Alloc
public import Lemmas.Flow.WriteSpace

@[expose] public section

/-! # Where a thread's memory accesses are

A proof tool for the memory regions of a kernel. A read is fired by a read template
(`fires_read_tmpl`). The footprint of a thread's access is fixed by its instruction and the register
holding the address: a weak load into one register reads its element at the effective address
(`fires_ld_rd`), and the write of a Tensor Memory allocation's column writes the four bytes at its
effective address (`fires_tcAlloc_wr`). -/

namespace PTX.Flow

open PTX

/-- A weak load into one register reads its element at the effective address. -/
theorem fires_ld_rd {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {sp : Space}
    {a : MemAccess} {d base bw : Nat} {pc : Nat} {e : Event} {o : Option TState} {loc : Loc}
    (hd : effAddr L g t sp base 0 = .ok loc) (hsub : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hr : a.rule = some .threadAccess := by rfl) (hs : a.locSpace? = some sp := by rfl)
    (hb : a.addr.base = .reg base bw := by rfl) (hl : a.kind = .load := by rfl)
    (hnc : a.nc = false := by rfl) (hsem : a.sem = .weak := by rfl)
    (hregs : a.regs = [d] := by rfl) (hoff : a.addr.off = 0 := by rfl) :
    ∀ ac bs, e.kind = .rd ac bs → ac.loc = loc ∧ ac.size = a.elem.width / 8 := by
  intro ac bs hk
  rw [eventTmpl, memTmpl_load hr hs hb hl hsem, hnc, hregs, hoff] at hf
  simp only [loadTmpl, hd, hsub, bind, Except.bind, Bool.false_eq_true,
    ↓reduceIte] at hf
  cases helem : elemAcc loc (a.elem.width / 8) [d].length 0 with
  | error f =>
    simp only [helem, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok a' =>
    simp only [helem, Fires] at hf
    obtain ⟨bs', -, he, -⟩ := hf
    rw [he] at hk
    cases hk
    unfold elemAcc at helem
    split_ifs at helem
    all_goals cases helem
    all_goals refine ⟨?_, rfl⟩
    all_goals simp only [Loc.at, Nat.mul_zero, Nat.add_zero]

/-- The address store of a Tensor Memory allocation writes the four bytes at the allocation's
effective address. -/
theorem fires_tcAlloc_wr {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {dst : Loc} (hd : effAddr L g t .shared base off = .ok dst)
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e o) :
    ∀ a bs, e.kind = .wr a bs → a.loc = dst ∧ a.size = 4 := by
  intro a bs hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  simp only [eventTmpl, tcTmpl, hd] at hf
  cases hn : readBits L g t 32 nc with
  | error f =>
    simp [ofExec, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf
  | ok n =>
    simp [ofExec, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf
    all_goals first
      | (simp [Fires] at hf; done)
      | (simp only [Fires] at hf
         obtain ⟨col, -, he, -⟩ := hf
         simp only [Event.mk.injEq, Kind.wr.injEq] at he
         obtain ⟨-, rfl, -⟩ := he
         exact ⟨rfl, rfl⟩)

end PTX.Flow
