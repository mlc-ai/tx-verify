-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
public import Lemmas.Flow.NotTcData

@[expose] public section

/-! # The address of a Tensor Memory load

A proof tool. A Tensor Memory load whose address register holds a 32-bit integer loads at that
address (`fires_tcLd_addr`); it returns one word per destination register (`fires_tcLd_len`). The
`.pack::16b` shapes are left out of the count, since they load two words per register. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- A Tensor Memory load template of `n` values of shape `sh` that reads its address from register
`ta` fires the load of `n` values at the address that register holds. -/
theorem fires_tcLd_ofTmpl {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta a n : Nat} {sh : TcShape} {k : List Value → TState} {pc : Nat} {e : Event}
    {o : Option TState} (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (hd : isTcData e = true)
    (hf : Fires pc (ofExec (do
      unless L.block % 32 = 0 do throw .noRule
      unless sh.countOk ds.length do throw .noRule
      let v ← readBits L g t 32 (.reg ta)
      unless tcDataAddressOk L g sh v.toNat do throw .noRule
      pure (.tcLd v.toNat n sh k))) e o) :
    ∃ vals, vals.length = n ∧ e = ⟨pc, .tc (.ld a vals sh)⟩ := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  simp [ofExec, readBits_b32' hr, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
    Nat.mod_eq_of_lt h64, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  split_ifs at hf <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; simp [isTcData] at hd)
    | (obtain ⟨vals, hl, rfl, -⟩ := hf; exact ⟨vals, hl, rfl⟩)

/-- A data event of a Tensor Memory load, at a site with no implicit wait, is the load at the
address its register holds. -/
theorem fires_tcLd_addr {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {a pc : Nat} {e : Event} {o : Option TState}
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e o) (hd : isTcData e = true)
    (hw : A.any (·.tcLdWait t.pc) = false := by hooks_off) :
    ∃ vals, e = ⟨pc, .tc (.ld a vals sh)⟩ := by
  rw [eventTmpl_tcLd_noWait hw] at hf
  cases sh with
  | s32x32b | s16x64b | s16x128b | s16x256b | s16x32bx2 n =>
    rw [tcTmpl_tcLd_none (by intro s hs; cases hs)] at hf
    obtain ⟨vals, -, he⟩ := fires_tcLd_ofTmpl hr ha hd hf
    exact ⟨vals, he⟩
  | packed16 s =>
    simp only [tcTmpl] at hf
    obtain ⟨vals, -, he⟩ := fires_tcLd_ofTmpl (n := 2 * ds.length) (sh := .packed16 s)
      (k := fun vals => ldResult (next t) ds none (TcPack16.pack vals)) hr ha hd hf
    exact ⟨vals, he⟩

/-- A load template of a shape other than `.pack::16b` returns one word per destination
register. -/
theorem fires_tcTmpl_len {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {pc : Nat} {e : Event} {o : Option TState}
    (hsh : ∀ s, sh ≠ .packed16 s) (hf : Fires pc (tcTmpl L g t (.tcLd ds ta sh)) e o)
    {a : Nat} {vals : List Value} {sh' : TcShape} (he : e.kind = .tc (.ld a vals sh')) :
    vals.length = ds.length := by
  rw [tcTmpl_tcLd_none hsh] at hf
  cases ha : readBits L g t 32 (.reg ta) with
  | error f =>
    simp [ofExec, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf <;> (obtain ⟨rfl, -⟩ := hf; cases he)
  | ok v =>
    simp [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf
    all_goals first
      | (obtain ⟨rfl, -⟩ := hf; cases he)
      | (obtain ⟨vals', hl, rfl, -⟩ := hf
         simp only [Kind.tc.injEq, TcKind.ld.injEq] at he
         rw [← he.2.1]
         exact hl)

/-- A Tensor Memory load of a shape other than `.pack::16b` returns one word per destination
register, with or without an implicit wait. -/
theorem fires_tcLd_len {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {pc : Nat} {e : Event} {o : Option TState}
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e o) {a : Nat} {vals : List Value}
    {sh' : TcShape} (he : e.kind = .tc (.ld a vals sh')) : vals.length = ds.length := by
  rcases eventTmpl_tcLd_cases (A := A) (L := L) (g := g) (t := t) (ds := ds) (ta := ta)
    (sh := sh) with
    h | h | h <;> rw [h] at hf
  · exact fires_tcTmpl_len hsh hf he
  · obtain ⟨o', hf⟩ := fires_thenWaitLd hf
    exact fires_tcTmpl_len hsh hf he
  · obtain ⟨rfl, -⟩ := hf
    cases he

end

end PTX.Flow
