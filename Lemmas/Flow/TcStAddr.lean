-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcLdTmpl
public import Lemmas.Flow.TcStLen

@[expose] public section

/-! # The address of a Tensor Memory store, and its wait

A proof tool beside `Lemmas/Flow/TcLdTmpl.lean`. A data event of a Tensor Memory store of a shape
other than `.unpack::16b`, at a site with no implicit wait, is the store at the address its
register holds, with the shape of the instruction (`fires_tcSt_addr`). Its wait fires the wait
event (`fires_tcWaitSt_kind`). -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- A store template that reads its address from register `ta` fires the store at the address
that register holds. -/
theorem fires_tcSt_ofTmpl {L : Launch} {g : Nat} {t : TState}
    {ss : List Opnd} {ta a : Nat} {sh : TcShape} {pc : Nat}
    {e : Event} {o : Option TState} (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hd : isTcData e = true)
    (hf : Fires pc (ofExec (do
      unless L.block % 32 = 0 do throw .noRule
      unless sh.countOk ss.length do throw .noRule
      let v ← readBits L g t 32 (.reg ta)
      unless tcDataAddressOk L g sh v.toNat do throw .noRule
      let vals ← ss.mapM (readValue L g t 32)
      unless vals.all (·.bytes = 4) do throw .typeMismatch
      pure (.tc (.st v.toNat vals sh) (next t)))) e o) :
    ∃ vals, e = ⟨pc, .tc (.st a vals sh)⟩ := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  simp [ofExec, readBits_b32' hr, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
    Nat.mod_eq_of_lt h64, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  generalize List.mapM (readValue L g t 32) ss = r at hf
  cases r with
  | error x =>
    split_ifs at hf <;> simp only [Fires] at hf <;> (obtain ⟨rfl, -⟩ := hf; simp [isTcData] at hd)
  | ok vals =>
    by_cases hb : ∀ x ∈ vals, x.bytes = 4
    · split_ifs at hf <;> dsimp only at hf <;> (try simp only [eq_true hb, ↓reduceIte] at hf) <;>
        simp only [Fires] at hf
      all_goals first
        | (obtain ⟨rfl, -⟩ := hf; exact ⟨vals, rfl⟩)
        | (obtain ⟨rfl, -⟩ := hf; simp [isTcData] at hd)
    · split_ifs at hf <;> dsimp only at hf <;> (try simp only [eq_false hb, ↓reduceIte] at hf) <;>
        simp only [Fires] at hf <;> (obtain ⟨rfl, -⟩ := hf; simp [isTcData] at hd)

/-- A data event of a Tensor Memory store, at a site with no implicit wait, is the store at the
address its register holds, with the shape of the instruction. -/
theorem fires_tcSt_addr {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ss : List Opnd} {ta : Nat} {sh : TcShape} {a pc : Nat} {e : Event} {o : Option TState}
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o) (hd : isTcData e = true)
    (hnp : ∀ s, sh ≠ .packed16 s) (hw : A.any (·.tcStWaitLd t.pc) = false := by hooks_off) :
    ∃ vals, e = ⟨pc, .tc (.st a vals sh)⟩ := by
  rw [eventTmpl_tcSt_noWait hw, tcTmpl_tcSt_plain hnp] at hf
  exact fires_tcSt_ofTmpl hr ha hd hf

/-- A Tensor Memory store wait fires its event, in a block of whole warps. -/
theorem fires_tcWaitSt_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} (hb : L.block % 32 = 0)
    (hf : Fires pc (eventTmpl A L g t .tcWaitSt) e o) : e = ⟨pc, .tc .waitSt⟩ := by
  simp only [eventTmpl, tcTmpl, hb, ofExec, pure, Except.pure, ↓reduceIte] at hf
  exact hf.1

end
end PTX.Flow
