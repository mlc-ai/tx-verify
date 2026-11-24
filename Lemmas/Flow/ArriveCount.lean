-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotObject

@[expose] public section

/-! # The arrival count of an arrival

A proof tool. An arrival event carries the value its count operand reads (`fires_arrive_count`),
whatever its object and byte count evaluate to: an immediate count is that immediate. An arrival
whose operands evaluate is not undefined behaviour (`fires_arrive_notUb`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- An arrival carries the count its count operand reads. -/
theorem fires_arrive_count {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {st : Option Nat} {pc : Nat} {e : Event} {o : Option TState} {n : BitVec 64}
    (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc st)) e o) :
    ∀ m tx' c' rel' sc', e.kind = .arrive m tx' c' rel' sc' → c' = n.toNat := by
  intro m tx' c' rel' sc' hk
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  have herr : ∀ f, Fires pc (widenMbarScope A t.pc (Tmpl.ub f)) e o → False := by
    intro f h
    simp only [widenMbarScope] at h
    split_ifs at h <;> (simp only [Fires] at h; rw [h.1] at hk; cases hk)
  cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hf
  · cases hm : mbarLoc L g t base off with
    | error f => rw [hm] at hf; exact (herr f hf).elim
    | ok l =>
      rw [hm] at hf
      cases hb : readBits L g t 32 tx with
      | error f => rw [hb] at hf; exact (herr f hf).elim
      | ok bytes =>
        simp only [hb, hn, ofExec] at hf
        cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
        · rw [hf.1] at hk
          cases hk
          rfl
  · cases hm : mbarClusterLoc L g t base off with
    | error f => rw [hm] at hf; exact (herr f hf).elim
    | ok l =>
      rw [hm] at hf
      cases hb : readBits L g t 32 tx with
      | error f => rw [hb] at hf; exact (herr f hf).elim
      | ok bytes =>
        simp only [hb, hn, ofExec] at hf
        cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
        · rw [hf.1] at hk
          cases hk
          rfl

/-- An arrival with the immediate count `1` arrives once. -/
theorem fires_arrive_one {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {st : Option Nat} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx (.imm 1) cluster rel sc st)) e o) :
    ∀ m tx' c' rel' sc', e.kind = .arrive m tx' c' rel' sc' → c' = 1 := by
  intro m tx' c' rel' sc' hk
  have h := fires_arrive_count (n := truncBits 32 (BitVec.ofInt 64 1))
    (by simp [readBits, pure, Except.pure]) hf m tx' c' rel' sc' hk
  rw [h]
  decide

/-- An arrival whose object, byte count and count evaluate is not undefined behaviour. -/
theorem fires_arrive_notUb {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {rel : Bool} {sc : MbarScope}
    {st : Option Nat} {pc : Nat} {e : Event} {o : Option TState} {m : Loc} {b n : BitVec 64}
    (hm : mbarLoc L g t base off = .ok m) (hb : readBits L g t 32 tx = .ok b)
    (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count false rel sc st)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  intro f hk
  simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hb, hn, bind, Except.bind,
    pure, Except.pure, ofExec] at hf
  cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  · rw [hf.1] at hk
    cases hk

end
end PTX.Flow
