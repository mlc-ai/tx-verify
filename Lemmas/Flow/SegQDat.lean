-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFS

@[expose] public section

/-! # A strict local piece that writes a four-byte datum

`segQ_dat`: an unguarded local instruction that writes the register `d` with a datum of four bytes
(the tag `.dat32`), when the caller shows from the state of the lane (the tags at the pc and the
fact `R` of the states it reaches) that the step succeeds. It is `segQ_singleD` for an instruction
that is not one of the single forms. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem segQ_dat {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hq : qt (pc + 1) = [(d, .dat32)] ++ qt pc) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d)
    (hs : ∀ t : TState, t.pc = pc → TypedF (qt pc) t → R t →
      ∃ v, execLocalA A L g t op = .ok (PTX.next (setReg t d v)) ∧ Dat32 v) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G := by
  refine SegQ.local1 hc hl hG fun t ht ⟨hQ, hTau⟩ => ?_
  have hty : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  obtain ⟨v, hex, hdv⟩ := hs t ht.1 hty (hTau t .refl)
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨v, rfl, hdv⟩
  refine ⟨_, hex, by simp [PTX.next, setReg, ht.1], rfl, rfl, rfl,
    fun p hp => by simp [setReg, PTX.next, hd p hp],
    fun hu => ⟨?_, fun w hw => hTau w (.head hu hw)⟩⟩
  have := typedF_cons hty hw1 hw2
  unfold QTF
  rw [show (PTX.next (setReg t d v)).pc = pc + 1 by simp [PTX.next, setReg, ht.1], hq]
  exact this

end PTX.Flow.TyG
