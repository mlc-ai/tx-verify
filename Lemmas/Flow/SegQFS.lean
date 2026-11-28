-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedSingleG

@[expose] public section

/-! # A single piece whose end table is `[(d, tag)] ++ qt pc`

`segQ_single` checks the whole table at the next pc (`afterF`); when that table is the one at the
single's pc with the written register in front, the typed state follows without a check. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The check of a single at a pc without the end table: the instruction is one, with the needs
held, and it writes `d`. -/
def singleOkD (op : Op) (qt : Nat → EnvF) (pc d : Nat) : Bool :=
  match singleNeeds op with
  | some nd => op.isLocal && needsIn nd.1 (qt pc) && decide (nd.2.1 = d)
  | none => false

theorem segQ_singleD {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {tg : TagF} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hk : singleOkD op qt pc d = true) (hT : (singleNeeds op).map (fun nd => nd.2.2) = some tg)
    (hq : qt (pc + 1) = [(d, tg)] ++ qt pc) (hS : SingleStep K A L g R pc)
    (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G := by
  unfold singleOkD at hk
  split at hk
  · rename_i nd hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨⟨hl, hN⟩, rfl⟩ := hk
    simp only [hn, Option.map_some, Option.some.injEq] at hT
    subst hT
    refine SegQ.local1 hc hl hG fun t ht ⟨hQ, hTau⟩ => ?_
    have hty : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
    obtain ⟨v, hex, hdv⟩ := hS op nd hc hn t ht.1 (typedF_of_needs hN hty) (hTau t .refl)
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := nd.2.1) (tg := nd.2.2) hdv
    refine ⟨_, hex, by simp [PTX.next, setReg, ht.1], rfl, rfl, rfl,
      fun p hp => by simp [setReg, PTX.next, hd p hp],
      fun hu => ⟨?_, fun w hw => hTau w (.head hu hw)⟩⟩
    have := typedF_cons hty hw1 hw2
    unfold QTF
    rw [show (PTX.next (setReg t nd.2.1 v)).pc = pc + 1 by simp [PTX.next, setReg, ht.1], hq]
    exact this
  · cases hk

end PTX.Flow.TyG
