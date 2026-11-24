-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NthEv

@[expose] public section

/-! # The events of a class inside a wider class, by ordinal

A proof tool. `ordEv X p q g n` says whether thread `g`'s event of class `p` with `n` earlier ones
is of class `q`. When `q` is inside `p`, the events of class `q` among a prefix of the trace are
those of its events of class `p` by ordinal (`countP_ordinal`), so two lanes whose events of class
`p` agree on `q` by ordinal count in the order of their events of class `p`
(`countP_le_of_ordinal`). -/

namespace PTX.Flow
open PTX

noncomputable section

variable {X : Execution} {p q : Event → Bool}

/-- Whether thread `g`'s event of class `p` with `n` earlier ones is of class `q`. -/
def ordEv (X : Execution) (p q : Event → Bool) (g n : Nat) : Bool :=
  match X.get (g, nthEv X p g n) with
  | some e => q e
  | none => false

theorem ordEv_eq {g j : Nat} {e : Event} (he : X.get (g, j) = some e) (hp : p e = true) :
    ordEv X p q g (((X.tr g).take j).countP p) = q e := by
  rw [ordEv, nthEv_eq he hp, he]

/-- **The events of class `q` of a prefix are those of its events of class `p` by ordinal.** -/
theorem countP_ordinal (hqp : ∀ e, q e = true → p e = true) (g j : Nat) :
    ((X.tr g).take j).countP q =
      (List.range (((X.tr g).take j).countP p)).countP (ordEv X p q g) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.lt_or_ge j (X.tr g).length with hj | hj
    · have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
        List.countP_append, List.countP_append, ih]
      by_cases hv : p (X.tr g)[j] = true
      · simp only [List.countP_singleton, hv, ↓reduceIte, List.range_succ, List.countP_append]
        rw [ordEv_eq he hv]
      · have hnz : q (X.tr g)[j] = false := by
          rw [Bool.eq_false_iff]; exact fun h => hv (hqp _ h)
        simp [hv, hnz]
    · rw [List.take_of_length_le hj, List.take_of_length_le (by omega)] at *
      exact ih

/-- **Counts by ordinal are monotone**: a lane with at least as many events of class `p`, which
agree with the other lane's on `q` by ordinal, has at least as many of class `q`. -/
theorem countP_le_of_ordinal {g h j k : Nat} (hqp : ∀ e, q e = true → p e = true)
    (hle : ((X.tr g).take j).countP p ≤ ((X.tr h).take k).countP p)
    (heq : ∀ n < ((X.tr g).take j).countP p, ordEv X p q g n = ordEv X p q h n) :
    ((X.tr g).take j).countP q ≤ ((X.tr h).take k).countP q := by
  rw [countP_ordinal hqp, countP_ordinal hqp]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, List.range_add, List.countP_append]
  refine Nat.le_add_right_of_le (le_of_eq (List.countP_congr fun n hn => ?_))
  rw [heq n (List.mem_range.mp hn)]

end
end PTX.Flow
