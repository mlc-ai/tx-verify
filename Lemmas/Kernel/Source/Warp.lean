-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NthEv

@[expose] public section

/-! # Source of a returned value: a warp collective

A proof tool, generic over the kernel. What a shuffle or ballot returns comes from the lanes of
the warp at the same instance (DEP-WARP-SHFL, DEP-WARP-VOTE): the instance is fixed by the count
of the lane's earlier collectives of its kind. A kernel shows that every lane runs one common
sequence of collectives; then the source lanes at an instance are at the same position of that
sequence, and hold the reference values there by induction on the collectives before.

* `coll_le`: the order of two kinds of collectives along a lane. When a lane that has made at most
  `s` events of kind `S` could have made more than `v` events of kind `V` only by being, at its
  `v`-th `V` event, past `s` events of kind `S` (the kernel's position fact, from its common
  sequence), it has made at most `v` events of kind `V`. This bounds the source lane's position
  at an instance.
* `coll_induction`: the induction that proves the reference values of all lanes: on a measure of
  positions (the collectives before them) and along each lane. A step of a lane may use the
  values at every position of every lane whose measure is at most its own, when the step's event
  increases the measure (it is a collective); this is `Frame.inductive_lex` on positions. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {X : Execution}

/-- The events of kind `p` among lane `h`'s first `j`. -/
abbrev cnt (X : Execution) (p : Event → Bool) (h j : Nat) : Nat := ((X.tr h).take j).countP p

/-- **A lane at most `s` events of kind `S` in is at most `v` events of kind `V` in**, when its
`v`-th event of kind `V` would be past `s` events of kind `S`. -/
theorem coll_le {S V : Event → Bool} {h s v : Nat} {Good : Nat → Prop}
    (IH : ∀ j, j < (X.tr h).length → cnt X S h j + cnt X V h j ≤ s + v → Good j)
    (hV : ∀ j e, X.get (h, j) = some e → V e = true → Good j → cnt X V h j = v →
      s < cnt X S h j)
    {j : Nat} (hsj : cnt X S h j ≤ s) : cnt X V h j ≤ v := by
  simp only [cnt] at *
  by_contra hgt
  obtain ⟨j0, e0, hj0, he0, hv0, hc0⟩ := exists_nthEv (X := X) (p := V) (g := h) (k := j) (n := v)
    (by omega)
  have hlen : j0 < (X.tr h).length := (List.getElem?_eq_some_iff.mp he0).1
  have hmono := countP_take_mono S (X.tr h) (Nat.le_of_lt hj0)
  have := hV j0 e0 he0 hv0 (IH j0 hlen (by omega)) hc0
  omega

/-- **Induction on the collectives before a position, and along each lane.** A lane's step
over an event of kind `c` may use `Good` at every position of every lane with at most as many
events of kind `c` before it. -/
theorem coll_induction {c : Event → Bool} {Q : Nat → Prop} {Good : Nat → Nat → Prop}
    {lo : Nat → Nat} (hbase : ∀ g, Q g → lo g ≤ (X.tr g).length → Good g (lo g))
    (hstep : ∀ g k e, Q g → lo g ≤ k → X.get (g, k) = some e → Good g k →
      (c e = true → ∀ h j, Q h → lo h ≤ j → j ≤ (X.tr h).length → cnt X c h j ≤ cnt X c g k →
        Good h j) → Good g (k + 1)) :
    ∀ g k, Q g → lo g ≤ k → k ≤ (X.tr g).length → Good g k := by
  suffices H : ∀ n g k, Q g → lo g ≤ k → k ≤ (X.tr g).length → cnt X c g k ≤ n → Good g k from
    fun g k hg hlo hk => H _ g k hg hlo hk le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g k hg hlo hk hn
  induction k, hlo using Nat.le_induction with
  | base => exact hbase g hg hk
  | succ k hlo ihk =>
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    have hsucc : cnt X c g (k + 1) = cnt X c g k + (if c e then 1 else 0) := by
      simp only [cnt]
      rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some,
        List.countP_append]
      simp [List.countP_singleton]
    have hle : cnt X c g k ≤ cnt X c g (k + 1) := by split at hsucc <;> omega
    refine hstep g k e hg hlo he (ihk (by omega) (by omega)) fun hc h j hh hlj hj hle' =>
      ih (cnt X c g k) (by rw [hc] at hsucc; simp only [↓reduceIte] at hsucc; omega) h j hh hlj
        hj hle'

end PTX.Frame
