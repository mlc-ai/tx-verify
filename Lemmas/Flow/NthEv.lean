-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

@[expose] public section

/-! # A thread's events of one kind, by their ordinals

A proof tool. Along one list, if before each `p`-element there are more `q`-elements than
earlier `p`-elements, then the `n`-th `p`-element can be matched with the `n`-th `q`-element: it
comes before it, and distinct `p`-elements get distinct `q`-elements (`exists_nth`,
`eq_of_count_eq`). Protocol proofs use the matching to compare counts of records of different
objects.

On a thread's trace: the event of thread `g` satisfying `p` with `n` earlier such events is at
position `nthEv X p g n` of `g`'s trace (`nthEv_spec`), past the trace when there is none
(`nthEv_lt_iff`). An event satisfying `p` is the one its count names (`nthEv_eq`). Ring protocols
index the arrivals, copies and commits of their threads this way. -/

namespace PTX.Flow

/-- The position of the `n`-th element satisfying `q` among those before position `k`. -/
theorem exists_nth {α : Type} (q : α → Bool) (es : List α) {n k : Nat}
    (h : n < (es.take k).countP q) :
    ∃ j < k, ∃ x, es[j]? = some x ∧ q x = true ∧ (es.take j).countP q = n := by
  induction k generalizing n with
  | zero => simp at h
  | succ k ih =>
    by_cases hk : k < es.length
    · have htake : es.take (k + 1) = es.take k ++ [es[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      rw [htake, List.countP_append, List.countP_singleton] at h
      by_cases hn : n < (es.take k).countP q
      · obtain ⟨j, hj, x, hx, hq, hc⟩ := ih hn
        exact ⟨j, by omega, x, hx, hq, hc⟩
      · have hqk : q es[k] = true := by
          by_contra hf
          simp [hf] at h
          omega
        simp only [hqk, ↓reduceIte] at h
        exact ⟨k, by omega, es[k], List.getElem?_eq_getElem hk, hqk, by omega⟩
    · have : es.take (k + 1) = es.take k := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [this] at h
      obtain ⟨j, hj, x, hx, hq, hc⟩ := ih h
      exact ⟨j, by omega, x, hx, hq, hc⟩

/-- Two `p`-positions with the same count of earlier `p`-elements are equal. -/
theorem eq_of_count_eq {α : Type} (p : α → Bool) (es : List α) {k k' : Nat} {x x' : α}
    (hx : es[k]? = some x) (hp : p x = true) (hx' : es[k']? = some x') (hp' : p x' = true)
    (hc : (es.take k).countP p = (es.take k').countP p) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hle : (es.take (k + 1)).countP p ≤ (es.take k').countP p := by
      apply List.Sublist.countP_le
      exact (List.take_sublist_take_left (by omega))
    have hk : k < es.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [List.take_add_one, List.getElem?_eq_getElem hk, List.countP_append] at hle
    have : es[k] = x := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hx)
    simp [this, hp] at hle
    omega
  · have hle : (es.take (k' + 1)).countP p ≤ (es.take k).countP p := by
      apply List.Sublist.countP_le
      exact (List.take_sublist_take_left (by omega))
    have hk : k' < es.length := (List.getElem?_eq_some_iff.mp hx').1
    rw [List.take_add_one, List.getElem?_eq_getElem hk, List.countP_append] at hle
    have : es[k'] = x' := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hx')
    simp [this, hp'] at hle
    omega

/-- The prefix counts of a list grow with the prefix. -/
theorem countP_take_mono {α : Type} (p : α → Bool) (es : List α) {i j : Nat} (hij : i ≤ j) :
    (es.take i).countP p ≤ (es.take j).countP p :=
  (List.take_sublist_take_left hij).countP_le

theorem countP_take_le_length {α : Type} (p : α → Bool) (es : List α) (j : Nat) :
    (es.take j).countP p ≤ j :=
  (List.countP_le_length).trans (by simp)

noncomputable section

variable {X : Execution}

open Classical in
/-- The position of thread `g`'s event satisfying `p` with `n` earlier such events; the end of
`g`'s trace when there is none. -/
def nthEv (X : Execution) (p : Event → Bool) (g n : Nat) : Nat :=
  if h : ∃ j e, X.get (g, j) = some e ∧ p e = true ∧ ((X.tr g).take j).countP p = n then
    Classical.choose h
  else (X.tr g).length

theorem countP_take_succ {p : Event → Bool} {g j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hp : p e = true) :
    ((X.tr g).take (j + 1)).countP p = ((X.tr g).take j).countP p + 1 := by
  have he' : (X.tr g)[j]? = some e := he
  rw [List.take_add_one, he', Option.toList_some, List.countP_append]
  simp [hp]

/-- Two events satisfying `p` with the same count are one. -/
theorem nthEv_unique {p : Event → Bool} {g j j' : Nat} {e e' : Event}
    (he : X.get (g, j) = some e) (hp : p e = true) (he' : X.get (g, j') = some e')
    (hp' : p e' = true) (hc : ((X.tr g).take j).countP p = ((X.tr g).take j').countP p) :
    j = j' :=
  eq_of_count_eq p (X.tr g) he hp he' hp' hc

/-- A thread with more than `n` events satisfying `p` among its first `k` made the one with `n`
earlier ones before position `k`. -/
theorem exists_nthEv {p : Event → Bool} {g k n : Nat}
    (h : n + 1 ≤ ((X.tr g).take k).countP p) :
    ∃ j e, j < k ∧ X.get (g, j) = some e ∧ p e = true ∧ ((X.tr g).take j).countP p = n := by
  obtain ⟨j, hj, e, he, hp, hc⟩ := exists_nth p (X.tr g) (n := n) (k := k) (by omega)
  exact ⟨j, e, hj, he, hp, hc⟩

/-- The event with `n` earlier ones, when the thread made more than `n`. -/
theorem nthEv_spec {p : Event → Bool} {g n : Nat} (h : n < (X.tr g).countP p) :
    ∃ e, X.get (g, nthEv X p g n) = some e ∧ p e = true ∧
      ((X.tr g).take (nthEv X p g n)).countP p = n := by
  have h' : n + 1 ≤ ((X.tr g).take (X.tr g).length).countP p := by
    rw [List.take_length]; omega
  obtain ⟨j, e, -, he, hp, hc⟩ := exists_nthEv h'
  have hex : ∃ j e, X.get (g, j) = some e ∧ p e = true ∧ ((X.tr g).take j).countP p = n :=
    ⟨j, e, he, hp, hc⟩
  unfold nthEv
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

/-- An event satisfying `p` is the one its count names. -/
theorem nthEv_eq {p : Event → Bool} {g j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hp : p e = true) : nthEv X p g (((X.tr g).take j).countP p) = j := by
  have hlt : ((X.tr g).take j).countP p < (X.tr g).countP p := by
    have h1 := countP_take_succ he hp
    have h2 := countP_take_mono p (X.tr g) (show j + 1 ≤ (X.tr g).length from
      (List.getElem?_eq_some_iff.mp he).1)
    rw [List.take_length] at h2
    omega
  obtain ⟨e', he', hp', hc'⟩ := nthEv_spec hlt
  exact nthEv_unique he' hp' he hp hc'

/-- The event's position is in the trace exactly when the thread made more than `n` events
satisfying `p`. -/
theorem nthEv_lt_iff {p : Event → Bool} {g n : Nat} :
    nthEv X p g n < (X.tr g).length ↔ n < (X.tr g).countP p := by
  constructor
  · intro hlt
    by_contra hn
    have hex : ¬ ∃ j e, X.get (g, j) = some e ∧ p e = true ∧ ((X.tr g).take j).countP p = n := by
      rintro ⟨j, e, he, hp, rfl⟩
      have h1 := countP_take_succ he hp
      have h2 := countP_take_mono p (X.tr g) (show j + 1 ≤ (X.tr g).length from
        (List.getElem?_eq_some_iff.mp he).1)
      rw [List.take_length] at h2
      omega
    unfold nthEv at hlt
    rw [dite_eq_right_of_eq_false (eq_false hex)] at hlt
    omega
  · intro h
    obtain ⟨e, he, -, -⟩ := nthEv_spec h
    exact (List.getElem?_eq_some_iff.mp he).1

/-- An event at the position of `nthEv` is the event with `n` earlier ones. -/
theorem nthEv_spec_of_get {p : Event → Bool} {g n : Nat} {e : Event}
    (he : X.get (g, nthEv X p g n) = some e) :
    p e = true ∧ ((X.tr g).take (nthEv X p g n)).countP p = n := by
  have hn := nthEv_lt_iff.mp (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨e', he', hp, hc⟩ := nthEv_spec hn
  rw [he] at he'
  cases he'
  exact ⟨hp, hc⟩

/-- A thread with more than `n` events satisfying `p` among its first `k` has the one with `n`
earlier ones before `k`. -/
theorem nthEv_lt {p : Event → Bool} {g k n : Nat} (h : n + 1 ≤ ((X.tr g).take k).countP p) :
    nthEv X p g n < k ∧ ∃ e, X.get (g, nthEv X p g n) = some e ∧ p e = true := by
  obtain ⟨j, e, hj, he, hp, hc⟩ := exists_nthEv h
  rw [← hc, nthEv_eq he hp]
  exact ⟨hj, e, he, hp⟩

end

end PTX.Flow
