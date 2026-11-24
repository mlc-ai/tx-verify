-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-! # The lanes of a warp make the same barrier events

A proof tool for ERR-BARRIER-MISMATCH (`BarArriveMismatch`). When the lanes of every warp make
the same CTA barrier events in the same order (`WarpBars`: of two lanes, one's sequence of
barrier events is a prefix of the other's), two lanes' barrier events with the same ordinal, among
all barrier events or among those on one barrier, are the same event (`WarpBars.same_event`).
So no `bar.arrive` lane disagrees with a lane of its warp (`WarpBars.not_barArriveMismatch`); two
barrier lanes of one warp with the same key are one site (`WarpBars.event_eq_of_key`). -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

/-- The lanes of every warp make the same CTA barrier events in the same order. -/
def WarpBars (L : Launch) (X : Execution) : Prop :=
  ∀ g h, SameWarp L g h → (X.tr g).filter Execution.isBar <+: (X.tr h).filter Execution.isBar ∨
    (X.tr h).filter Execution.isBar <+: (X.tr g).filter Execution.isBar

/-- The entry of a list at index `i`, selected by `p`, is entry number `(xs.take i).countP p` of
the selected entries. -/
theorem getElem_filter_countP {α : Type} {p : α → Bool} {xs : List α} {i : Nat} {x : α}
    (hx : xs[i]? = some x) (hp : p x = true) : (xs.filter p)[(xs.take i).countP p]? = some x := by
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hd : xs.drop i = x :: xs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.mp hx).2]
  have hf : xs.filter p = (xs.take i).filter p ++ x :: (xs.drop (i + 1)).filter p := by
    conv_lhs => rw [← List.take_append_drop i xs]
    rw [List.filter_append, hd, List.filter_cons_of_pos hp]
  rw [hf, List.getElem?_append_right (by rw [List.countP_eq_length_filter]),
    List.countP_eq_length_filter]
  simp

/-- Two lists of which one is a prefix of the other agree where both have entries. -/
theorem prefix_entry {α : Type} {l1 l2 : List α} (h : l1 <+: l2 ∨ l2 <+: l1) {n : Nat} {x y : α}
    (hx : l1[n]? = some x) (hy : l2[n]? = some y) : x = y := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1, hx] at hy
    exact Option.some.inj hy
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hy).1, hy] at hx
    exact (Option.some.inj hx).symm

variable {L : Launch} {X : Execution}

/-- **Two lanes of a warp agree on their barrier events of one ordinal**, counted among the
events selected by `q`, a selection of barrier events. -/
theorem WarpBars.same_event (hw : WarpBars L X) {g h i j : Nat} (hs : SameWarp L g h)
    {q : Event → Bool} (hq : ∀ e, q e = true → Execution.isBar e = true) {ev ev' : Event}
    (hgi : X.get (g, i) = some ev) (hhj : X.get (h, j) = some ev') (h1 : q ev = true)
    (h2 : q ev' = true)
    (hord : ((X.tr g).take i).countP q = ((X.tr h).take j).countP q) : ev = ev' := by
  have hsel : ∀ xs : List Event, (xs.filter Execution.isBar).filter q = xs.filter q := by
    intro xs
    rw [List.filter_filter]
    congr 1
    funext e
    cases hqe : q e
    · simp
    · simp [hq e hqe]
  have hpre : (X.tr g).filter q <+: (X.tr h).filter q ∨
      (X.tr h).filter q <+: (X.tr g).filter q := by
    rcases hw g h hs with hp | hp
    · exact .inl (by rw [← hsel, ← hsel (X.tr h)]; exact hp.filter q)
    · exact .inr (by rw [← hsel, ← hsel (X.tr g)]; exact hp.filter q)
  have hx := getElem_filter_countP (p := q) (show (X.tr g)[i]? = some ev from hgi) h1
  have hy := getElem_filter_countP (p := q) (show (X.tr h)[j]? = some ev' from hhj) h2
  rw [hord] at hx
  exact prefix_entry hpre hx hy

/-- **With warp-uniform barrier events, no `bar.arrive` mismatch.** -/
theorem WarpBars.not_barArriveMismatch (hw : WarpBars L X) : ¬ BarArriveMismatch L X := by
  rintro ⟨g, h, i, j, id, id', count, count', mode', pc, pc', hs, hgi, hhj, hord, hne⟩
  have hb : ∀ e, Execution.isBar e = true → Execution.isBar e = true := fun _ h => h
  have heq := hw.same_event hs hb hgi hhj (by simp [Execution.isBar])
    (by simp [Execution.isBar]) hord
  simp only [Event.mk.injEq, Kind.bar.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  simp at hne

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0} {count : Option Nat} {p : Finset Nat}
  {id : Nat}

/-- **Two lanes of a warp arriving in one generation make the same event.** -/
theorem WarpBars.event_eq_of_key (hw : WarpBars L X) (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id) (hG : Shape L count p id) {e f : EvId} {key pc pc' : Nat}
    {cnt cnt' : Option Nat} {m m' : BarMode} (hs : SameWarp L e.1 f.1)
    (hke : CtaBarArrivalK L X e key) (hkf : CtaBarArrivalK L X f key)
    (he : X.get e = some ⟨pc, .bar id cnt m⟩) (hf : X.get f = some ⟨pc', .bar id cnt' m'⟩) :
    pc = pc' ∧ cnt = cnt' ∧ m = m' := by
  have h1 := hS.arrival_key hX hG he hke
  have h2 := hS.arrival_key hX hG hf hkf
  have hord : ((X.tr e.1).take e.2).countP (Execution.isBarId id) =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by omega
  have heq := hw.same_event hs (fun _ h => isBar_of_isBarId h) he hf
    (by simp [Execution.isBarId]) (by simp [Execution.isBarId]) hord
  simp only [Event.mk.injEq, Kind.bar.injEq] at heq
  exact ⟨heq.1, heq.2.2.1, heq.2.2.2⟩

end
end PTX.NamedBar
