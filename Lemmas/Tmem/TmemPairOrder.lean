-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Tmem.TmemPairCompletionFrame
public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Order.OrderBaseCausality

@[expose] public section

section
namespace PTX
noncomputable section

private theorem sums_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sums_strict {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) (x : α) (hx : x ∈ xs) (hlt : f x < g x) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    have hh := h y (by simp)
    have ht : ∀ z ∈ ys, f z ≤ g z := fun z hz => h z (by simp [hz])
    simp only [List.mem_cons] at hx
    simp only [List.map_cons, List.sum_cons]
    rcases hx with rfl | hx
    · have := sums_mono ys f g ht
      omega
    · have := ih ht hx
      omega

/-- A new allocator record makes progress even if no thread advances.
The caller must separately prove that the appended record is consistent. -/
theorem Execution.recordEntry_size (X : Execution) (L : Launch) (cta : Nat)
    (hk : cta < L.grid) (r : Tmem.Pair.Requests) : X.size L < (X.recordEntry cta r).size L := by
  have hs : X.pairSize L < (X.recordEntry cta r).pairSize L := by
    apply Nat.add_lt_add_right
    apply sums_strict _ _ _ ?_ cta (List.mem_range.mpr hk) ?_
    · intro k _
      by_cases he : k = cta <;> simp [Execution.recordEntry, he]
    · simp [Execution.recordEntry]
  exact Nat.add_lt_add_left hs _

/-- A new pairing makes progress even if no thread advances. -/
theorem Execution.recordPairing_size (X : Execution) (L : Launch)
    (q : Tmem.Pair.WarpRequest × Tmem.Pair.WarpRequest) :
    X.size L < (X.recordPairing q).size L := by
  have hs : X.pairSize L < (X.recordPairing q).pairSize L := by
    simp [Execution.pairSize, Execution.recordPairing]
  exact Nat.add_lt_add_left hs _

end
end PTX
end

section
/-! # The execution order of a Tensor Memory allocator history (OBJ-TMEM-ORDER)

`ObjectCoherent` with the object `.tmem cta` makes the history of CTA `cta` agree with
causality between the lanes of its records. Consequences: no lane event is recorded twice, and
the requests of one warp are recorded in its program order (`ObjectCoherent.tmemOrdered`). -/

namespace PTX.Tmem.Pair
noncomputable section

/-- A request of a warp is recorded after that warp's earlier requests. -/
def WarpRequest.Ordered (a b : WarpRequest) : Prop :=
  a.cta = b.cta → a.warp = b.warp → a.Before b

variable {L : Launch} {X : Execution}

/-- The order of one allocator is never contrary to causality: no lane of a later record
causally precedes (or is) a lane of an earlier record in the same CTA. -/
theorem _root_.PTX.ObjectCoherent.not_precedes (h : ObjectCoherent L X) {cta : Nat} {i j : EvId}
    (hp : Precedes L X cta i j)
    (hc : Relation.ReflTransGen (stageCausality L X) (.thread j, true) (.thread i, true)) : False :=
  h (.tmem cta) (.thread i, true) (Relation.TransGen.head'
    (show WithObject L X (.tmem cta) (.thread i, true) (.thread j, true) from
      .inr ⟨rfl, rfl, i, j, rfl, rfl, hp⟩)
    (Relation.ReflTransGen.mono (fun _ _ => Or.inl) _ _ hc))

/-- Two lanes of one thread in two records of a history: the earlier record's lane is earlier
in program order. -/
theorem _root_.PTX.ObjectCoherent.lane_lt (h : ObjectCoherent L X) {cta k l : Nat} {x y : Requests}
    (hx : (X.tmemHistory cta)[k]? = some x) (hy : (X.tmemHistory cta)[l]? = some y) (hkl : k < l)
    {e f : EvId} (he : Participates L x.own e) (hf : Participates L y.own f) (ht : e.1 = f.1)
    (hev : ∃ ev, X.get e = some ev) (hna : (X.get e).bind Event.acc = none) : e.2 < f.2 := by
  by_contra hn
  have hp : Precedes L X cta e f := ⟨k, l, x, y, hx, hy, hkl, he, hf⟩
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hn) with heq | hlt
  · have hef : f = e := Prod.ext ht.symm heq
    subst hef
    exact h.not_precedes hp .refl
  · obtain ⟨ev, hget⟩ := hev
    have hpo : po X f e := po_of_not_access ht.symm hlt (len_of_get hget) hna
    have h1 : stageCausality L X (.thread f, true) (.thread e, false) :=
      .inr (.inl ⟨rfl, rfl, f, e, rfl, rfl, .single (.inl hpo)⟩)
    have h2 : stageCausality L X (.thread e, false) (.thread e, true) :=
      .inl (.inl ⟨rfl, rfl, rfl, ⟨ev, hget⟩⟩)
    exact h.not_precedes hp (.tail (.single h1) h2)

/-- The lane events of a valid warp request exist. -/
theorem WarpRequest.Valid.get {group : CtaGroup} {w : WarpRequest} (hw : w.Valid L X group)
    (lane : Fin 32) : ∃ ev, X.get (w.event L lane) = some ev :=
  ⟨_, hw.2.2.1 lane⟩

theorem WarpRequest.Valid.not_access {group : CtaGroup} {w : WarpRequest} (hw : w.Valid L X group)
    (lane : Fin 32) : (X.get (w.event L lane)).bind Event.acc = none := by
  simp [hw.2.2.1 lane, Event.acc]

/-- Two warp requests of one warp recorded in a history are in its program order. -/
theorem _root_.PTX.ObjectCoherent.warp_ordered (h : ObjectCoherent L X) {cta k l : Nat}
    {x y : Requests}
    (hx : (X.tmemHistory cta)[k]? = some x) (hy : (X.tmemHistory cta)[l]? = some y) (hkl : k < l)
    {group : CtaGroup} (ha : x.own.Valid L X group) : x.own.Ordered y.own := by
  intro hc hw
  refine ⟨hc, hw, fun lane => ?_⟩
  have ht : (x.own.event L lane).1 = (y.own.event L lane).1 := by
    simp only [WarpRequest.event, hc, hw]
  exact h.lane_lt hx hy hkl ⟨lane, rfl⟩ ⟨lane, rfl⟩ ht (ha.get lane) (ha.not_access lane)

/-- OBJ-TMEM-ORDER: the requests of one warp in a history are in its program order. -/
theorem _root_.PTX.ObjectCoherent.tmemOrdered (h : ObjectCoherent L X) (hh : HistoriesOk L X)
    (cta : Nat) : (X.tmemHistory cta).Pairwise fun a b => a.own.Ordered b.own := by
  rw [List.pairwise_iff_getElem]
  intro k l hk hl hkl
  exact h.warp_ordered (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hl) hkl
    ((hh.1 cta).1 _ (List.getElem_mem hk)).2.2

end
end PTX.Tmem.Pair
end
