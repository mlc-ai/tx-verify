-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairHistory
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

namespace PTX.Tmem

/-- The action that performs an allocation request is an allocation of its column count. -/
theorem Action.request_eq_alloc {a : Action} {n : Nat} (h : a.request = .alloc n) :
    ∃ c, a = .alloc n c := by
  cases a <;> simp_all [Action.request]

theorem Action.request_eq_dealloc {a : Action} {b n : Nat} (h : a.request = .dealloc b n) :
    a = .dealloc b n := by
  cases a <;> simp_all [Action.request]

theorem Action.request_eq_relinquish {a : Action} (h : a.request = .relinquish) :
    a = .relinquish := by
  cases a <;> simp_all [Action.request]

end PTX.Tmem

namespace PTX.Tmem.Pair
noncomputable section

theorem WarpRequest.Before.irrefl (a : WarpRequest) : ¬ a.Before a := by
  intro h
  exact Nat.lt_irrefl _ (h.2.2 0)

theorem WarpRequest.Before.trans {a b c : WarpRequest} (h : a.Before b) (k : b.Before c) :
    a.Before c :=
  ⟨h.1.trans k.1, h.2.1.trans k.2.1, fun lane => (h.2.2 lane).trans (k.2.2 lane)⟩

/-- Erasing the entire instruction trace cannot retain a nonempty request history. -/
theorem no_ghost_history (L : Launch) (X : Execution) (r : Requests) (rest : List Requests)
    (h : RequestHistory L X (r :: rest)) :
    ∃ ev, X.get (r.own.event L 0) = some ev :=
  ⟨_, (h r (by simp)).2.2.2.2.1 0⟩

/-- Extension keeps every complete operation complete. -/
theorem Completed.mono {X Y : Execution} {ws : List WarpRequest}
    (h : X.le Y) (hc : Completed X ws) : Completed Y ws := by
  rcases hc with ⟨cta, r, hr, hg, rfl⟩ | ⟨q, hq, rfl⟩
  · exact .inl ⟨cta, r, (Execution.le_tmemHistory h cta).subset hr, hg, rfl⟩
  · exact .inr ⟨q, (Execution.le_tmemPairing h).subset hq, rfl⟩

/-- Extension cannot turn a recorded completion back into a pending request. -/
theorem Covered.mono {L : Launch} {X Y : Execution} {i : EvId}
    (h : X.le Y) (hc : Covered L X i) : Covered L Y i := by
  obtain ⟨ws, hws, w, hw, hi⟩ := hc
  exact ⟨ws, hws.mono h, w, hw, hi⟩

/-- Every warp request of a complete operation is an actual warp request. -/
theorem Completed.valid {L : Launch} {X : Execution} {ws : List WarpRequest}
    (hv : HistoriesOk L X) (hc : Completed X ws) {w : WarpRequest} (hw : w ∈ ws) :
    ∃ group, w.Valid L X group := by
  rcases hc with ⟨cta, r, hr, -, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, ((hv.1 cta).1 r hr).2.2⟩
  · have hp := (hv.2.1 q hq).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨_, hp.2.1⟩
    · exact ⟨_, hp.2.2.1⟩

/-- A covered event is a lane of an actual warp request. -/
theorem Covered.request {L : Launch} {X : Execution} {i : EvId}
    (hv : HistoriesOk L X) (hc : Covered L X i) :
    ∃ w group, w.Valid L X group ∧ Participates L w i := by
  obtain ⟨ws, hws, w, hw, hi⟩ := hc
  obtain ⟨group, hg⟩ := hws.valid hv hw
  exact ⟨w, group, hg, hi⟩

/-- Provenance ties coverage back to a real paired instruction at that event id. -/
theorem Covered.actual {L : Launch} {X : Execution} {i : EvId}
    (hv : HistoriesOk L X) (hc : Covered L X i) :
    ∃ pc group dst action, X.get i = some ⟨pc, .tc (.resource group dst action)⟩ := by
  obtain ⟨w, group, hw, lane, rfl⟩ := hc.request hv
  exact ⟨w.pc, group, w.dst, w.request, hw.2.2.1 lane⟩

/-- Both lanes of an allocator order edge are lanes of records of that CTA's history. -/
theorem Precedes.recorded {L : Launch} {X : Execution} {cta : Nat} {i j : EvId}
    (h : Precedes L X cta i j) :
    (∃ x ∈ X.tmemHistory cta, Participates L x.own i) ∧
      ∃ y ∈ X.tmemHistory cta, Participates L y.own j := by
  obtain ⟨k, l, x, y, hx, hy, -, hi, hj⟩ := h
  exact ⟨⟨x, List.mem_of_getElem? hx, hi⟩, ⟨y, List.mem_of_getElem? hy, hj⟩⟩

/-- The source of an allocator order edge is an actual allocation-management event. -/
theorem Precedes.actual {L : Launch} {X : Execution} {cta : Nat} {i j : EvId}
    (hv : HistoriesOk L X) (h : Precedes L X cta i j) :
    ∃ pc group dst action, X.get i = some ⟨pc, .tc (.resource group dst action)⟩ := by
  obtain ⟨x, hx, lane, rfl⟩ := h.recorded.1
  have hxv := ((hv.1 cta).1 x hx).2.2
  exact ⟨x.own.pc, x.group, x.own.dst, x.own.request, hxv.2.2.1 lane⟩

/-- The lanes of a valid warp request are one warp of its CTA. -/
theorem WarpRequest.event_props {L : Launch} {X : Execution} {group : CtaGroup} {w : WarpRequest}
    (hv : w.Valid L X group)
    (l : Fin 32) : (w.event L l).1 / L.block = w.cta ∧ (w.event L l).1 % L.block / 32 = w.warp ∧
      (w.event L l).1 < L.threads := by
  obtain ⟨hc, hw, -, -⟩ := hv
  have hl := l.isLt
  have hlt : w.warp * 32 + l.val < L.block := by omega
  have hb : 0 < L.block := by omega
  simp only [WarpRequest.event]
  have e1 : w.cta * L.block + w.warp * 32 + l.val = (w.warp * 32 + l.val) + L.block * w.cta := by
    ring
  rw [e1, Nat.add_mul_div_left _ _ hb, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hlt,
    Nat.mod_eq_of_lt hlt]
  refine ⟨by simp, by omega, ?_⟩
  unfold Launch.threads
  nlinarith

theorem WarpRequest.event_sameWarp {L : Launch} {X : Execution} {group : CtaGroup}
    {w : WarpRequest} (hv : w.Valid L X group)
    (i j : Fin 32) : SameWarp L (w.event L i).1 (w.event L j).1 := by
  obtain ⟨hi1, hi2, hi3⟩ := WarpRequest.event_props hv i
  obtain ⟨hj1, hj2, hj3⟩ := WarpRequest.event_props hv j
  exact ⟨⟨hi3, hj3, hi1.trans hj1.symm⟩, hi2.trans hj2.symm⟩

/-- A recorded lane of a warp collective: every lane of its warp has executed that collective
instance. -/
theorem WarpRequest.Valid.tcDone {L : Launch} {X : Execution} {f : EvId} {k : Nat}
    {w : WarpRequest} {grp : CtaGroup} (hw : w.Valid L X grp) (hp : Participates L w f)
    (hk : X.TcK f k) :
    ∀ h < L.threads, SameWarp L f.1 h → ∃ j, X.TcK (h, j) k := by
  obtain ⟨l0, rfl⟩ := hp
  obtain ⟨k', hk'⟩ := hw.2.2.2
  have hkk : k' = k := (hk' l0).2.symm.trans hk.2
  intro h _ hsw
  obtain ⟨p1, p2, -⟩ := WarpRequest.event_props hw l0
  have hcta : h / L.block = w.cta := by rw [← hsw.1.2.2, p1]
  have hwarp : h % L.block / 32 = w.warp := by rw [← hsw.2, p2]
  let l : Fin 32 := ⟨h % L.block % 32, Nat.mod_lt _ (by decide)⟩
  refine ⟨w.indices l, ?_⟩
  have heq : w.event L l = (h, w.indices l) := by
    have e1 := Nat.div_add_mod h L.block
    have e2 := Nat.div_add_mod (h % L.block) 32
    rw [hcta] at e1
    rw [hwarp] at e2
    show (w.cta * L.block + w.warp * 32 + h % L.block % 32, w.indices l) = (h, w.indices l)
    rw [Nat.mul_comm w.cta]
    congr 1
    omega
  rw [← heq, ← hkk]
  exact hk' l

/-- A covered lane of a warp collective: every lane of its warp has executed that collective
instance. -/
theorem Covered.tcDone {L : Launch} {X : Execution} {f : EvId} {k : Nat} (hv : HistoriesOk L X)
    (hc : Covered L X f) (hk : X.TcK f k) :
    ∀ h < L.threads, SameWarp L f.1 h → ∃ j, X.TcK (h, j) k := by
  obtain ⟨w, grp, hw, hp⟩ := hc.request hv
  exact hw.tcDone hp hk

/-- A warp-collective ordinal is fixed once its event exists. -/
theorem _root_.PTX.Execution.TcK.mono {X Y : Execution} (h : X.le Y) {e : EvId} {k : Nat}
    (hk : X.TcK e k) : Y.TcK e k := by
  obtain ⟨⟨ev, he, hc⟩, hn⟩ := hk
  refine ⟨⟨ev, Execution.le_get h he, hc⟩, ?_⟩
  obtain ⟨suffix, hs⟩ := h.1 e.1
  have hi := len_of_get he
  rw [← hs, List.take_append_of_le_length hi.le]
  exact hn

private theorem countP_take_strict {p : Event → Bool} {l : List Event} {i j : Nat} {e : Event}
    (he : l[i]? = some e) (hp : p e = true) (hij : i < j) :
    (l.take i).countP p < (l.take j).countP p := by
  have h1 : (l.take (i + 1)).countP p = (l.take i).countP p + 1 := by
    rw [List.take_add_one, List.countP_append, he]; simp [hp]
  have h2 : (l.take (i + 1)).countP p ≤ (l.take j).countP p :=
    (List.take_sublist_take_left (by omega)).countP_le
  omega

/-- A thread's warp-collective ordinal names one event. -/
theorem _root_.PTX.Execution.TcK.unique {X : Execution} {g i j k : Nat} (hi : X.TcK (g, i) k)
    (hj : X.TcK (g, j) k) : i = j := by
  obtain ⟨⟨ev, he, hc⟩, hci⟩ := hi
  obtain ⟨⟨ev', he', hc'⟩, hcj⟩ := hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := countP_take_strict (p := isTcColl) he hc h
    simp only at hci hcj this
    omega
  · exact h
  · have := countP_take_strict (p := isTcColl) he' hc' h
    simp only at hci hcj this
    omega

/-- Two actual warp requests with a common lane event are the same instruction instance. -/
theorem WarpRequest.Valid.ext {L : Launch} {X : Execution} {w w' : WarpRequest}
    {g g' : CtaGroup} (hv : w.Valid L X g) (hv' : w'.Valid L X g') {l l' : Fin 32}
    (he' : w.event L l = w'.event L l') : w = w' := by
  obtain ⟨p1, p2, -⟩ := WarpRequest.event_props hv l
  obtain ⟨q1, q2, -⟩ := WarpRequest.event_props hv' l'
  have hc : w.cta = w'.cta := by rw [← p1, ← q1, he']
  have hw : w.warp = w'.warp := by rw [← p2, ← q2, he']
  have hll : l = l' := by
    have h1 := congrArg Prod.fst he'
    simp only [WarpRequest.event, hc, hw] at h1
    exact Fin.ext (by omega)
  subst hll
  have he := he'
  obtain ⟨k, hk⟩ := hv.2.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2.2
  have hkk : k = k' := (hk l).2.symm.trans (by rw [he]; exact (hk' l).2)
  have hidx : ∀ lane, w.indices lane = w'.indices lane := by
    intro lane
    have a := hk lane
    have b := hk' lane
    rw [hkk] at a
    have hev : w.event L lane = ((w'.event L lane).1, w.indices lane) := by
      simp [WarpRequest.event, hc, hw]
    rw [hev] at a
    exact Execution.TcK.unique a b
  have hget := hv.2.2.1 l
  rw [he, hv'.2.2.1 l] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hget
  obtain ⟨hpc, -, hdst, hreq⟩ := hget
  obtain ⟨c, wa, i, pc, d, r⟩ := w
  obtain ⟨c', wa', i', pc', d', r'⟩ := w'
  simp only at hc hw hidx hpc hdst hreq ⊢
  subst hc hw hpc hdst hreq
  have := funext hidx
  subst this
  rfl

theorem WarpRequest.Valid.mono {L : Launch} {X Y : Execution} {group : CtaGroup}
    {w : WarpRequest} (h : X.le Y) (hw : w.Valid L X group) : w.Valid L Y group := by
  obtain ⟨h1, h2, hev, k, hk⟩ := hw
  exact ⟨h1, h2, fun lane => Execution.le_get h (hev lane), k, fun lane => (hk lane).mono h⟩

theorem Requests.Valid.mono {L : Launch} {X Y : Execution} {r : Requests}
    (h : X.le Y) (hr : r.Valid L X) : r.Valid L Y :=
  ⟨hr.1, hr.2.1, hr.2.2.mono h⟩

theorem PairValid.mono {L : Launch} {X Y : Execution} {q : WarpRequest × WarpRequest}
    (h : X.le Y) (hq : PairValid L X q) : PairValid L Y q :=
  ⟨hq.1, hq.2.1.mono h, hq.2.2.1.mono h, hq.2.2.2⟩

/-- Unchanged histories and pairings remain valid as their events persist. -/
theorem HistoriesOk.mono {L : Launch} {X Y : Execution} (hv : HistoriesOk L X) (h : X.le Y)
    (hp : ∀ cta, Y.tmemHistory cta = X.tmemHistory cta) (hq : Y.tmemPairing = X.tmemPairing) :
    HistoriesOk L Y := by
  obtain ⟨hh, hpair, hdist⟩ := hv
  refine ⟨fun cta => ?_, ?_, ?_⟩
  · rw [hp cta]
    obtain ⟨hval, hcta, hrun⟩ := hh cta
    exact ⟨fun r hr => (hval r hr).mono h, hcta, hrun⟩
  · rw [hq]
    intro q hqm
    obtain ⟨hv, ⟨a, ha, ha'⟩, b, hb, hb'⟩ := hpair q hqm
    exact ⟨hv.mono h, ⟨a, by rwa [hp], ha'⟩, b, by rwa [hp], hb'⟩
  · rw [hq]; exact hdist

/-- An issued instruction's peer wait cannot disappear in an extension. -/
theorem MustWait.mono {X Y : Execution} {i : EvId}
    (h : X.le Y) (hw : MustWait X i) : MustWait Y i := by
  obtain ⟨pc, group, dst, action, he, hw⟩ := hw
  refine ⟨pc, group, dst, action, Execution.le_get h he, ?_⟩
  cases action with
  | alloc n => trivial
  | dealloc col n => exact (Execution.le_tmemPairBlocks h he).symm ▸ hw
  | relinquish => exact (Execution.le_tmemPairBlocks h he).symm ▸ hw

/-- An extension adds no peer wait to an event that is already present. -/
theorem MustWait.of_le {X Y : Execution} {i : EvId} (h : X.le Y)
    (hi : i.2 < (X.tr i.1).length) (hw : MustWait Y i) : MustWait X i := by
  obtain ⟨pc, group, dst, action, he, hw⟩ := hw
  obtain ⟨ev, hev⟩ : ∃ ev, X.get i = some ev := ⟨_, List.getElem?_eq_getElem hi⟩
  have hY := Execution.le_get h hev
  rw [he] at hY
  cases hY
  refine ⟨pc, group, dst, action, hev, ?_⟩
  cases action with
  | alloc n => trivial
  | dealloc col n => exact (Execution.le_tmemPairBlocks h hev) ▸ hw
  | relinquish => exact (Execution.le_tmemPairBlocks h hev) ▸ hw

/-- Extension keeps every performed request performed. -/
theorem Performed.mono {L : Launch} {X Y : Execution} {i : EvId}
    (h : X.le Y) (hp : Performed L X i) : Performed L Y i := by
  obtain ⟨cta, r, hr, hi⟩ := hp
  exact ⟨cta, r, (Execution.le_tmemHistory h cta).subset hr, hi⟩

/-- A covered event is performed: a pairing pairs two recorded requests. -/
theorem Covered.performed {L : Launch} {X : Execution} {i : EvId}
    (hv : HistoriesOk L X) (hc : Covered L X i) : Performed L X i := by
  obtain ⟨ws, hws, w, hw, hi⟩ := hc
  rcases hws with ⟨cta, r, hr, -, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [List.mem_singleton.mp hw] at hi
    exact ⟨cta, r, hr, hi⟩
  · obtain ⟨-, ⟨a, ha, ha1, -⟩, b, hb, hb1, -⟩ := hv.2.1 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨_, a, ha, ha1 ▸ hi⟩
    · exact ⟨_, b, hb, hb1 ▸ hi⟩

/-- What the return of allocation-management event `i` requires: its CTA's allocator has
performed its request, and its operation is complete if it waits for that. These are the
`Tmem.Pair.Performed` and `Tmem.Pair.Covered` needs of the `tcgen05` arm of `KindNeeds`; the arm
holds them of every returned event (`DependencyOk.ready`), which `of_ready` reads off. -/
def ReturnReady (L : Launch) (X : Execution) (i : EvId) : Prop :=
  Performed L X i ∧ (MustWait X i → Covered L X i)

/-- A ready allocation-management event is ready to return: the resource arm of `KindNeeds` holds
its performed condition, and its covered condition when it waits. -/
theorem ReturnReady.of_ready {L : Launch} {X : Execution} {i : EvId} {pc : Nat}
    {group : CtaGroup} {dst : Option Loc} {request : Request}
    (he : X.get i = some ⟨pc, .tc (.resource group dst request)⟩) (h : Ready L X i) :
    ReturnReady L X i := by
  have hEq : Needs L X i = resourceNeeds L X i group request := by
    unfold Needs
    rw [he]
    rfl
  have hpos : Need.cond (Performed L X i) ∈ Needs L X i := by
    rw [hEq]
    simp [resourceNeeds]
  refine ⟨h _ hpos, fun hm => ?_⟩
  have hcov : Need.cond (Covered L X i) ∈ Needs L X i := by
    rw [hEq]
    simp [resourceNeeds, needsIf, eq_true hm]
  exact h _ hcov

/-- An extension keeps what the return of a present event requires. -/
theorem ReturnReady.mono {L : Launch} {X Y : Execution} {i : EvId} (h : X.le Y)
    (hi : i.2 < (X.tr i.1).length) (hr : ReturnReady L X i) : ReturnReady L Y i :=
  ⟨hr.1.mono h, fun hm => (hr.2 (hm.of_le h hi)).mono h⟩

/-- Every returned allocation-management event is ready: the `tcgen05` arm of
`DependencyOk.ready`, which replaces the per-form waiting predicate of the earlier layer. -/
def Blocking (L : Launch) (X : Execution) : Prop :=
  ∀ i pc group dst request, X.get i = some ⟨pc, .tc (.resource group dst request)⟩ →
    i.2 + 1 < (X.tr i.1).length → Ready L X i

/-- A waiting event with a later event of its thread is covered. -/
theorem Blocking.covered {L : Launch} {X : Execution} (h : Blocking L X) {i : EvId}
    (hm : MustWait X i) (hl : i.2 + 1 < (X.tr i.1).length) : Covered L X i := by
  obtain ⟨pc, group, dst, request, he, -⟩ := id hm
  exact (ReturnReady.of_ready he (h i pc group dst request he hl)).2 hm

/-- An allocation-management event with a later event of its thread is performed. -/
theorem Blocking.performed {L : Launch} {X : Execution} (h : Blocking L X) {i : EvId}
    {pc : Nat} {group : CtaGroup} {dst : Option Loc} {request : Request}
    (he : X.get i = some ⟨pc, .tc (.resource group dst request)⟩)
    (hl : i.2 + 1 < (X.tr i.1).length) : Performed L X i :=
  (ReturnReady.of_ready he (h i pc group dst request he hl)).1

/-- A thread event after an allocation request is already covered. -/
def AllocBlocking (L : Launch) (X : Execution) : Prop :=
  ∀ i pc group dst n, X.get i = some ⟨pc, .tc (.resource group dst (.alloc n))⟩ →
    i.2 + 1 < (X.tr i.1).length → Covered L X i

/-- The general choice-sensitive rule includes mandatory allocation blocking. -/
theorem Blocking.alloc {L : Launch} {X : Execution} (h : Blocking L X) :
    AllocBlocking L X := by
  intro i pc group dst n he hn
  exact h.covered ⟨pc, group, dst, .alloc n, he, trivial⟩ hn

/-- **The requests of a warp are performed in program order.** An earlier request `w` of the warp
of an actual request `v` has returned, since `v`'s lanes follow it, so its CTA's allocator has
performed it (DEP-TMEM-ALLOC-WAIT). -/
theorem recorded_of_before {L : Launch} {X : Execution} (hh : HistoriesOk L X)
    (hb : Blocking L X) {w v : WarpRequest} {g g' : CtaGroup} (hw : w.Valid L X g)
    (hv : v.Valid L X g') (hbef : w.Before v) : ∃ x ∈ X.tmemHistory w.cta, x.own = w := by
  have hget := hw.2.2.1 0
  have hl : (w.event L 0).2 + 1 < (X.tr (w.event L 0).1).length := by
    have hlt := len_of_get (hv.2.2.1 0)
    have hth : (v.event L 0).1 = (w.event L 0).1 := by
      simp only [WarpRequest.event, hbef.1, hbef.2.1]
    have hix := hbef.2.2 0
    rw [hth] at hlt
    simp only [WarpRequest.event] at hlt hix ⊢
    omega
  obtain ⟨cta, x, hx, l, hxl⟩ := hb.performed hget hl
  have hxw : x.own = w := ((hh.1 cta).1 x hx).2.2.ext hw hxl
  refine ⟨x, ?_, hxw⟩
  rw [← hxw, (hh.1 cta).2.1 x hx]
  exact hx

/-- The rendezvous of a complete operation: `i` and `j` are lane events of the same complete
operation and the return of `j` waits for that operation (`MustWait`). In the dependency order these
are the witness edges of the `Performed` and `Covered` needs of `j` (`Witness`,
`DepStep.of_witness`); they order nothing in causality by themselves. -/
def WaitEdge (L : Launch) (X : Execution) (i j : EvId) : Prop :=
  ∃ ws, Completed X ws ∧ (∃ w ∈ ws, Participates L w i) ∧ (∃ w ∈ ws, Participates L w j) ∧
    MustWait X j

/-- Recorded start-to-return dependencies survive execution growth. -/
theorem WaitEdge.mono {L : Launch} {X Y : Execution} {i j : EvId}
    (h : X.le Y) (hw : WaitEdge L X i j) : WaitEdge L Y i j := by
  obtain ⟨ws, hws, hi, hj, hm⟩ := hw
  exact ⟨ws, hws.mono h, hi, hj, hm.mono h⟩

/-- A history in which no allocation record follows a deallocation record has no allocation in
the window of `PendingReleaseAlloc`. -/
theorem not_pendingReleaseAlloc {L : Launch} {X : Execution} {cta : Nat}
    (h : (X.tmemHistory cta).Pairwise fun d a =>
      (∃ base n, d.action = .dealloc base n) → ∀ n base, a.action ≠ .alloc n base) :
    ¬ PendingReleaseAlloc L X cta := by
  rintro ⟨k, l, d, a, hd, ha, hkl, -, hdd, ⟨n, base, han⟩, -⟩
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  exact List.pairwise_iff_getElem.mp h k l hk hl hkl hdd n base han

/-- No replay faults and no allocation record after a deallocation record: no resource
unsafety. -/
theorem not_resourceUnsafe {L : Launch} {X : Execution}
    (hrun : ∀ cta reason, runRequests {} (X.tmemHistory cta) ≠ .fault reason)
    (horder : ∀ cta, (X.tmemHistory cta).Pairwise fun d a =>
      (∃ base n, d.action = .dealloc base n) → ∀ n base, a.action ≠ .alloc n base) :
    ¬ ResourceUnsafe L X := by
  rintro ⟨cta, ⟨reason, hf⟩ | hw⟩
  · exact hrun cta reason hf
  · exact not_pendingReleaseAlloc (horder cta) hw

end
end PTX.Tmem.Pair
