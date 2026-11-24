-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Lemmas.Protocol.UnitHandoff
public import Lemmas.Tcgen05.TmemWriters
public import Lemmas.Order.OrderWaits
public import Lemmas.Flow.NthEv
public import Lemmas.Order.OrderNotAccess

@[expose] public section

/-! # The P-ready objects

Stage `st`'s P-ready object of a pair (`pReadyBar`, offset `144 + 8 st` of the leader CTA, count
512) is arrived on by the stage's 128 softmax threads and the 128 correction threads of each CTA
of the pair (`pProd`) and polled by the leader's MMA warp (`mmaIn`), whose first poll needs an
arrival. **PPhase**: its phase `u` holds each producer's arrival with `u` earlier ones (a softmax
thread's arrival of score tile `u`, a correction thread's credit `u`), and the MMA warp's poll with
`u` earlier successful polls observes it: the unit handoff with offset 0 (`PReadyHandoff`). Its
derivation from the object's history (`MbarRing.Multi.phase_of_counts`: every phase needs one unit
of every producer, a unit of use `u` is enabled by the polls before `u`) is the ring layer's, and
the protocol takes it as its premise (derived in `PReadyObj`, `pReadyHandoff`, from the object's
unit-object facts and the reuse paths `PReadyReach`).

The columns `112 …` of `P` are published through the second object (`pReady2Bar`, count 8): the
warp's elected lane arrives after `bar.warp.sync`, which follows every lane's `wait::st`. That a
lane's store of tile `u` to those columns is followed by a `wait::st` that happens before every
MMA of the pair after the poll of phase `u` of the second object (`P2Gate`) needs the warp
rendezvous and that object's ring; it is a premise (derived in `PReady2Gate`, `p2Gate`, from its
warp part and its object part).

Exports:
* **OverwriteGate** (`overwrite_gate`): every event of a producer up to its arrival of phase `u`
  happens before every MMA of the pair issued after the poll of phase `u`: every QK MMA of a later
  score tile (`ScoreFacts.qk_polls`) and every PV MMA of tile `u` or later. That arrival is in the
  producer's trace, after each of its `tcgen05` events with at most `u` arrivals before it
  (`gate_after`): a trace that stops earlier has no such MMA.
* **PPublished** (`store_done`): a softmax store of tile `u` is done (`StoreDoneBefore`, through its
  `wait::st`) before every MMA of the pair after the polls of phase `u` of the object its columns
  are published through.

The order lemmas used by the score and accumulator protocols are here too: program order between
non-memory events (`baseCausality_src`), the order of events by their counts (`lt_of_count_lt`), the
synchronizing count after a non-arrival (`count_succ_not`), and the thread of a cell
(`soft_cell_thread`, `corr_cell_thread`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

section
variable {L : Launch} {X : Execution}

/-- Program order from a non-memory event is causality. -/
theorem baseCausality_src {e f : EvId} {ev : Event} (he : X.get e = some ev) (hacc : ev.acc = none)
    (hs : e.1 = f.1) (hlt : e.2 < f.2) (hf : f.2 < (X.tr f.1).length) : baseCausality L X e f :=
  .single (.inl (po_of_source_not_access hs hlt hf (by rw [he]; exact hacc)))

/-- Program order from a tcgen05 event is causality. -/
theorem baseCausality_tc {e f : EvId} {pc : Nat} {k : TcKind} (he : X.get e = some ⟨pc, .tc k⟩)
    (hs : e.1 = f.1) (hlt : e.2 < f.2) (hf : f.2 < (X.tr f.1).length) : baseCausality L X e f :=
  baseCausality_src he rfl hs hlt hf

/-- An MMA's event. -/
theorem IsMma.get {i : EvId} (h : IsMma X i) :
    ∃ pc d s acc mask, X.get i = some ⟨pc, .tc (.mma d s acc mask)⟩ := by
  obtain ⟨d, s, acc, mask, pc, hp⟩ := h
  exact ⟨pc, d, s, acc, mask, hp⟩

theorem IsMma.lt {i : EvId} (h : IsMma X i) : i.2 < (X.tr i.1).length := by
  obtain ⟨_, _, _, _, _, hp⟩ := h.get
  exact len_of_get hp

/-- Program order from an MMA is causality. -/
theorem IsMma.baseCausality {i f : EvId} (h : IsMma X i) (hs : i.1 = f.1) (hlt : i.2 < f.2)
    (hf : f.2 < (X.tr f.1).length) : baseCausality L X i f := by
  obtain ⟨_, _, _, _, _, hp⟩ := h.get
  exact baseCausality_tc hp hs hlt hf

end

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The MMA warp of leader CTA `c`. -/
def mmaIn (L : Launch) (c g : Nat) : Prop := g < L.threads ∧ ctaOf L g = c ∧ warpOf L g = 12

/-- A producer of stage `st`'s P-ready object of the pair led by `c`: a softmax thread of the stage
or a correction thread, of either CTA of the pair. -/
def pProd (L : Launch) (c st g : Nat) : Prop :=
  g < L.threads ∧ leadCta (ctaOf L g) = c ∧
    ((warpOf L g < 8 ∧ warpOf L g / 4 = st) ∨ (8 ≤ warpOf L g ∧ warpOf L g < 12))

/-- **PPhase**, the P-ready handoff of every stage of every pair. -/
def PReadyHandoff (L : Launch) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 →
    MbarRing.UnitHandoff L X (pReadyBar L c st) (pProd L c st) (mmaIn L c) 0

/-- **The second P-ready gate**: a softmax lane's store of tile `u` to columns `112 …` is followed
by a `wait::st` of the tile that happens before every MMA of its pair after the poll of phase `u`
of the second object. -/
def P2Gate (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a : Nat} {vals : List Value} {f : EvId}, h < L.threads → warpOf L h < 8 →
    X.TSt (h, i) a vals .s32x32b →
    (∀ j < vals.length, InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) → IsMma X f →
    ctaOf L f.1 = leadCta (ctaOf L h) →
    sPolls L X h (warpOf L h / 4) i ≤ p2Polls L X f.1 (warpOf L h / 4) f.2 →
      ∃ w pc, i < w ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧ baseCausality L X (h, w) f

/-! ## Order lemmas -/

theorem TLd.lt {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (h : X.TLd e a vals sh) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨pc, hp⟩ := h
  exact len_of_get hp

theorem TSt.lt {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (h : X.TSt e a vals sh) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨pc, hp⟩ := h
  exact len_of_get hp

/-- A smaller prefix count comes first. -/
theorem lt_of_count_lt {p : Event → Bool} {g i j : Nat}
    (h : ((X.tr g).take i).countP p < ((X.tr g).take j).countP p) : i < j := by
  by_contra hle
  have := countP_take_mono p (X.tr g) (Nat.le_of_not_lt hle)
  omega

/-- The count of events of a kind does not change over an event of another kind. -/
theorem count_succ_not {p : Event → Bool} {g i : Nat} {ev : Event} (he : X.get (g, i) = some ev)
    (hp : p ev = false) : ((X.tr g).take (i + 1)).countP p = ((X.tr g).take i).countP p := by
  have he' : (X.tr g)[i]? = some ev := he
  rw [List.take_add_one, he', Option.toList_some, List.countP_append]
  simp [hp]

/-- A tcgen05 event is no arrival. -/
theorem pArr_succ_tc {g st i pc : Nat} {k : TcKind} (he : X.get (g, i) = some ⟨pc, .tc k⟩) :
    pArr L X g st (i + 1) = pArr L X g st i :=
  count_succ_not he (by simp [arrivesOn, sourceArrive])

/-- **An MMA's completion observed before `e` is observed before what follows `e`.** -/
theorem DoneBefore.of_po {x e e' : EvId} (h : DoneBefore L X x e) (hp : po X e e') :
    DoneBefore L X x e' := by
  rcases h with ⟨w, ws, ho, hs, hw⟩ | ⟨w, hc, f, hwf, hf, hfe⟩
  · exact .inl ⟨w, ws, ho, hs, hw.trans (.single (.inl hp))⟩
  · exact .inr ⟨w, hc, f, hwf, hf, po_trans hfe hp⟩

/-- Two MMAs of one thread with the same accumulator, in program order, are pipelined. -/
theorem mma_writeBefore (ht : ScoreFacts L X) {x y : EvId} {d d' : Nat} {s s' : OperandSpec}
    {acc acc' : Bool} {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask)
    (hy : X.MmaIssue y d' s' acc' mask') (hthr : x.1 = y.1) (hlt : x.2 < y.2)
    (hacc : SameAccumulator d s d' s') : Before L X x y := by
  obtain ⟨hg, -⟩ := ht.mma_cells hx
  have hyl : y.2 < (X.tr y.1).length := IsMma.lt ⟨_, _, _, _, hy⟩
  refine .inr ⟨⟨⟨hg, hthr ▸ hg, by rw [hthr]⟩, by rw [hthr]⟩,
    .inl (IsMma.baseCausality ⟨_, _, _, _, hx⟩ hthr hlt
        hyl), d, s, acc, mask, d', s', acc', mask', hx, hy,
    hacc⟩

/-- An MMA writing a cell of stage `st`'s scores writes only cells of them, in its pair. -/
theorem mma_s (ht : ScoreFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} {st : Nat} (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hs : InS st cell) (hst : st < 2) :
    ∀ c, X.MmaCell i c → InS st c ∧ leadCta c.cta = ctaOf L i.1 := by
  obtain ⟨-, -, -, st', -, h | h⟩ := ht.mma_cells hi
  · have h1 := (h cell hc).1
    unfold InS at hs h1
    have : st' = st := by omega
    subst this
    exact h
  · have h1 := (h cell hc).1
    unfold InS at hs
    unfold InO at h1
    omega

/-- An MMA writing a cell of stage `st`'s accumulator writes only cells of it, in its pair. -/
theorem mma_o (ht : ScoreFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} {st : Nat} (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hs : InO st cell) :
    ∀ c, X.MmaCell i c → InO st c ∧ leadCta c.cta = ctaOf L i.1 := by
  obtain ⟨-, -, -, st', hst', h | h⟩ := ht.mma_cells hi
  · have h1 := (h cell hc).1
    unfold InO at hs
    unfold InS at h1
    omega
  · have h1 := (h cell hc).1
    unfold InO at hs h1
    have : st' = st := by omega
    subst this
    exact h

/-- The MMA warp of the issuer's CTA. -/
theorem mma_in (ht : ScoreFacts L X) {i : EvId} (hi : IsMma X i) :
    mmaIn L (ctaOf L i.1) i.1 ∧ leadCta (ctaOf L i.1) = ctaOf L i.1 := by
  obtain ⟨d, s, acc, mask, hm⟩ := hi
  obtain ⟨hg, hw, hl, -⟩ := ht.mma_cells hm
  exact ⟨⟨hg, rfl, hw⟩, hl⟩

/-- Two softmax threads of one stage loading or storing one cell are one thread. -/
theorem soft_cell_thread (hpre : Pre P L mem0) {h h' a a' j j' : Nat}
    (hst : warpOf L h / 4 = warpOf L h' / 4)
    (hc : tcDataCell32 L h a j = tcDataCell32 L h' a' j') : h = h' := by
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq] at hc
  obtain ⟨h1, h2, -⟩ := hc
  unfold warpOf at *
  rw [hpre.block] at *
  omega

/-- Two correction threads loading or storing one cell are one thread. -/
theorem corr_cell_thread (hpre : Pre P L mem0) {h h' a a' j j' : Nat} (hw : 8 ≤ warpOf L h)
    (hw1 : warpOf L h < 12) (hw' : 8 ≤ warpOf L h') (hw1' : warpOf L h' < 12)
    (hc : tcDataCell32 L h a j = tcDataCell32 L h' a' j') : h = h' := by
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq] at hc
  obtain ⟨h1, h2, -⟩ := hc
  unfold warpOf at *
  rw [hpre.block] at *
  omega

/-- A leader CTA is its own leader. -/
theorem leadCta_idem (c : Nat) : leadCta (leadCta c) = leadCta c := by
  unfold leadCta
  omega

/-- The CTA of a load's or store's cell. -/
theorem cell_cta (L : Launch) (h a j : Nat) : (tcDataCell32 L h a j).cta = ctaOf L h := rfl

/-! ## OverwriteGate -/

/-- **OverwriteGate.** An event of a producer of stage `st`'s P-ready object with at most `u`
arrivals before it happens before every MMA of its pair after the MMA thread's poll of phase
`u`. -/
theorem overwrite_gate (ht : ScoreFacts L X) (hP : PReadyHandoff L X) {g e u st : Nat}
    {f : EvId} (hst : st < 2) (hg : pProd L (leadCta (ctaOf L g)) st g)
    (he : pArr L X g st e ≤ u) (hf : IsMma X f) (hc : ctaOf L f.1 = leadCta (ctaOf L g))
    (hu : u + 1 ≤ pPolls L X f.1 st f.2) : baseCausality L X (g, e) f := by
  obtain ⟨hin, hl⟩ := mma_in ht hf
  have hlc : leadCta (leadCta (ctaOf L g)) = leadCta (ctaOf L g) := by rw [← hc, hl]
  rw [hc] at hin
  simp only [pPolls, hc] at hu
  exact (hP _ st hlc hst).baseCausality_of_counts (h := f.1) (f := f.2) hin hg he
      (by simpa using hu) hf.lt

/-- A thread with an event after `i` has an event at `i + 1`. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.NonTcAfter.succ_lt {h i e : Nat}
    (hn : NonTcAfter X h i e) : i + 1 < (X.tr h).length := by
  obtain ⟨hie, ev, he, -⟩ := hn
  have := (List.getElem?_eq_some_iff.mp (show (X.tr h)[e]? = some ev from he)).1
  omega

/-- **The observed arrival is after the producer's `tcgen05` events**: an MMA of the pair after
the MMA thread's poll of phase `u` of stage `st`'s P-ready object comes after a producer's arrival
on the object with `u` earlier ones, which is a later event of the producer than each of its
`tcgen05` events with at most `u` arrivals before it. -/
theorem gate_after (ht : ScoreFacts L X) (hP : PReadyHandoff L X) {g k u st pck : Nat}
    {tk : TcKind} {f : EvId} (hst : st < 2) (hg : pProd L (leadCta (ctaOf L g)) st g)
    (hk : X.get (g, k) = some ⟨pck, .tc tk⟩) (hku : pArr L X g st k ≤ u) (hf : IsMma X f)
    (hc : ctaOf L f.1 = leadCta (ctaOf L g)) (hu : u + 1 ≤ pPolls L X f.1 st f.2) :
    ∃ e, NonTcAfter X g k e ∧ pArr L X g st e = u := by
  obtain ⟨hin, hl⟩ := mma_in ht hf
  have hlc : leadCta (leadCta (ctaOf L g)) = leadCta (ctaOf L g) := by rw [← hc, hl]
  rw [hc] at hin
  simp only [pPolls, hc] at hu
  obtain ⟨j, pc, p, acq, sc, -, hw, hq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (h := f.1) (f := f.2) (c := u) hu
  obtain ⟨e, he, hs⟩ := hP _ st hlc hst f.1 j pc p acq sc u hin hw (by simpa using hq) g hg
  obtain ⟨ev, hev, ha⟩ := hs.arrives
  have hke := MbarRing.arrival_index_ge hev ha he hku
  refine ⟨e, ⟨?_, ev, hev, fun tk' htk => ?_, fun f hf => ?_⟩, he⟩
  · rcases Nat.lt_or_eq_of_le hke with h | rfl
    · exact h
    · rw [hk] at hev
      cases hev
      simp [arrivesOn, sourceArrive] at ha
  · obtain ⟨pce, kind⟩ := ev
    simp only at htk
    subst htk
    simp [arrivesOn, sourceArrive] at ha
  · obtain ⟨pce, kind⟩ := ev
    simp only at hf
    subst hf
    simp [arrivesOn, sourceArrive] at ha

/-! ## PPublished -/

/-- A softmax thread of stage `warpOf / 4` is a producer of the stage's P-ready object. -/
theorem soft_prod {h : Nat} (hh : h < L.threads) (hw : warpOf L h < 8) :
    pProd L (leadCta (ctaOf L h)) (warpOf L h / 4) h :=
  ⟨hh, rfl, .inl ⟨hw, rfl⟩⟩

/-- **PPublished.** A softmax store of tile `u` is done before every MMA of its pair after the
MMA thread's poll of phase `u` of the P-ready object (columns below `112`) or of the second object
(columns `112 …`). -/
theorem store_done (ht : ScoreFacts L X) (hP : PReadyHandoff L X) (h2 : P2Gate L X)
    {h i a : Nat} {vals : List Value} {f : EvId} (hh : h < L.threads) (hw : warpOf L h < 8)
    (hs : X.TSt (h, i) a vals .s32x32b) (hf : IsMma X f) (hc : ctaOf L f.1 = leadCta (ctaOf L h))
    (hlow : sPolls L X h (warpOf L h / 4) i ≤ pPolls L X f.1 (warpOf L h / 4) f.2)
    (hhigh : (∀ j < vals.length, InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) →
      sPolls L X h (warpOf L h / 4) i ≤ p2Polls L X f.1 (warpOf L h / 4) f.2) :
    StoreDoneBefore L X (h, i) f := by
  obtain ⟨-, -, h1, -, hpub, hwait⟩ := ht.soft_st hh hw hs
  rcases hpub with hhi | harr
  · obtain ⟨w, pc, hiw, hwget, hhb⟩ := h2 hh hw hs hhi hf hc (hhigh hhi)
    exact ⟨⟨a, vals, _, hs⟩, .inl ⟨(h, w), ⟨pc, hwget⟩, rfl, hiw, .inl hhb⟩⟩
  · have hst : warpOf L h / 4 < 2 := by omega
    obtain ⟨pcs, hsget⟩ := id hs
    obtain ⟨e, hne, he⟩ := gate_after ht hP hst (soft_prod hh hw) hsget
      (u := sPolls L X h (warpOf L h / 4) i - 1) (by omega) hf hc (by omega)
    obtain ⟨w, pc, hiw, hwe, hwget, -⟩ := hwait e hne
    have hwu : pArr L X h (warpOf L h / 4) w ≤ sPolls L X h (warpOf L h / 4) i - 1 := by
      rw [← he]
      exact countP_take_mono _ _ hwe.le
    exact ⟨⟨a, vals, _, hs⟩, .inl ⟨(h, w), ⟨pc, hwget⟩, rfl, hiw, .inl
      (overwrite_gate ht hP hst (soft_prod hh hw) hwu hf hc (by omega))⟩⟩

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
