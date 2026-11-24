-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.P.HandoffDef
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.NthEv
public import Lemmas.Order.OrderNotAccess
public import Lemmas.Order.OrderWaits
public import Lemmas.Tcgen05.TcProgramOrder
public import Lemmas.Tcgen05.TmemWriters

@[expose] public section

/-! # The orders through the P-full objects (`overwrite_gate`, `store_done`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

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
theorem isMma_get {i : EvId} (h : IsMma X i) :
    ∃ pc d s acc mask, X.get i = some ⟨pc, .tc (.mma d s acc mask)⟩ := by
  obtain ⟨d, s, acc, mask, pc, hp⟩ := h
  exact ⟨pc, d, s, acc, mask, hp⟩

theorem isMma_lt {i : EvId} (h : IsMma X i) : i.2 < (X.tr i.1).length := by
  obtain ⟨_, _, _, _, _, hp⟩ := isMma_get h
  exact len_of_get hp

/-- Program order from an MMA is causality. -/
theorem isMma_baseCausality {i f : EvId} (h : IsMma X i) (hs : i.1 = f.1) (hlt : i.2 < f.2)
    (hf : f.2 < (X.tr f.1).length) : baseCausality L X i f := by
  obtain ⟨_, _, _, _, _, hp⟩ := isMma_get h
  exact baseCausality_tc hp hs hlt hf

end

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## Order lemmas -/

theorem tLd_lt {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (h : X.TLd e a vals sh) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨pc, hp⟩ := h
  exact len_of_get hp

theorem tSt_lt {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
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
theorem doneBefore_of_po {x e e' : EvId} (h : DoneBefore L X x e) (hp : po X e e') :
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
  have hyl : y.2 < (X.tr y.1).length := isMma_lt ⟨_, _, _, _, hy⟩
  refine .inr ⟨⟨⟨hg, hthr ▸ hg, by rw [hthr]⟩, by rw [hthr]⟩,
    .inl (isMma_baseCausality ⟨_, _, _, _, hx⟩ hthr hlt
        hyl), d, s, acc, mask, d', s', acc', mask', hx, hy,
    hacc⟩

/-- An MMA writing a cell of stage `st`'s scores writes only cells of them, in its pair. -/
theorem mma_s (ht : ScoreFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} {st : Nat} (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hs : InS st cell) (hst : st < 2) :
    ∀ c, X.MmaCell i c → InS st c ∧ c.cta = i.1 / L.block := by
  obtain ⟨-, -, st', -, h | h⟩ := ht.mma_cells hi
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
    ∀ c, X.MmaCell i c → InO st c ∧ c.cta = i.1 / L.block := by
  obtain ⟨-, -, st', hst', h | h⟩ := ht.mma_cells hi
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
theorem mma_in (ht : ScoreFacts L X) {i : EvId} (hi : IsMma X i) : mmaIn L (i.1 / L.block) i.1 := by
  obtain ⟨d, s, acc, mask, hm⟩ := hi
  obtain ⟨hg, hw, -⟩ := ht.mma_cells hm
  exact ⟨hg, rfl, hw⟩

/-- Two softmax threads of one stage loading or storing one cell are one thread. -/
theorem soft_cell_thread (hpre : Pre P L mem0) {h h' a a' j j' : Nat}
    (hst : Prologue.warpIndex L h / 4 = Prologue.warpIndex L h' / 4)
    (hc : tcDataCell32 L h a j = tcDataCell32 L h' a' j') : h = h' := by
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq] at hc
  obtain ⟨h1, h2, -⟩ := hc
  unfold Prologue.warpIndex at *
  rw [hpre.block] at *
  omega

/-- Two correction threads loading or storing one cell are one thread. -/
theorem corr_cell_thread (hpre : Pre P L mem0) {h h' a a' j j' : Nat} (hw : 8 ≤ Prologue.warpIndex
    L h)
    (hw1 : Prologue.warpIndex L h < 12) (hw' : 8 ≤ Prologue.warpIndex L h') (hw1' :
        Prologue.warpIndex L h' < 12)
    (hc : tcDataCell32 L h a j = tcDataCell32 L h' a' j') : h = h' := by
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq] at hc
  obtain ⟨h1, h2, -⟩ := hc
  unfold Prologue.warpIndex at *
  rw [hpre.block] at *
  omega

/-- The CTA of a load's or store's cell. -/
theorem cell_cta (L : Launch) (h a j : Nat) : (tcDataCell32 L h a j).cta = h / L.block := rfl

/-! ## OverwriteGate -/

/-- **OverwriteGate.** An event of a producer of stage `st`'s P-full object with at most `u`
arrivals before it happens before every MMA of its CTA after the MMA lane's poll of phase `u`. -/
theorem overwrite_gate (ht : ScoreFacts L X) (hP : PReadyHandoff L X) {g e u st : Nat}
    {f : EvId} (hst : st < 2) (hg : pProd L (g / L.block) st g)
    (he : pArr L X g st e ≤ u) (hf : IsMma X f) (hc : f.1 / L.block = g / L.block)
    (hu : u + 1 ≤ pPolls L X f.1 st f.2) : baseCausality L X (g, e) f := by
  have hin := mma_in ht hf
  rw [hc] at hin
  simp only [pPolls, hc] at hu
  exact (hP _ st hst).baseCausality_of_counts (h := f.1) (f := f.2) hin hg he
      (by simpa using hu) (isMma_lt hf)

/-- A thread with an event after `i` has an event at `i + 1`. -/
theorem NonTcAfter.succ_lt {h i e : Nat}
    (hn : NonTcAfter X h i e) : i + 1 < (X.tr h).length := by
  obtain ⟨hie, ev, he, -⟩ := hn
  have := (List.getElem?_eq_some_iff.mp (show (X.tr h)[e]? = some ev from he)).1
  omega

/-- **The observed arrival is after the producer's `tcgen05` events**: an MMA of the CTA after
the MMA lane's poll of phase `u` of stage `st`'s P-full object comes after a producer's arrival on
the object with `u` earlier ones, which is a later event of the producer than each of its `tcgen05`
events with at most `u` arrivals before it. -/
theorem gate_after (ht : ScoreFacts L X) (hP : PReadyHandoff L X) {g k u st pck : Nat}
    {tk : TcKind} {f : EvId} (hst : st < 2) (hg : pProd L (g / L.block) st g)
    (hk : X.get (g, k) = some ⟨pck, .tc tk⟩) (hku : pArr L X g st k ≤ u) (hf : IsMma X f)
    (hc : f.1 / L.block = g / L.block) (hu : u + 1 ≤ pPolls L X f.1 st f.2) :
    ∃ e, NonTcAfter X g k e ∧ pArr L X g st e = u ∧
      ∃ ev, X.get (g, e) = some ev ∧ arrivesOn (pFull L (g / L.block) st) ev = true := by
  have hin := mma_in ht hf
  rw [hc] at hin
  simp only [pPolls, hc] at hu
  obtain ⟨j, pc, p, acq, sc, -, hw, hq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (h := f.1) (f := f.2) (c := u) hu
  obtain ⟨e, he, hs⟩ := hP _ st hst f.1 j pc p acq sc u hin hw (by simpa using hq) g hg
  obtain ⟨ev, hev, ha⟩ := hs.arrives
  have hke := MbarRing.arrival_index_ge hev ha he hku
  refine ⟨e, ⟨?_, ev, hev, fun tk' htk => ?_, fun f hf => ?_⟩, he, ev, hev, ha⟩
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
theorem soft_prod {h : Nat} (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8) :
    pProd L (h / L.block) (Prologue.warpIndex L h / 4) h :=
  ⟨hh, rfl, .inl ⟨hw, rfl⟩⟩

/-- **PPublished.** A softmax store of tile `u` is done before every MMA of its pair after the
MMA thread's poll of phase `u` of the P-ready object (columns below `112`) or of the second object
(columns `112 …`). -/
theorem store_done (ht : ScoreFacts L X) (hP : PReadyHandoff L X) (h2 : P2Gate L X)
    {h i a : Nat} {vals : List Value} {f : EvId} (hh : h < L.threads) (hw : Prologue.warpIndex L h
        < 8)
    (hs : X.TSt (h, i) a vals .s32x32b) (hf : IsMma X f) (hc : f.1 / L.block = h / L.block)
    (hlow : sPolls L X h (Prologue.warpIndex L h / 4) i ≤ pPolls L X f.1 (Prologue.warpIndex L h /
        4) f.2)
    (hhigh : (∀ j < vals.length, InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) →
      sPolls L X h (Prologue.warpIndex L h / 4) i ≤ p2Polls L X f.1 (Prologue.warpIndex L h / 4)
          f.2) :
    StoreDoneBefore L X (h, i) f := by
  obtain ⟨-, -, h1, hpub, hwait⟩ := ht.soft_st hh hw hs
  rcases hpub with hhi | harr
  · obtain ⟨w, pc, hiw, hwget, hhb⟩ := h2 hh hw hs hhi hf hc (hhigh hhi)
    exact ⟨⟨a, vals, _, hs⟩, .inl ⟨(h, w), ⟨pc, hwget⟩, rfl, hiw, .inl hhb⟩⟩
  · have hst : Prologue.warpIndex L h / 4 < 2 := by omega
    obtain ⟨pcs, hsget⟩ := id hs
    obtain ⟨e, hne, he, -⟩ := gate_after ht hP hst (soft_prod hh hw) hsget
      (u := sPolls L X h (Prologue.warpIndex L h / 4) i - 1) (by omega) hf hc (by omega)
    obtain ⟨w, pc, hiw, hwe, hwget, -⟩ := hwait e hne
    have hwu : pArr L X h (Prologue.warpIndex L h / 4) w ≤ sPolls L X h (Prologue.warpIndex L h /
        4) i - 1 := by
      rw [← he]
      exact countP_take_mono _ _ hwe.le
    exact ⟨⟨a, vals, _, hs⟩, .inl ⟨(h, w), ⟨pc, hwget⟩, rfl, hiw, .inl
      (overwrite_gate ht hP hst (soft_prod hh hw) hwu hf hc (by omega))⟩⟩


end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
