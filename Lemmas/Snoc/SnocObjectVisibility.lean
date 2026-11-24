-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectOrder
public import Lemmas.Snoc.SnocObjectMemory
public import Lemmas.Snoc.SnocVisibility
public import Lemmas.Tcgen05.TcExtend
import Lemmas.Order.GuardObserver

@[expose] public section

/-! Restrict visibility after a new control/object operation to old memory accesses.
The actual read and write effects are retained; no kernel-specific layout is used. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}

theorem old_wait_ne_new_record (hid : rec.id = .thread (g, (X.tr g).length)) {w : EvId}
    (hw : w.2 < (X.tr w.1).length) : rec.id ≠ .thread w := by
  rw [hid]
  intro he
  have heq := Ref.thread.inj he
  subst w
  simp at hw

theorem snocObject_mbarExec_old (ho : ObjectsOk X)
    (hid : rec.id = .thread (g, (X.tr g).length)) {x w : EvId}
    (hw : w.2 < (X.tr w.1).length) :
    MbarExec L (X.snocObject g e r mb rec) x w ↔ MbarExec L X x w :=
  (TcMma.appendObject_mbarExec_iff (old_wait_ne_new_record hid hw)).trans
    (mbarExec_snoc (g := g) (e := e) (r := r) ho hw)

theorem snocObject_observedMma_iff (hc : CommitOk X)
    (hid : rec.id = .thread (g, (X.tr g).length)) {x w : EvId} {acq : Bool} {ws : MbarScope}
    (hw : w.2 < (X.tr w.1).length) :
    AsyncObserved (X.snocObject g e r mb rec) x .mmaDone w acq ws ↔
      AsyncObserved X x .mmaDone w acq ws :=
  (appendObject_asyncObserved_iff (old_wait_ne_new_record hid hw)).trans
    (observesMma_snoc (g := g) (e := e) (r := r) hc hw)

/-- An observation by an old wait after any append was an observation of the same notification
in `X`: the notifications are those of `X`, and a commit with a notification is an old event. -/
theorem snoc_asyncObserved_old (hv : EffectValidity L X)
    {x w : EvId}
    {p : Part} {acq : Bool} {ws : MbarScope} (hw : w.2 < (X.tr w.1).length)
    (h : AsyncObserved (X.snoc g e r) x p w acq ws) : AsyncObserved X x p w acq ws := by
  obtain ⟨n, m, hn, ⟨pcw, q, hget⟩, hu⟩ := h
  have hwo : WaitObserves X n w m acq ws := ⟨⟨pcw, q, by rwa [snoc_get_old hw] at hget⟩, hu⟩
  have notifyOn : ∀ t, NotifyOn (X.snoc g e r) x t m → NotifyOn X x t m := by
    intro t ht
    cases t with
    | copy =>
      obtain ⟨bytes, s, hi, hn', hm, hs⟩ := ht
      exact ⟨bytes, s, issuedBy_some.mpr ((snoc_copy_of_nonempty hv.tma
        ⟨.notify .copy, hn'⟩).mp (issuedBy_some.mp hi)), hn', hm, hs⟩
    | load =>
      obtain ⟨o, addr, ho, hi, hm, hn'⟩ := ht
      obtain ⟨addr', pc, hp⟩ := (hv.tensor _ _ ho).1
      have hi' : X.TensorIssue x addr o.spec := by
        simpa only [Execution.TensorIssue, snoc_get_old (len_of_get hp)] using hi
      exact ⟨o, addr, ho, hi', hm, hn'⟩
    | cta c =>
      obtain ⟨spec, targets, hi, hc, hn', hm⟩ := ht
      obtain ⟨spec', targets', pc, hp⟩ := hv.clc.2.2.1 _ (.inr (.inr ⟨c, hn'⟩))
      have hi' : X.ClcIssue x spec targets := by
        simpa only [Execution.ClcIssue, snoc_get_old (len_of_get hp)] using hi
      exact ⟨spec, targets, hi', hc, hn', hm⟩
  have mma : Notifies (X.snoc g e r) x .mmaDone n m → Notifies X x .mmaDone n m := by
    rintro ⟨c, s, rank, rfl, ht, hc, htg, hn'⟩
    obtain ⟨⟨_,_,⟨prior,hPrior⟩,_⟩,_⟩ := hv.tcCommit c rank hn'
    have hOld := len_of_get hPrior
    obtain ⟨pc,hc⟩ := hc
    exact ⟨c,s,rank,rfl,(tracksMma_snoc_old hOld).mp ht,
      ⟨pc,(snoc_get_old hOld).symm.trans hc⟩,htg,hn'⟩
  have copy : ∀ {p : Part}, (p = .read .copy ∨ p = .write .copy) →
      Notifies (X.snoc g e r) x p n m → Notifies X x p n m := by
    rintro p (rfl | rfl) (⟨hn, ho⟩ | ⟨j, noinc, hn, ⟨h1, h2, ⟨s, hc, hs⟩, m', ni, ha'⟩, ha, harr⟩)
    all_goals first
      | exact .inl ⟨hn, notifyOn .copy ho⟩
      | (obtain ⟨⟨m'', ni', pcj, hj⟩, -⟩ := hv.tma.2.2.2 j harr
         have hjo := len_of_get hj
         have hxo : x.2 < (X.tr x.1).length := by rw [h1]; omega
         refine .inr ⟨j, noinc, hn, ⟨h1, h2, ⟨s, ?_, hs⟩, m', ni, ?_⟩, ?_, harr⟩
         · obtain ⟨pc, hp⟩ := hc; exact ⟨pc, by rwa [snoc_get_old hxo] at hp⟩
         · obtain ⟨pc, hp⟩ := ha'; exact ⟨pc, by rwa [snoc_get_old hjo] at hp⟩
         · obtain ⟨pc, hp⟩ := ha; exact ⟨pc, by rwa [snoc_get_old hjo] at hp⟩)
  refine ⟨n, m, ?_, hwo⟩
  cases p
  case mmaRead | mmaDone => exact mma hn
  case readCopy => exact copy (.inl rfl) hn
  case writeCopy => exact copy (.inr rfl) hn
  all_goals
    simp only [Notifies, Part.target] at hn ⊢
    try exact ⟨hn.1, notifyOn _ hn.2⟩

/-- An observation by an old wait in the extension by an object operation was an observation
of the same notification in `X`. -/
theorem snocObject_asyncObserved_old (hv : EffectValidity L X)
    (_hk : ∀ k, e.kind ≠ .tc k) (hid : rec.id = .thread (g, (X.tr g).length)) {x w : EvId}
    {p : Part} {acq : Bool} {ws : MbarScope} (hw : w.2 < (X.tr w.1).length)
    (h : AsyncObserved (X.snocObject g e r mb rec) x p w acq ws) : AsyncObserved X x p w acq ws :=
  snoc_asyncObserved_old hv hw
    ((appendObject_asyncObserved_iff (old_wait_ne_new_record hid hw)).mp h)

/-- A group wait of an old event after an append with retained async stages covers the stages it
covers in `X`. -/
theorem snoc_groupWait_retained
    (hPresent : ∀ {i p}, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    {x w : EvId} {k : GroupWait} (hw : w.2 < (X.tr w.1).length)
    (hgw : GroupWaitsFor (X.snoc g e r) k x w)
    (hs : ∀ q ∈ GroupWaitStages (X.snoc g e r) x k,
      (X.snoc g e r).AsyncPresent x q) :
    GroupWaitsFor X k x w ∧ ∀ q ∈ GroupWaitStages X x k, X.AsyncPresent x q := by
  have ha := (SnocRecords.same (X := X) (g := g)).threadAppend (e := e) (r := r)
  have hgX : GroupWaitsFor X k x w :=
    ha.groupWaitsFor (fun h => by subst h; simp at hw) hgw
  refine ⟨hgX, fun q hq => ?_⟩
  have hst : GroupWaitStages (X.snoc g e r) x k = GroupWaitStages X x k :=
    snoc_groupWaitStages_old (r := r) (groupWaitsFor_issuer hgX)
  rw [← hst] at hq
  exact hPresent (hs q hq)

/-- A group wait of an old event in the extension by an object operation covers the stages it
covers in `X`. -/
theorem snocObject_groupWait_old (hk : ∀ k, e.kind ≠ .tc k)
    {x w : EvId} {k : GroupWait} (hw : w.2 < (X.tr w.1).length)
    (hgw : GroupWaitsFor (X.snocObject g e r mb rec) k x w)
    (hs : ∀ q ∈ GroupWaitStages (X.snocObject g e r mb rec) x k,
      (X.snocObject g e r mb rec).AsyncPresent x q) :
    GroupWaitsFor X k x w ∧ ∀ q ∈ GroupWaitStages X x k, X.AsyncPresent x q :=
  snoc_groupWait_retained (snoc_asyncPresent_of_not_tc hk).mp hw hgw
    (fun q hq => appendObject_asyncPresent.mp (hs q hq))

theorem snocObject_asyncFinished_old (hv : EffectValidity L X)
    (hk : ∀ k, e.kind ≠ .tc k)
    (hid : rec.id = .thread (g, (X.tr g).length)) {x w : EvId} {p : Part}
    (hw : w.2 < (X.tr w.1).length)
    (h : AsyncFinished L (X.snocObject g e r mb rec) x p w) : AsyncFinished L X x p w := by
  rcases h with ⟨k, hvis, hgw, hs⟩ | ⟨ws, h, hs⟩
  · obtain ⟨h1, h2⟩ := snocObject_groupWait_old hk hw hgw hs
    exact .inl ⟨k, hvis, h1, h2⟩
  · exact .inr ⟨ws, snocObject_asyncObserved_old hv hk hid hw h, hs⟩

theorem snocObject_asyncOnlyFinished_old (hk : ∀ k, e.kind ≠ .tc k) {x w : EvId} {p : Part}
    (hw : w.2 < (X.tr w.1).length)
    (h : AsyncOnlyFinished (X.snocObject g e r mb rec) x p w) : AsyncOnlyFinished X x p w := by
  obtain ⟨hvis, hgw, hs⟩ := h
  obtain ⟨h1, h2⟩ := snocObject_groupWait_old hk hw hgw hs
  exact ⟨hvis, h1, h2⟩

theorem snocObject_proxyBefore_old (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc)
    {x y : EvId} {l : Loc} (hy : y.2 < (X.tr y.1).length)
    (h : ProxyBefore L (X.snocObject g e r mb rec) x y l) : ProxyBefore L X x y l := by
  obtain ⟨f, sp, scope, ⟨pc, hf⟩, hthread, hcov, hreach, hxf, hfy⟩ := h
  have hfy' := snocObject_baseCausality_old hcl hold hfree hid hnb hna hy hfy
  have hfo := (baseCausality_events hfy').1
  exact ⟨f, sp, scope, ⟨pc, (snoc_get_old (r := r) hfo).symm.trans hf⟩, hthread, hcov, hreach,
    snocObject_baseCausality_old hcl hold hfree hid hnb hna hfo hxf, hfy'⟩

theorem snocObject_asyncCovers_old {x : EvId} {p : Part} {l : Loc}
    (hx : x.2 < (X.tr x.1).length)
    (h : AsyncCovers (X.snocObject g e r mb rec) x p l) : AsyncCovers X x p l := by
  obtain ⟨a, w, ha, hc⟩ := h
  exact ⟨a, w, (snoc_intent_at (g := g) (e := e) (r := r) (v := .async x p) hx).mp ha, hc⟩

theorem snocObject_asyncBefore_old (ht : EffectValidity L X)
    (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r) (hk : ∀ k, e.kind ≠ .tc k)
    (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc)
    {a b : EvId × Part} (ha : a.1.2 < (X.tr a.1.1).length)
    (hb : b.1.2 < (X.tr b.1.1).length)
    (h : AsyncBefore L (X.snocObject g e r mb rec) l a b) : AsyncBefore L X l a b := by
  obtain ⟨hc,hc',hh⟩ := h
  refine ⟨snocObject_asyncCovers_old ha hc,snocObject_asyncCovers_old hb hc',?_⟩
  rcases hh with ⟨w,ho,hafter⟩ | ⟨w,ho,hafter⟩
  · have hafter' := snocObject_baseCausality_old hcl hold hfree hid hnb hna hb hafter
    exact .inl ⟨w, snocObject_asyncFinished_old ht hk hid (baseCausality_events hafter').1 ho,
        hafter'⟩
  · have hafter' := (po_snoc_old (g := g) (e := e) (r := r) hb).mp hafter
    have hwo : w.2 < (X.tr w.1).length := by rw [hafter'.1]; have := hafter'.2.1; omega
    exact .inr ⟨w, snocObject_asyncOnlyFinished_old hk hwo ho, hafter'⟩

/-- Completion order between older event instances reflects across an object append
whenever its causal and proxy paths reflect. -/
theorem snocObject_completionBefore_old {x w y : EvId} {p : Part} {l : Loc}
    (hx : x.2 < (X.tr x.1).length) (hy : y.2 < (X.tr y.1).length)
    (hb : baseCausality L (X.snocObject g e r mb rec) w y → baseCausality L X w y)
    (hp : ProxyBefore L (X.snocObject g e r mb rec) w y l → ProxyBefore L X w y l)
    (h : ObservedCompletionBefore L (X.snocObject g e r mb rec) l x p w y) :
    ObservedCompletionBefore L X l x p w y ∧ w.2 < (X.tr w.1).length := by
  have h' := observedCompletionBefore_map (fun hcopy => by
    obtain ⟨pc, he⟩ := hcopy
    change (X.snoc g e r).get x = _ at he
    exact ⟨pc, by rwa [snoc_get_old hx] at he⟩) (fun hmma => by
    obtain ⟨pc, he⟩ := hmma
    change (X.snoc g e r).get x = _ at he
    exact ⟨pc, by rwa [snoc_get_old hx] at he⟩) (fun hwrite => by
    obtain ⟨pc, he⟩ := hwrite
    change (X.snoc g e r).get y = _ at he
    exact ⟨pc, by rwa [snoc_get_old hy] at he⟩) hb hp h
  exact ⟨h', (baseCausality_events (observedCompletionBefore_baseCausality h')).1⟩

theorem snocObject_modelCausality_old (ht : EffectValidity L X)
    (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r) (hk : ∀ k, e.kind ≠ .tc k)
    (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc)
    {x y : Ref} {l : Loc} (hx : x.issuer.2 < (X.tr x.issuer.1).length)
    (hy : y.issuer.2 < (X.tr y.issuer.1).length)
    (h : modelCausality L (X.snocObject g e r mb rec) l x y) : modelCausality L X l x y := by
  cases x with
  | thread x =>
    cases y with
    | thread y =>
      rcases h with hb | ha
      · exact .inl (snocObject_baseCausality_old hcl hold hfree hid hnb hna hy hb)
      · exact .inr (ha.of_prefix (Execution.le_trans le_snoc (Execution.le_appendObject ..)) hx hy)
    | async y q =>
      refine ⟨snocObject_asyncCovers_old hy h.1, ?_⟩
      rcases h.2 with hp | ⟨⟨s, ⟨pc, hc⟩, hgen⟩, hb⟩
      · exact .inl (snocObject_proxyBefore_old hcl hold hfree hid hnb hna hy hp)
      · exact .inr ⟨⟨s, ⟨pc, (snoc_get_old (r := r) hy).symm.trans hc⟩, hgen⟩,
          snocObject_baseCausality_old hcl hold hfree hid hnb hna hy hb⟩
  | async x p =>
    cases y with
    | thread y =>
      obtain ⟨hc, w, ho, hb⟩ := h
      obtain ⟨hb', hwo⟩ := snocObject_completionBefore_old hx hy
        (snocObject_baseCausality_old hcl hold hfree hid hnb hna hy)
        (snocObject_proxyBefore_old hcl hold hfree hid hnb hna hy) hb
      exact ⟨snocObject_asyncCovers_old hx hc, w,
        snocObject_asyncFinished_old ht hk hid hwo ho, hb'⟩
    | async y q =>
      have transport {a b : EvId × Part}
          (h : AsyncChain L (X.snocObject g e r mb rec) l a b) :
          a.1.2 < (X.tr a.1.1).length → b.1.2 < (X.tr b.1.1).length →
          AsyncChain L X l a b := by
        induction h with
        | direct hd =>
          intro ha hb
          exact .direct (snocObject_asyncBefore_old ht hcl hold hk hfree hid hnb hna ha hb hd)
        | tail _ hp hd ih =>
          intro ha hb
          have hp0 := appendObject_asyncPresent.mp hp
          have hp' := (snoc_asyncPresent_of_not_tc (X:=X) (g := g) (e := e) (r := r) hk).mp hp0
          obtain ⟨event,he⟩ := asyncPresent_issuer ht hp'
          have hm := len_of_get he
          exact .tail (ih ha hm) hp'
            (snocObject_asyncBefore_old ht hcl hold hk hfree hid hnb hna hm hb hd)
      have hpt : ∀ {k : EvId}, PairTc (X.snocObject g e r mb rec) k → PairTc X k := by
        have hold : ∀ {k : EvId} {pc : Nat} {t : TcKind},
            (X.snocObject g e r mb rec).get k = some ⟨pc, .tc t⟩ →
              X.get k = some ⟨pc, .tc t⟩ := by
          intro k pc t hm
          change (X.snoc g e r).get k = _ at hm
          rw [snoc_get] at hm
          split_ifs at hm
          · exact absurd (congrArg Event.kind (Option.some.inj hm)) (hk _)
          · exact hm
        rintro k (⟨d, s, acc, mask, ⟨pc, hm⟩, hs⟩ | ⟨c, ⟨pc, hc⟩, hn⟩)
        · exact .inl ⟨d, s, acc, mask, ⟨pc, hold hm⟩, hs⟩
        · exact .inr ⟨c, ⟨pc, hold hc⟩, hn⟩
      exact ⟨h.1.imp_right fun hp => ⟨hp.1, hp.2.imp hpt hpt⟩, transport h.2 hx hy⟩

end
end PTX
