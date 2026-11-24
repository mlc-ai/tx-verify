-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame

public import Lemmas.Snoc.SnocObjectOrder
public import Lemmas.Snoc.SnocObjectVisibility
public import Lemmas.Snoc.SnocObjectPreserve
public import Lemmas.Snoc.SnocWaitFrame
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! Preservation of an older execution under an appended object-recording acquire wait, at any
mbarrier scope. The appended event is `e` with `e.kind = .wait waitM waitP waitOk true waitScope`.
It adds an object record to one mbarrier and observes its own history, but creates no edge into an
older event. The lemmas say that happens-before, visibility, reads, the waiting graph and
future-read freedom of the older execution are unchanged. Lemmas that take no kind restriction are
reused from `PTX`. -/
namespace PTX.Step
open PTX AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}
  {waitM : Loc} {waitP : Nat} {waitOk : Bool} {waitScope : MbarScope}

/-- An appended object record cannot affect an edge into an older thread event:
its observing wait is also old, hence it is not the appended record. -/
theorem snocObject_step_old (hcl : ClusterHistoryOk L X)
    (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : po (X.snocObject g e r mb rec) a b ∨ CtaBarSync L (X.snocObject g e r mb rec) a b ∨
      MSync L (X.snocObject g e r mb rec) a b ∨ ClusterSync L (X.snocObject g e r mb rec) a b ∨
      WarpBarSync L (X.snocObject g e r mb rec) a b ∨ synchronizesWith L
          (X.snocObject g e r mb rec) a b ∨ FenceSync L (X.snocObject g e r mb rec) a b) :
    po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b := by
  have waitOld {w : EvId} (hw : w.1 = b.1) (hi : w.2 < b.2) : rec.id ≠ .thread w := by
    rw [hid]
    intro he
    have heq := Ref.thread.inj he
    subst w
    simp only at hw hi
    rw [← hw] at hbo
    omega
  have hs : po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨
      MSync L (X.snoc g e r) a b ∨ ClusterSync L (X.snoc g e r) a b ∨
      WarpBarSync L (X.snoc g e r) a b ∨ synchronizesWith L (X.snoc g e r) a b ∨
      FenceSync L (X.snoc g e r) a b := by
    rcases h with hp | hbar | hm | hc | hw | hmem | hfs
    · exact .inl hp
    · exact .inr (.inl hbar)
    · obtain ⟨x, w, m, rs, ws, hr, ⟨ha, hu⟩, hsc, hwt, hwi, hlen, hxt, hxi⟩ := hm
      exact .inr (.inr (.inl
        ⟨x, w, m, rs, ws, hr, ⟨ha, (appendObject_update_iff (waitOld hwt hwi)).mp hu⟩, hsc, hwt,
          hwi, hlen, hxt, hxi⟩))
    · exact .inr (.inr (.inr (.inl hc)))
    · exact .inr (.inr (.inr (.inr (.inl hw))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl hmem)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr hfs)))))
  exact snoc_step_old_full (fun mask inst he => by rw [hshape] at he; cases he)
    hcl (.of_noWrite (fun a bs he => by rw [hshape] at he; cases he)
      (fun a old new he => by rw [hshape] at he; cases he)) hnb hna
    (fun s he => by rw [hshape] at he; cases he) hbo hs

theorem snocObject_baseCausality_old (hcl : ClusterHistoryOk L X)
    (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : baseCausality L (X.snocObject g e r mb rec) a b) : baseCausality L X a b :=
  baseCausality_old_of_step (fun hb => snocObject_step_old hcl hshape hid hnb hna hb) h hbo

theorem snocObject_proxyBefore_old (hcl : ClusterHistoryOk L X)
    (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc)
    {x y : EvId} {l : Loc} (hy : y.2 < (X.tr y.1).length)
    (h : ProxyBefore L (X.snocObject g e r mb rec) x y l) : ProxyBefore L X x y l := by
  obtain ⟨f, sp, scope, ⟨pc, hf⟩, hthread, hcov, hreach, hxf, hfy⟩ := h
  have hfy' := snocObject_baseCausality_old hcl hshape hid hnb hna hy hfy
  have hfo := (baseCausality_events hfy').1
  exact ⟨f, sp, scope, ⟨pc, (snoc_get_old (r := r) hfo).symm.trans hf⟩, hthread, hcov, hreach,
    snocObject_baseCausality_old hcl hshape hid hnb hna hfo hxf, hfy'⟩

theorem snocObject_asyncBefore_old (ht : EffectValidity L X)
    (hcl : ClusterHistoryOk L X) (hk : ∀ k, e.kind ≠ .tc k)
    (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc)
    {l : Loc} {a b : EvId × Part} (ha : a.1.2 < (X.tr a.1.1).length)
    (hb : b.1.2 < (X.tr b.1.1).length)
    (h : AsyncBefore L (X.snocObject g e r mb rec) l a b) : AsyncBefore L X l a b := by
  obtain ⟨hc, hc', hh⟩ := h
  refine ⟨snocObject_asyncCovers_old ha hc, snocObject_asyncCovers_old hb hc', ?_⟩
  rcases hh with ⟨w, ho, hafter⟩ | ⟨w, ho, hafter⟩
  · have hafter' := snocObject_baseCausality_old hcl hshape hid hnb hna hb hafter
    exact .inl ⟨w, PTX.snocObject_asyncFinished_old ht hk hid (baseCausality_events hafter').1
        ho, hafter'⟩
  · have hafter' := (po_snoc_old (g := g) (e := e) (r := r) hb).mp hafter
    have hwo : w.2 < (X.tr w.1).length := by rw [hafter'.1]; have := hafter'.2.1; omega
    exact .inr ⟨w, PTX.snocObject_asyncOnlyFinished_old hk hwo ho, hafter'⟩

theorem snocObject_modelCausality_old (ht : EffectValidity L X)
    (hcl : ClusterHistoryOk L X) (hk : ∀ k, e.kind ≠ .tc k)
    (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
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
      · exact .inl (snocObject_baseCausality_old hcl hshape hid hnb hna hy hb)
      · exact .inr (ha.of_prefix (Execution.le_trans le_snoc (Execution.le_appendObject ..)) hx hy)
    | async y q =>
      refine ⟨snocObject_asyncCovers_old hy h.1, ?_⟩
      rcases h.2 with hp | ⟨⟨s, ⟨pc, hc⟩, hgen⟩, hb⟩
      · exact .inl (snocObject_proxyBefore_old hcl hshape hid hnb hna hy hp)
      · exact .inr ⟨⟨s, ⟨pc, (snoc_get_old (r := r) hy).symm.trans hc⟩, hgen⟩,
          snocObject_baseCausality_old hcl hshape hid hnb hna hy hb⟩
  | async x p =>
    cases y with
    | thread y =>
      obtain ⟨hc, w, ho, hb⟩ := h
      obtain ⟨hb', hwo⟩ := snocObject_completionBefore_old hx hy
        (snocObject_baseCausality_old hcl hshape hid hnb hna hy)
        (snocObject_proxyBefore_old hcl hshape hid hnb hna hy) hb
      exact ⟨snocObject_asyncCovers_old hx hc, w,
        PTX.snocObject_asyncFinished_old ht hk hid hwo ho, hb'⟩
    | async y q =>
      have transport {a b : EvId × Part}
          (h : AsyncChain L (X.snocObject g e r mb rec) l a b) :
          a.1.2 < (X.tr a.1.1).length → b.1.2 < (X.tr b.1.1).length →
          AsyncChain L X l a b := by
        induction h with
        | direct hd =>
          intro ha hb
          exact .direct (snocObject_asyncBefore_old ht hcl hk hshape hid hnb hna ha hb hd)
        | tail _ hp hd ih =>
          intro ha hb
          have hp0 := appendObject_asyncPresent.mp hp
          have hp' := (snoc_asyncPresent_of_not_tc (X := X) (g := g) (e := e) (r := r) hk).mp hp0
          obtain ⟨event, he⟩ := asyncPresent_issuer ht hp'
          have hm := len_of_get he
          exact .tail (ih ha hm) hp'
            (snocObject_asyncBefore_old ht hcl hk hshape hid hnb hna hm hb hd)
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

private theorem intent_index {v : Ref} {a : Acc} {w : Bool} (h : X.Intent v a w) :
    v.issuer.2 < (X.tr v.issuer.1).length := by
  obtain ⟨ev, he⟩ := intent_issuer h
  exact len_of_get he

theorem snocObject_noFuture {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hk : ∀ k, e.kind ≠ .tc k) (hrd : ∀ a bs, e.kind ≠ .rd a bs)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc) :
    NoFuture L (X.snocObject g e r mb rec) := by
  intro v a bs k w hr hk' hrf hv
  have hr' := (snoc_memReads_control (g := g) (e := e) (r := r) hX.effectValidity hk hrd
    (fun _ _ _ he => by rw [hshape] at he; cases he)).mp hr
  have hle : X.le (X.snocObject g e r mb rec) :=
    Execution.le_trans (le_snoc (X := X) (g := g) (e := e) (r := r))
      (Execution.le_appendObject _ _ _)
  rw [hle.2.1 v k ⟨a, bs, hr'⟩] at hrf
  have hsrc := (hX.rf v a bs hr').2 k hk'
  rw [hrf] at hsrc
  obtain ⟨target, bytes, hw, _⟩ := hsrc
  exact hX.noFuture v a bs k w hr' hk' hrf
    (ByteCausality.le_reflect hle hX.tma.2.1 hX.tcCommit
      (fun old edge => snocObject_modelCausality_old hX.effectValidity hX.cluster
        hk hshape hid hnb hna (intent_index hr'.intent) old edge)
      (fun hw' => (PTX.snocObject_observedMma_iff hX.tcCommit hid hw').mp)
      (intent_index hw.intent) hv)

theorem snocObject_hidden {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hk : ∀ k, e.kind ≠ .tc k) (hrd : ∀ a bs, e.kind ≠ .rd a bs)
    (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc) :
    Hidden L (X.snocObject g e r mb rec) := by
  intro v a bs k w target bytes hr hk' hw hc hv
  have hr' := (snoc_memReads_control (g := g) (e := e) (r := r) hX.effectValidity hk hrd
    (fun _ _ _ he => by rw [hshape] at he; cases he)).mp hr
  have hw' := (snoc_memWrites_control (g := g) (e := e) (r := r) hX.effectValidity hwr
    (fun _ _ _ he => by rw [hshape] at he; cases he)).mp hw
  have hle : X.le (X.snocObject g e r mb rec) :=
    Execution.le_trans (le_snoc (X := X) (g := g) (e := e) (r := r))
      (Execution.le_appendObject _ _ _)
  rw [hle.2.1 v k ⟨a, bs, hr'⟩]
  have reflect {src dst : Ref} {loc : Loc}
      (hsrc : src.issuer.2 < (X.tr src.issuer.1).length)
      (hdst : dst.issuer.2 < (X.tr dst.issuer.1).length)
      (he : ByteCausality L (X.snocObject g e r mb rec) loc src dst) :
      ByteCausality L X loc src dst :=
    ByteCausality.le_reflect hle hX.tma.2.1 hX.tcCommit
      (fun old edge => snocObject_modelCausality_old hX.effectValidity hX.cluster
        hk hshape hid hnb hna hsrc old edge)
      (fun hw' => (PTX.snocObject_observedMma_iff hX.tcCommit hid hw').mp) hdst he
  have hv' := reflect (intent_index hw'.intent) (intent_index hr'.intent) hv
  have hh := hX.hidden v a bs k w target bytes hr' hk' hw' hc hv'
  cases hs : X.rf v k with
  | none => simp only [hs] at hh
  | some src =>
    rw [hs] at hh
    have hsrc := (hX.rf v a bs hr').2 k hk'
    rw [hs] at hsrc
    obtain ⟨target', bytes', hsrc, _⟩ := hsrc
    exact fun hv => hh (reflect (intent_index hsrc.intent) (intent_index hw'.intent) hv)

/-- An object-recording wait adds no Tensor Memory evidence about old loads. -/
theorem snocObject_readOk {A : List Assumption} (hv : EffectValidity L X)
    (hr : TcMma.ReadOk L A X) (hcl : ClusterHistoryOk L X)
    (hshape : e.kind = .wait waitM waitP waitOk true waitScope)
    (hid : rec.id = .thread (g, (X.tr g).length)) (hk : ∀ k, e.kind ≠ .tc k)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc) :
    TcMma.ReadOk L A (X.snocObject g e r mb rec) := by
  have hlog : ∀ l, List.IsPrefix (X.objects l)
      ((fun l => if l = mb then X.objects mb ++ [rec] else X.objects l) l) := by
    intro l
    by_cases hl : l = mb
    · subst l; exact ⟨[rec], by simp⟩
    · simp [hl]
  refine (TcMma.ReadPreserved.readOk ⟨Execution.le_trans (le_snoc (X := X) (g := g) (e := e)
      (r := r)) (Execution.le_appendObject _ _ _), fun hf =>
        ⟨snocObject_baseCausality_old hcl hshape hid hnb hna hf,
      fun h => baseCausality_snoc_history (records := fun l => if l = mb then X.objects mb ++ [rec]
        else X.objects l) hlog h⟩, fun hw => snocObject_observedMma_iff hv.tcCommit hid hw,
      fun _ _ h => h, fun _ _ hr => .inl hr, fun hw => snocObject_mbarExec_old hv.tma.2.2.1 hid hw,
      fun _ hq => .inl hq⟩
      hr hv.tma.2.1) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
  change (X.snoc g e r).get load = _ at hl
  rcases snoc_get_cases hl with ⟨rfl, he⟩ | ⟨hold, _⟩
  · exact (hk _ (by rw [← he])).elim
  · omega

/-- An acquiring wait at any scope, with its own record on one object, keeps the
execution-order axioms. -/
theorem poll_object_orderOk {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X)
    (hk : ∀ k, e.kind ≠ .tc k) (hwait : e.kind = .wait waitM waitP waitOk true waitScope)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (m : Loc) (rec : MBarrier.Record Ref) (hid : rec.id = .thread (g, (X.tr g).length)) :
    OrderOk L K A ((X.snoc g e r).appendObject m rec) :=
  (SnocWaitFrame.of_waitFree hX ⟨by rw [hwait]; trivial, hk⟩ hns (by rw [hwait]; nofun)
    (by rw [hwait]; rfl) (by obtain ⟨pc, k⟩ := e; simp only at hwait; subst hwait; rfl)
    (fun _ _ _ _ he => by rw [hwait] at he; cases he)
    (fun _ _ _ he => by rw [hwait] at he; cases he)
    (snoc_not_allocResult_of_not_wr (by rw [hwait]; nofun))).objectOrderOk hX m rec hid

end
end PTX.Step
