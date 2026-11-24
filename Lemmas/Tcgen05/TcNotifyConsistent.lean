-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame

public import Lemmas.Async.AsyncChain
public import Lemmas.Tcgen05.TcNotifyObject
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Order.Order
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.MmaFinishConsistent
public import Lemmas.Tcgen05.TcMmaReadMono
public import Lemmas.Snoc.Snoc
public import Lemmas.Order.CompletionFrame

@[expose] public section

section
/-! A commit notification appended after existing waits cannot change their observations. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {rank : Fin 16} {mb : Loc} {rec : Record Ref}

theorem notifyTcRecord_baseCausality_iff (hid : rec.id = .async i (.tcNotify rank)) {e f : EvId} :
    baseCausality L (X.notifyTcRecord i rank mb rec) e f ↔ baseCausality L X e f := by
  change baseCausality L ((X.notifyTc i rank).appendObject mb rec) e f ↔ _
  rw [appendObject_baseCausality_iff (fun w _ _ => by rw [hid]; simp)]
  rfl

theorem notifyTcRecord_asyncObserved_iff (ho : ObjectsOk X)
    (hn : rank ∉ X.tcNotified i) (hid : rec.id = .async i (.tcNotify rank))
    {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.notifyTcRecord i rank mb rec) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  change AsyncObserved ((X.notifyTc i rank).appendObject mb rec) j p w acq ws ↔ _
  rw [appendObject_asyncObserved_iff (by rw [hid]; simp)]
  have hnone : ∀ loc,
      ¬ UpdateBeforeWait (X.objects loc) (.async i (.tcNotify rank)) (.thread w) := by
    rintro loc ⟨j, k, r, waiter, phase, hj, hrid, _⟩
    exact no_tc_notification_record ho hn (List.mem_of_getElem? hj) hrid
  have hmem : ∀ j r loc, UpdateBeforeWait (X.objects loc) (.async j (.tcNotify r)) (.thread w) →
      (r ∈ (X.notifyTc i rank).tcNotified j ↔ r ∈ X.tcNotified j) := by
    intro j r loc hw
    by_cases he : j = i
    · subst j
      have hr : r ≠ rank := by rintro rfl; exact hnone loc hw
      simp [Execution.notifyTc, hr]
    · simp [Execution.notifyTc, he]
  cases p <;> try rfl
  all_goals
    constructor
    · rintro ⟨n, loc, ⟨c, s, r, rfl, ht, hc, htg, hnot⟩, hwo⟩
      exact ⟨_, loc, ⟨c, s, r, rfl, ht, hc, htg, (hmem c r loc hwo.2).1 hnot⟩, hwo⟩
    · rintro ⟨n, loc, ⟨c, s, r, rfl, ht, hc, htg, hnot⟩, hwo⟩
      exact ⟨_, loc, ⟨c, s, r, rfl, ht, hc, htg, (hmem c r loc hwo.2).2 hnot⟩, hwo⟩

/-- The stages that a group wait waits for are not commit notifications, so their presence is
unchanged. -/
theorem notifyTcRecord_groupPresent (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages (X.notifyTcRecord i rank mb rec) j k,
        (X.notifyTcRecord i rank mb rec).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl <;> exact Iff.rfl

theorem notifyTcRecord_asyncFinished_iff (ho : ObjectsOk X)
    (hn : rank ∉ X.tcNotified i) (hid : rec.id = .async i (.tcNotify rank))
    {j w : EvId} {p : Part} :
    AsyncFinished L (X.notifyTcRecord i rank mb rec) j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      notifyTcRecord_groupPresent j k)
    (exists_congr fun _ => and_congr_left' (notifyTcRecord_asyncObserved_iff ho hn hid))

theorem notifyTcRecord_asyncOnlyFinished_iff {j w : EvId} {p : Part} :
    AsyncOnlyFinished (X.notifyTcRecord i rank mb rec) j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ => notifyTcRecord_groupPresent j _

theorem notifyTcRecord_asyncBefore_iff (ho : ObjectsOk X)
    (hn : rank ∉ X.tcNotified i) (hid : rec.id = .async i (.tcNotify rank))
    {l : Loc} {a b : EvId × Part} :
    AsyncBefore L (X.notifyTcRecord i rank mb rec) l a b ↔ AsyncBefore L X l a b := by
  exact AsyncBefore.congr (L:=L) (X:=X.notifyTcRecord i rank mb rec) (Y:=X)
    (fun _ _ => Iff.rfl)
    (fun _ _ _ => notifyTcRecord_asyncFinished_iff ho hn hid)
    (fun _ _ _ => notifyTcRecord_asyncOnlyFinished_iff)
    (fun _ _ _ _ => notifyTcRecord_baseCausality_iff hid)
    (fun _ _ _ _ => Iff.rfl)

theorem notifyTcRecord_asyncPresent_on_edge {l : Loc} {a b : EvId × Part}
    (hedge : AsyncBefore L (X.notifyTcRecord i rank mb rec) l a b) :
    (X.notifyTcRecord i rank mb rec).AsyncPresent a.1 a.2 ↔ X.AsyncPresent a.1 a.2 := by
  rcases a with ⟨j,p⟩
  cases p <;> try rfl
  case tcNotify rank' =>
    obtain ⟨acc,w,hi,_⟩ := hedge.1
    cases hi.2

theorem notifyTcRecord_modelCausality_iff (ho : ObjectsOk X)
    (hn : rank ∉ X.tcNotified i) (hid : rec.id = .async i (.tcNotify rank))
    {l : Loc} {e f : Ref} :
    modelCausality L (X.notifyTcRecord i rank mb rec) l e f ↔ modelCausality L X l e f := by
  have hp : ∀ e j, ProxyBefore L (X.notifyTcRecord i rank mb rec) e j l ↔
      ProxyBefore L X e j l := by
    intro e j
    unfold ProxyBefore
    simp only [notifyTcRecord_baseCausality_iff hid]
    rfl
  cases e with
  | thread e =>
    cases f with
    | thread f => exact or_congr (notifyTcRecord_baseCausality_iff hid) Iff.rfl
    | async j p =>
      simp only [modelCausality, hp, notifyTcRecord_baseCausality_iff hid]
      rfl
  | async j p =>
    cases f with
    | thread f =>
      have hcb (w) : ObservedCompletionBefore L (X.notifyTcRecord i rank mb rec) l j p w f ↔
          ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr rfl rfl (notifyTcRecord_baseCausality_iff hid) (hp w f)
      simp only [modelCausality, notifyTcRecord_asyncFinished_iff ho hn hid, hcb]
      rfl
    | async k q =>
      exact and_congr_right fun _ =>
        AsyncChain.congr_on_edges (fun _ _ => notifyTcRecord_asyncBefore_iff ho hn hid)
          (fun _ _ => notifyTcRecord_asyncPresent_on_edge)

theorem notifyTcRecord_mbarExec_iff (hid : rec.id = .async i (.tcNotify rank)) {x w : EvId} :
    MbarExec L (X.notifyTcRecord i rank mb rec) x w ↔ MbarExec L X x w := by
  change MbarExec L ((X.notifyTc i rank).appendObject mb rec) x w ↔ _
  unfold MbarExec
  simp only [appendObject_waitObserves_iff (r := rec) (w := w) (by rw [hid]; simp)]
  rfl

end
end PTX
end

section
/-! A newly appended commit notification has no outgoing object dependency. Its
start/finish nodes form a sink of the extension; every other order relation is old. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {rank : Fin 16} {mb : Loc} {rec : Record Ref}

theorem notifyTcRecord_no_before (ho : ObjectsOk X)
    (hn : rank ∉ X.tcNotified i) {loc : Loc} {f : Ref} :
    ¬ Before ((X.notifyTcRecord i rank mb rec).objects loc) (.async i (.tcNotify rank)) f := by
  rintro ⟨a, b, ra, rb, ha, hid, hb, _, hab⟩
  by_cases hm : loc = mb
  · subst loc
    have hb' : (X.objects mb ++ [rec])[b]? = some rb := by
      simpa [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc] using hb
    have hbl := (List.getElem?_eq_some_iff.mp hb').1
    have hao : a < (X.objects mb).length := by
      simp only [List.length_append, List.length_singleton] at hbl
      omega
    have ha' : (X.objects mb)[a]? = some ra := by
      simpa only [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc,
        ↓reduceIte, List.getElem?_append_left hao] using ha
    exact no_tc_notification_record ho hn (List.mem_of_getElem? ha') hid
  · have ha' : (X.objects loc)[a]? = some ra := by
      simpa [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, hm] using ha
    exact no_tc_notification_record ho hn (List.mem_of_getElem? ha') hid

theorem notifyTcRecord_present_old {e : Ref} (he : e ≠ .async i (.tcNotify rank)) :
    (X.notifyTcRecord i rank mb rec).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    rename_i r
    simp only [Execution.RefPresent, Execution.AsyncPresent, Execution.notifyTcRecord,
      Execution.appendObject, Execution.notifyTc]
    by_cases hj : j = i
    · subst hj
      have hr : r ≠ rank := fun h => he (by rw [h])
      simp [hr]
    · simp [hj]

/-- The needs of every event are unchanged: the new record is observed by no wait, and the
presence of every recorded update is old. -/
theorem notifyTcRecord_needs (ho : ObjectsOk X) (hn : rank ∉ X.tcNotified i)
    (hid : rec.id = .async i (.tcNotify rank)) (e : EvId) :
    Needs L (X.notifyTcRecord i rank mb rec) e = Needs L X e := by
  refine (appendObject_needs (X := X.notifyTc i rank)
    (fun l q hq h => no_tc_notification_record ho hn hq (h.trans hid))
    (fun e h => by rw [hid] at h; cases h) e).trans ?_
  refine needs_congr (X := X) (Y := X.notifyTc i rank) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e m => pollNeeds_congr (X := X) (Y := X.notifyTc i rank) (fun _ => rfl)
      (fun m r hr w => and_congr ?_ Iff.rfl) e m) e
  exact notifyTcRecord_present_old (mb := mb) (rec := rec) (no_tc_notification_record ho hn hr)

/-- The new notification fills no need: it is no stage of a group wait and no recorded update of
`X`. -/
theorem notifyTcRecord_not_witness (ho : ObjectsOk X) (hn : rank ∉ X.tcNotified i)
    (hid : rec.id = .async i (.tcNotify rank)) (w : EvId) :
    ¬ Witness L (X.notifyTcRecord i rank mb rec) (.async i (.tcNotify rank)) w := by
  refine not_witness_of_needRef (notifyTcRecord_needs ho hn hid w) ?_
  rintro (⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨m, r, hr, h⟩)
  · cases h
  · cases h
    rcases groupWaitStages_cases X _ k hq with h | h | h | h <;> cases h
  · exact no_tc_notification_record ho hn hr h.symm

theorem notifyTcRecord_waits_from_notify (ho : ObjectsOk X)
    (hn : rank ∉ X.tcNotified i) (hid : rec.id = .async i (.tcNotify rank))
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.notifyTcRecord i rank mb rec) (.async i (.tcNotify rank), b) v) :
    v.1 = .async i (.tcNotify rank) ∧ b = false ∧ v.2 = true := by
  rcases h with ⟨he, hb, hb', _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, ha⟩ | ⟨_, _, loc, ho'⟩ | ⟨j, k, he, _⟩ | ⟨_, _, w, -, hw⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨_, _, hi⟩
  · exact ⟨he.symm, hb, hb'⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · exfalso
    rcases ha with ⟨-, h0, -⟩ | ⟨-, -, ha⟩
    · simp_all
    · cases hv : v.1 with
      | thread j => rw [hv] at ha; exact ha
      | async j p => rw [hv] at ha; cases p <;> exact ha
  · exact (notifyTcRecord_no_before ho hn ho').elim
  · cases he
  · exact (notifyTcRecord_not_witness ho hn hid w hw).elim
  · cases he
  · cases he
  · cases he
  · cases he
  · cases he
  · obtain ⟨_, _, k, q, he, _⟩ := hi
    cases he

/-- The appended commit notification waits on nothing and has no successor in its object;
outside it every order relation is old. -/
theorem notifyTcRecord_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : rank ∉ X.tcNotified i)
    (hid : rec.id = .async i (.tcNotify rank)) :
    SinkFrame L K A X (X.notifyTcRecord i rank mb rec)
      (CompletionNodes L (X.notifyTcRecord i rank mb rec) (· = .async i (.tcNotify rank))) := by
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hnot : ∀ {w : Ref}, ¬ w = .async i (.tcNotify rank) → rec.id ≠ w := fun hw he =>
    hw (he.symm.trans hid)
  have hth : ∀ e, rec.id ≠ .thread e := fun e h => by rw [hid] at h; cases h
  have hpres : ∀ {e : Ref}, e ≠ .async i (.tcNotify rank) →
      (X.notifyTcRecord i rank mb rec).RefPresent e → X.RefPresent e :=
    fun he h => (notifyTcRecord_present_old he).mp h
  have hold : ∀ {u : Ref × Bool}, ¬ CompletionNodes L (X.notifyTcRecord i rank mb rec)
      (· = .async i (.tcNotify rank)) u → u.1 ≠ .async i (.tcNotify rank) :=
    fun hu he => hu (.inl he)
  have hobject : ∀ o (u v : Ref × Bool), v.1 ≠ .async i (.tcNotify rank) →
      ObjectOrder L (X.notifyTcRecord i rank mb rec) o u v → ObjectOrder L X o u v :=
    fun o u v hv h => (appendObject_objectOrder_iff (X := X.notifyTc i rank) (hnot hv)).mp h
  refine sinkFrame_completion (· = .async i (.tcNotify rank)) (fun _ h => by cases h)
    (fun u v hu h => ?_) (fun w x hx hw => (notifyTcRecord_not_witness ho hn hid w (hx ▸ hw)).elim)
    (fun u v hu hv hc => ?_) (fun x w hx hw h => ?_)
    (fun o u v _ hv h => hobject o u v (hold hv) h) (fun o u v _ hv h => ?_)
    (fun u v hu hv hc => ?_) (fun m j p y hb => ?_) (fun m j p y _ _ h => ?_) hX.initFence
    (fun _ _ _ h => h) (fun m y init h => ?_) (fun _ => rfl)
  · obtain ⟨e, b⟩ := u
    change e = _ at hu
    subst hu
    obtain ⟨h1, h2, h3⟩ := notifyTcRecord_waits_from_notify ho hn hid h
    exact .inl ⟨h1, h2, h3⟩
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | ⟨h1, h2, j, k, h3, h4, hc⟩ | ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, h7, h8⟩
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.notifyTcRecord i rank mb rec)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl ⟨h1, h2, j, k, h3, h4,
        (notifyTcRecord_baseCausality_iff hid).mp hc⟩))
    · exact .single (.inr (.inr ⟨h1, h2, k, h3, c, p, w, ws, h5, h6,
        (notifyTcRecord_asyncObserved_iff ho hn hid).mp h7, h8⟩))
  · have hx' : x ≠ .async i (.tcNotify rank) := hold hx
    have hw' : w ≠ .async i (.tcNotify rank) := hold hw
    rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · have h' := (appendObject_mbarObserved_iff (X := X.notifyTc i rank) (hnot hx')
        (hnot hw')).mp hm
      exact .inl ⟨⟨hpres hx' h'.1, h'.2⟩, rest⟩
    · exact .inr ⟨j, p, k, q, rfl, h2, hpres hx' h3, h4, h5⟩
  · cases o with
    | mbar m => exact ⟨hobject _ u v (hold hv) h.1, h.2⟩
    | ctaBar c id => exact hobject (.ctaBar c id) u v (hold hv) h
    | cluster c => exact hobject (.cluster c) u v (hold hv) h
    | tmem c => exact hobject (.tmem c) u v (hold hv) h
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | hc | ⟨h1, h2, j, hj, fills, hn', hx, hf⟩ | hc
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.notifyTcRecord i rank mb rec)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl (IssueStage.transfer (X := X)
        (Y := X.notifyTcRecord i rank mb rec) (fun _ => rfl) (hpres (hold hv)) hc)))
    · rw [notifyTcRecord_needs ho hn hid] at hn'
      exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, fills, hn', hpres (hold hu) hx, hf⟩)))
    · exact .single (.inr (.inr (.inr hc)))
  · by_cases hy : rec.id = y
    · rintro ⟨k, rfl, -⟩
      exact hth k hy
    · have hb' := (appendObject_objectOrder_iff (X := X.notifyTc i rank) (L := L)
        (o := .mbar m) (u := (.async j p, true)) (v := (y, true)) hy).mp ⟨rfl, rfl, hb⟩
      exact (hX.asyncObject m j p y hb'.2.2).1
  · rcases h with h | ⟨k, ws, rfl, hw⟩
    · exact .inl h
    · exact .inr ⟨k, ws, rfl, (appendObject_waitObserves_iff (hth k)).mp hw⟩
  · have hb' := (appendObject_objectOrder_iff (X := X.notifyTc i rank) (L := L)
      (o := .mbar m) (u := (y, true)) (v := (.thread init, true)) (hth init)).mp ⟨rfl, rfl, h⟩
    exact hb'.2.2

end
end PTX
end

section
/-! Commit notification is a separately checked extension, after every tracked MMA
has completed. It changes no earlier read or wait result. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

theorem Execution.le_notifyTc (X : Execution) (i : EvId) (rank : Fin 16) :
    X.le (X.notifyTc i rank) := by
  refine ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, Extends.refl _,
    (Execution.le_refl X).2.2.2.1, (Execution.le_refl X).2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.2.2.2.2.2.1,
    ?_⟩
  intro j
  by_cases he : j = i
  · simp [notifyTc, he, Finset.subset_insert]
  · simp [notifyTc, he]

theorem Execution.le_notifyTcRecord (X : Execution) (i : EvId) (rank : Fin 16) (mb : Loc)
    (rec : Record Ref) : X.le (X.notifyTcRecord i rank mb rec) :=
  Execution.le_trans (X.le_notifyTc i rank) (Execution.le_appendObject _ _ _)

variable {L : Launch} {X : Execution} {i : EvId} {rank : Fin 16} {mb : Loc} {rec : Record Ref}

theorem notifyTcRecord_memReads {e : Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.notifyTcRecord i rank mb rec).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p => cases p <;> rfl

theorem notifyTcRecord_memWrites {e : Ref} {a : Acc} {bs : List Byte} :
    (X.notifyTcRecord i rank mb rec).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p => cases p <;> rfl

/-- A notification adds no evidence about loads already in the execution. -/
theorem notifyTcRecord_readOk {A : List Assumption} (ho : ObjectsOk X)
    (hr : TcMma.ReadOk L A X) (hte : AsyncCopy.TcEffectsOk X) (hn : rank ∉ X.tcNotified i)
    (hid : rec.id = .async i (.tcNotify rank)) :
    TcMma.ReadOk L A (X.notifyTcRecord i rank mb rec) := by
  refine (TcMma.ReadPreserved.readOk ⟨X.le_notifyTcRecord i rank mb rec,
    fun _ => notifyTcRecord_baseCausality_iff hid, fun _ => notifyTcRecord_asyncObserved_iff ho hn
        hid,
    fun _ _ h => h, fun _ _ hr => .inl hr, fun _ => notifyTcRecord_mbarExec_iff hid,
    fun _ hq => .inl hq⟩ hr hte) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
  have := len_of_get (X := X) hl
  omega

theorem consistent_notifyTcRecord {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {s : TcCommit.Spec} (hi : X.Commit i s)
    (hmb : TcCommit.target s rank = some mb) (hn : rank ∉ X.tcNotified i)
    (hd : ∀ x, TracksMma X x i → X.async.mmaDone x = true)
    (hid : rec.id = .async i (.tcNotify rank)) (ha : rec.action = .arrive 1 0)
    (hc : CheckedLog (X.objects mb ++ [rec]))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.notifyTcRecord i rank mb rec)) :
    Consistent L K A mem0 (X.notifyTcRecord i rank mb rec) := by
  have hcommit : CommitOk (X.notifyTcRecord i rank mb rec) := by
    intro j r hr
    by_cases he : j = i ∧ r = rank
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨⟨s, mb, hi, hmb⟩, hd⟩
    · have hr' : r ∈ X.tcNotified j := by
        by_cases hj : j = i
        · subst hj
          have hne : r ≠ rank := fun h => he ⟨rfl, h⟩
          simpa [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, hne] using hr
        · simpa [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, hj] using hr
      obtain ⟨⟨s', m', hc, ht⟩, hdone⟩ := hX.tcCommit j r hr'
      exact ⟨⟨s', m', hc, ht⟩, fun x htr => hdone x htr⟩
  have hfr := notifyTcRecord_sinkFrame (mb := mb) hX hn hid
  have horder := hfr.orderOk hX.orderOk
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hdep : DependencyOk L K (X.notifyTcRecord i rank mb rec) := by
    refine ⟨?_, horder.depAcyclic⟩
    intro e hret n hn'
    rw [notifyTcRecord_needs ho hn hid] at hn'
    have hready := hX.dependency.ready e hret n hn'
    cases n with
    | cond holds => exact hready
    | node fills =>
      obtain ⟨x, hx, hf⟩ := hready
      have hne : x ≠ .async i (.tcNotify rank) := by
        rintro rfl
        rcases needs_node_cases hn' hf with ⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨m, r, hr, h⟩
        · cases h
        · cases h
          rcases groupWaitStages_cases X _ k hq with h | h | h | h <;> cases h
        · exact no_tc_notification_record ho hn hr h.symm
      exact ⟨x, (notifyTcRecord_present_old hne).mpr hx, hf⟩
  have reflect {l e f} :
      ByteCausality L (X.notifyTcRecord i rank mb rec) l e f → ByteCausality L X l e f :=
    ByteCausality.of_same_context (X := X) (Y := X.notifyTcRecord i rank mb rec) rfl rfl
      (fun h => (notifyTcRecord_modelCausality_iff hX.tma.2.2.1 hn hid).mp h)
      (fun h => (notifyTcRecord_asyncObserved_iff hX.tma.2.2.1 hn hid).mp h)
  refine {
    thr := hX.thr, outside := hX.outside, ctaBar := hX.ctaBar, shfl := hX.shfl,
    cluster := hX.cluster, elect := hX.elect, vote := hX.vote, warpValue := hX.warpValue,
    warpBar := hX.warpBar, matrix := hX.matrix,
    clc := hX.clc, tensor := hX.tensor, store := hX.store,
    tmemPair := hX.tmemPair, tmemPairResult := hX.tmemPairResult,
    tcCommit := hcommit,
    tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion,
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl,
    tcRead := notifyTcRecord_readOk ho hX.tcRead hX.tma.2.1 hn hid,
    reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩,
    atomic := atomicOk_congr (X := X) (Y := X.notifyTcRecord i rank mb rec)
      (fun p l n => by cases p <;> exact Iff.rfl) (fun _ _ => rmwStrong_congr rfl rfl)
      (fun p k => by cases p <;> rfl) hX.atomic,
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs h =>
      hX.fenceSc.causal e f hs ((notifyTcRecord_baseCausality_iff hid).mp h)⟩,
    dependency := hdep,
    observation := horder.observation, object := horder.object,
    asyncObject := horder.asyncObject, initFence := horder.initFence,
    asm := hasm, rf := ?_, noFuture := ?_, hidden := ?_, tma := ?_ }
  · intro e a bs hr
    obtain ⟨hlen, hv⟩ := hX.rf e a bs (notifyTcRecord_memReads.mp hr)
    refine ⟨hlen, fun k hk => ?_⟩
    have hh := hv k hk
    cases hs : X.rf e k with
    | none =>
      rw [show (X.notifyTcRecord i rank mb rec).rf e k = X.rf e k from rfl, hs]
      simp only [hs] at hh
      exact hh
    | some w =>
      rw [show (X.notifyTcRecord i rank mb rec).rf e k = X.rf e k from rfl, hs]
      rw [hs] at hh
      obtain ⟨target, bytes, hw, hcover, hbytes⟩ := hh
      exact ⟨target, bytes, notifyTcRecord_memWrites.mpr hw, hcover, hbytes⟩
  · intro e a bs k w hr hk hs hv
    exact hX.noFuture e a bs k w (notifyTcRecord_memReads.mp hr) hk hs
      (reflect hv)
  · intro e a bs k w target bytes hr hk hw hc hv
    have hh := hX.hidden e a bs k w target bytes (notifyTcRecord_memReads.mp hr) hk
      (notifyTcRecord_memWrites.mp hw) hc
          (reflect hv)
    cases hs : X.rf e k with
    | none => simp only [hs] at hh
    | some v =>
      rw [show (X.notifyTcRecord i rank mb rec).rf e k = X.rf e k from rfl, hs]
      rw [hs] at hh
      exact fun h => hh (reflect h)
  · exact ⟨hX.tma.1, hX.tma.2.1, notifyTcRecord_objects hX.tma.2.2.1 hi hmb hn hid ha hc,
      hX.tma.2.2.2⟩

private theorem tc_notify_sum_map_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ i ∈ xs, f i ≤ g i) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A new commit notification strictly increases counted size. -/
theorem notifyTcRecord_size {L : Launch} {X : Execution} {i : EvId} {rank : Fin 16} {mb : Loc}
    {rec : Record Ref} (hg : i.1 < L.threads) (hi : i.2 < (X.tr i.1).length)
    (hn : rank ∉ X.tcNotified i) :
    X.size L < (X.notifyTcRecord i rank mb rec).size L := by
  have hs : ∀ j, (if j = i then X.asyncSize j + 1 else X.asyncSize j) ≤
      (X.notifyTcRecord i rank mb rec).asyncSize j := by
    intro j
    by_cases he : j = i
    · subst j
      have hc : (X.tcNotified i).card + 1 ≤
          ((X.notifyTcRecord i rank mb rec).tcNotified i).card := by
        simp only [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, ↓reduceIte,
          Finset.card_insert_of_notMem hn, le_refl]
      simp only [↓reduceIte]
      unfold Execution.asyncSize
      have he : (X.notifyTcRecord i rank mb rec).elemSize i = X.elemSize i := rfl
      rw [he]
      rw [show ∀ a b c : Nat, a + b + c + 1 = a + (b + 1) + c from fun a b c => by omega]
      exact Nat.add_le_add_right (Nat.add_le_add_left hc _) _
    · have hc : (X.tcNotified j) = (X.notifyTcRecord i rank mb rec).tcNotified j := by
        simp only [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, he,
          ↓reduceIte]
      simp only [he, ↓reduceIte]
      unfold Execution.asyncSize
      rw [hc]
      exact Nat.le_refl _
  let f := fun g => (X.tr g).countP Event.counts +
    ((List.range (X.tr g).length).map fun k => X.asyncSize (g, k)).sum
  have hb : ∀ g, (if g = i.1 then f g + 1 else f g) ≤
      ((X.notifyTcRecord i rank mb rec).tr g).countP Event.counts +
      ((List.range ((X.notifyTcRecord i rank mb rec).tr g).length).map
        fun k => (X.notifyTcRecord i rank mb rec).asyncSize (g, k)).sum := by
    intro g
    have hm := tc_notify_sum_map_mono (List.range (X.tr g).length)
      (fun k => if (g, k) = i then X.asyncSize (g, k) + 1 else X.asyncSize (g, k))
      (fun k => (X.notifyTcRecord i rank mb rec).asyncSize (g, k)) (fun k _ => hs (g, k))
    by_cases he : g = i.1
    · subst g
      have heq : ∀ k, (i.1, k) = i ↔ k = i.2 := by intro k; exact Prod.ext_iff.trans (by simp)
      simp only [heq] at hm
      rw [sum_range_bump, ite_eq_left hi] at hm
      simpa [f, Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc,
        Nat.add_assoc] using
        Nat.add_le_add_left hm ((X.tr i.1).countP Event.counts)
    · have heq : ∀ k, (g, k) ≠ i := fun k h => he (congrArg Prod.fst h)
      simpa [f, Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, he, heq] using
        Nat.add_le_add_left hm ((X.tr g).countP Event.counts)
  have hm := tc_notify_sum_map_mono (List.range L.threads)
    (fun g => if g = i.1 then f g + 1 else f g) _ (fun g _ => hb g)
  rw [sum_range_bump, ite_eq_left hg] at hm
  change X.threadSize L + 1 ≤ (X.notifyTcRecord i rank mb rec).threadSize L at hm
  have hp : (X.notifyTcRecord i rank mb rec).pairSize L = X.pairSize L := rfl
  simp only [Execution.size, hp]
  omega

end
end PTX
end
