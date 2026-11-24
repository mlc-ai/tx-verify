-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tmem.AllocResult

public import Lemmas.Protocol.CpAsyncArrive
public import Lemmas.Order.CompletionFrame
public import Lemmas.Async.AsyncChain
public import Lemmas.Step.Object
public import Lemmas.Step.Drain
public import Lemmas.Step.WfInOrder
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.TcMmaReadMono

@[expose] public section

namespace PTX

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {X : Execution} {i : EvId} {m : Loc} {rec : Record Ref}

theorem finishCpAsyncArrive_baseCausality_iff (hid : rec.id = .async i .arriveOn) {e f : EvId} :
    baseCausality L (X.finishCpAsyncArrive i m rec) e f ↔ baseCausality L X e f := by
  change baseCausality L ((X.markCpAsyncArrived i).appendObject m rec) e f ↔ _
  rw [appendObject_baseCausality_iff (fun w _ _ => by rw [hid]; simp)]
  rfl

theorem finishCpAsyncArrive_asyncObserved_iff (ho : ObjectsOk X) (hn : X.async.arrived i = false)
    (hid : rec.id = .async i .arriveOn) {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.finishCpAsyncArrive i m rec) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  change AsyncObserved ((X.markCpAsyncArrived i).appendObject m rec) j p w acq ws ↔ _
  rw [appendObject_asyncObserved_iff (by rw [hid]; simp)]
  have hno : ∀ loc,
      ¬ UpdateBeforeWait (X.objects loc) (.async i .arriveOn) (.thread w) := by
    rintro loc ⟨j, k, r, waiter, phase, hj, hrid, _⟩
    exact no_arriveOn_record ho hn (List.mem_of_getElem? hj) hrid
  have happ : ∀ j (loc : Loc),
      UpdateBeforeWait (X.objects loc) (.async j .arriveOn) (.thread w) →
      ((X.markCpAsyncArrived i).async.arrived j = true ↔ X.async.arrived j = true) := by
    intro j loc hw
    have he : j ≠ i := by rintro rfl; exact hno loc hw
    simp [Execution.markCpAsyncArrived, he]
  have hpart (p : Part) (hp : p = .read .copy ∨ p = .write .copy) :
      AsyncObserved (X.markCpAsyncArrived i) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
    constructor <;> rintro ⟨n, loc, hnot, hw⟩ <;> refine ⟨n, loc, ?_, hw⟩
    · rcases hp with rfl | rfl
      all_goals
        rcases hnot with h | ⟨j, noinc, rfl, ht, hi, ha⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, noinc, rfl, ht, hi, (happ j loc hw.2).mp ha⟩
    · rcases hp with rfl | rfl
      all_goals
        rcases hnot with h | ⟨j, noinc, rfl, ht, hi, ha⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, noinc, rfl, ht, hi, (happ j loc hw.2).mpr ha⟩
  cases p <;> try rfl
  case readCopy => exact hpart _ (Or.inl rfl)
  case writeCopy => exact hpart _ (Or.inr rfl)

theorem finishCpAsyncArrive_present_old {e : Ref} (he : e ≠ .async i .arriveOn) :
    (X.finishCpAsyncArrive i m rec).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case arriveOn =>
      have hj : j ≠ i := fun h => he (by rw [h])
      simp [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCpAsyncArrive,
        Execution.appendObject, Execution.markCpAsyncArrived, hj]

theorem finishCpAsyncArrive_needs (ho : ObjectsOk X) (hn : X.async.arrived i = false)
    (hid : rec.id = .async i .arriveOn) (e : EvId) :
    Needs L (X.finishCpAsyncArrive i m rec) e = Needs L X e := by
  refine (appendObject_needs (X := X.markCpAsyncArrived i)
    (fun l q hq h => no_arriveOn_record ho hn hq (h.trans hid))
    (fun e h => by rw [hid] at h; cases h) e).trans ?_
  refine needs_congr (X := X) (Y := X.markCpAsyncArrived i) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e m => pollNeeds_congr (X := X) (Y := X.markCpAsyncArrived i) (fun _ => rfl)
      (fun _ r hr _ => and_congr ?_ Iff.rfl) e m) e
  exact finishCpAsyncArrive_present_old (m := m) (rec := rec) (no_arriveOn_record ho hn hr)

theorem finishCpAsyncArrive_not_witness (ho : ObjectsOk X) (hn : X.async.arrived i = false)
    (hid : rec.id = .async i .arriveOn) (w : EvId) :
    ¬ Witness L (X.finishCpAsyncArrive i m rec) (.async i .arriveOn) w := by
  refine not_witness_of_needRef (finishCpAsyncArrive_needs ho hn hid w) ?_
  rintro (⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨m, r, hr, h⟩)
  · cases h
  · cases h
    rcases groupWaitStages_cases X _ k hq with h | h | h | h <;> cases h
  · exact no_arriveOn_record ho hn hr h.symm

theorem finishCpAsyncArrive_no_before (ho : ObjectsOk X) (hn : X.async.arrived i = false)
    {loc : Loc} {f : Ref} :
    ¬ Before ((X.finishCpAsyncArrive i m rec).objects loc) (.async i .arriveOn) f := by
  rintro ⟨a, b, ra, rb, ha, hid, hb, _, hab⟩
  by_cases hm : loc = m
  · subst loc
    have hb' : (X.objects m ++ [rec])[b]? = some rb := by
      simpa [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived, Execution.appendObject]
        using hb
    have hbl := (List.getElem?_eq_some_iff.mp hb').1
    have hao : a < (X.objects m).length := by
      simp only [List.length_append, List.length_singleton] at hbl
      omega
    have ha' : (X.objects m)[a]? = some ra := by
      simpa only [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived,
        Execution.appendObject, ↓reduceIte, List.getElem?_append_left hao] using ha
    exact no_arriveOn_record ho hn (List.mem_of_getElem? ha') hid
  · have ha' : (X.objects loc)[a]? = some ra := by
      simpa [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived,
        Execution.appendObject, hm] using ha
    exact no_arriveOn_record ho hn (List.mem_of_getElem? ha') hid

theorem finishCpAsyncArrive_waits_from_arriveOn
    (ho : ObjectsOk X) (hn : X.async.arrived i = false) (hid : rec.id = .async i .arriveOn)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.finishCpAsyncArrive i m rec) (.async i .arriveOn, b) v) :
    v.1 = .async i .arriveOn ∧ b = false ∧ v.2 = true := by
  rcases h with ⟨he, hb, hb', _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, ha⟩ | ⟨_, _, loc, ho'⟩ | ⟨j, k, he, _⟩ | ⟨_, _, w, -, hw⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨_, _, hi⟩
  · exact ⟨he.symm, hb, hb'⟩
  all_goals try cases he
  · exfalso
    rcases ha with ⟨-, h0, -⟩ | ⟨-, -, ha⟩
    · simp_all
    · cases hv : v.1 with
      | thread j => rw [hv] at ha; exact ha
      | async j p => rw [hv] at ha; cases p <;> exact ha
  · exact (finishCpAsyncArrive_no_before ho hn ho').elim
  · exact (finishCpAsyncArrive_not_witness ho hn hid w hw).elim
  · obtain ⟨_, _, k, q, he, _⟩ := hi
    cases he

/-- The stages that a group wait waits for are not arrive-on stages, so their presence is
unchanged. -/
theorem finishCpAsyncArrive_groupPresent (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages (X.finishCpAsyncArrive i m rec) j k,
        (X.finishCpAsyncArrive i m rec).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl <;> exact Iff.rfl

theorem finishCpAsyncArrive_asyncFinished_iff (ho : ObjectsOk X)
    (hn : X.async.arrived i = false) (hid : rec.id = .async i .arriveOn)
    {j w : EvId} {p : Part} :
    AsyncFinished L (X.finishCpAsyncArrive i m rec) j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      finishCpAsyncArrive_groupPresent j k)
    (exists_congr fun _ => and_congr_left' (finishCpAsyncArrive_asyncObserved_iff ho hn hid))

theorem finishCpAsyncArrive_asyncOnlyFinished_iff {j w : EvId} {p : Part} :
    AsyncOnlyFinished (X.finishCpAsyncArrive i m rec) j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ => finishCpAsyncArrive_groupPresent j _

theorem finishCpAsyncArrive_asyncBefore_iff (ho : ObjectsOk X)
    (hn : X.async.arrived i = false) (hid : rec.id = .async i .arriveOn)
    {l : Loc} {a b : EvId × Part} :
    AsyncBefore L (X.finishCpAsyncArrive i m rec) l a b ↔ AsyncBefore L X l a b := by
  exact AsyncBefore.congr (L:=L) (X:=X.finishCpAsyncArrive i m rec) (Y:=X)
    (fun _ _ => Iff.rfl)
    (fun _ _ _ => finishCpAsyncArrive_asyncFinished_iff ho hn hid)
    (fun _ _ _ => finishCpAsyncArrive_asyncOnlyFinished_iff)
    (fun _ _ _ _ => finishCpAsyncArrive_baseCausality_iff hid)
    (fun _ _ _ _ => Iff.rfl)

theorem finishCpAsyncArrive_asyncPresent_on_edge {l : Loc} {a b : EvId × Part}
    (hedge : AsyncBefore L (X.finishCpAsyncArrive i m rec) l a b) :
    (X.finishCpAsyncArrive i m rec).AsyncPresent a.1 a.2 ↔ X.AsyncPresent a.1 a.2 := by
  rcases a with ⟨j,p⟩
  cases p <;> try rfl
  case arriveOn =>
    obtain ⟨acc,w,hi,_⟩ := hedge.1
    cases hi.2

theorem finishCpAsyncArrive_modelCausality_iff (ho : ObjectsOk X)
    (hn : X.async.arrived i = false) (hid : rec.id = .async i .arriveOn)
    {l : Loc} {e f : Ref} :
    modelCausality L (X.finishCpAsyncArrive i m rec) l e f ↔ modelCausality L X l e f := by
  have hp : ∀ e j, ProxyBefore L (X.finishCpAsyncArrive i m rec) e j l ↔
      ProxyBefore L X e j l := by
    intro e j
    unfold ProxyBefore
    simp only [finishCpAsyncArrive_baseCausality_iff hid]
    rfl
  cases e with
  | thread e =>
    cases f with
    | thread f =>
      exact or_congr (finishCpAsyncArrive_baseCausality_iff hid)
        (Tmem.Pair.AllocResultBefore.iff_of_tr rfl)
    | async j p =>
      simp only [modelCausality, hp, finishCpAsyncArrive_baseCausality_iff hid]
      rfl
  | async j p =>
    cases f with
    | thread f =>
      have hCompletion (w : EvId) :
          ObservedCompletionBefore L (X.finishCpAsyncArrive i m rec) l j p w f ↔
            ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr (X := X) (Y := (X.finishCpAsyncArrive i m rec))
          rfl rfl (finishCpAsyncArrive_baseCausality_iff hid) (hp w f)
      simp only [modelCausality, finishCpAsyncArrive_asyncFinished_iff ho hn hid, hCompletion]
      rfl
    | async k q =>
      exact and_congr_right fun _ =>
        AsyncChain.congr_on_edges (fun _ _ => finishCpAsyncArrive_asyncBefore_iff ho hn hid)
          (fun _ _ => finishCpAsyncArrive_asyncPresent_on_edge)

theorem finishCpAsyncArrive_mbarExec_iff (hid : rec.id = .async i .arriveOn) {x w : EvId} :
    MbarExec L (X.finishCpAsyncArrive i m rec) x w ↔ MbarExec L X x w := by
  change MbarExec L ((X.markCpAsyncArrived i).appendObject m rec) x w ↔ _
  unfold MbarExec
  simp only [appendObject_waitObserves_iff (r := rec) (w := w) (by rw [hid]; simp)]
  rfl


/-- The appended arrive-on record waits on nothing and has no successor in its object;
outside it every order relation is old. -/
theorem finishCpAsyncArrive_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : X.async.arrived i = false)
    (hid : rec.id = .async i .arriveOn) :
    SinkFrame L K A X (X.finishCpAsyncArrive i m rec)
      (CompletionNodes L (X.finishCpAsyncArrive i m rec) (· = .async i .arriveOn)) := by
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hnot : ∀ {w : Ref}, ¬ w = .async i .arriveOn → rec.id ≠ w := fun hw he =>
    hw (he.symm.trans hid)
  have hth : ∀ e, rec.id ≠ .thread e := fun e h => by rw [hid] at h; cases h
  have hpres : ∀ {e : Ref}, e ≠ .async i .arriveOn →
      (X.finishCpAsyncArrive i m rec).RefPresent e → X.RefPresent e :=
    fun he h => (finishCpAsyncArrive_present_old he).mp h
  have hold : ∀ {u : Ref × Bool}, ¬ CompletionNodes L (X.finishCpAsyncArrive i m rec)
      (· = .async i .arriveOn) u → u.1 ≠ .async i .arriveOn :=
    fun hu he => hu (.inl he)
  have hobject : ∀ o (u v : Ref × Bool), v.1 ≠ .async i .arriveOn →
      ObjectOrder L (X.finishCpAsyncArrive i m rec) o u v → ObjectOrder L X o u v :=
    fun o u v hv h => (appendObject_objectOrder_iff (X := X.markCpAsyncArrived i) (hnot hv)).mp h
  refine sinkFrame_completion (· = .async i .arriveOn) (fun _ h => by cases h)
    (fun u v hu h => ?_)
    (fun w x hx hw => (finishCpAsyncArrive_not_witness ho hn hid w (hx ▸ hw)).elim)
    (fun u v hu hv hc => ?_) (fun x w hx hw h => ?_)
    (fun o u v _ hv h => hobject o u v (hold hv) h) (fun o u v _ hv h => ?_)
    (fun u v hu hv hc => ?_) (fun m j p y hb => ?_) (fun m j p y _ _ h => ?_) hX.initFence
    (fun _ _ _ h => h) (fun m y init h => ?_) (fun _ => rfl)
  · obtain ⟨e, b⟩ := u
    change e = _ at hu
    subst hu
    obtain ⟨h1, h2, h3⟩ := finishCpAsyncArrive_waits_from_arriveOn ho hn hid h
    exact .inl ⟨h1, h2, h3⟩
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | ⟨h1, h2, j, k, h3, h4, hc⟩ | ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, h7, h8⟩
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.finishCpAsyncArrive i m rec)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl ⟨h1, h2, j, k, h3, h4,
        (finishCpAsyncArrive_baseCausality_iff hid).mp hc⟩))
    · exact .single (.inr (.inr ⟨h1, h2, k, h3, c, p, w, ws, h5, h6,
        (finishCpAsyncArrive_asyncObserved_iff ho hn hid).mp h7, h8⟩))
  · have hx' : x ≠ .async i .arriveOn := hold hx
    have hw' : w ≠ .async i .arriveOn := hold hw
    rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · have h' := (appendObject_mbarObserved_iff (X := X.markCpAsyncArrived i) (hnot hx')
        (hnot hw')).mp hm
      exact .inl ⟨⟨hpres hx' h'.1, h'.2⟩, rest⟩
    · exact .inr ⟨j, p, k, q, rfl, h2, hpres hx' h3, h4, h5⟩
  · cases o with
    | mbar loc => exact ⟨hobject _ u v (hold hv) h.1, h.2⟩
    | ctaBar c id => exact hobject (.ctaBar c id) u v (hold hv) h
    | cluster c => exact hobject (.cluster c) u v (hold hv) h
    | tmem c => exact hobject (.tmem c) u v (hold hv) h
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | hc | ⟨h1, h2, j, hj, fills, hn', hx, hf⟩ | hc
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.finishCpAsyncArrive i m rec)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl (IssueStage.transfer (X := X)
        (Y := X.finishCpAsyncArrive i m rec) (fun _ => rfl) (hpres (hold hv)) hc)))
    · rw [finishCpAsyncArrive_needs ho hn hid] at hn'
      exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, fills, hn', hpres (hold hu) hx, hf⟩)))
    · exact .single (.inr (.inr (.inr hc)))
  · by_cases hy : rec.id = y
    · rintro ⟨k, rfl, -⟩
      exact hth k hy
    · have hb' := (appendObject_objectOrder_iff (X := X.markCpAsyncArrived i) (L := L)
        (o := .mbar m) (u := (.async j p, true)) (v := (y, true)) hy).mp ⟨rfl, rfl, hb⟩
      exact (hX.asyncObject m j p y hb'.2.2).1
  · rcases h with h | ⟨k, ws, rfl, hw⟩
    · exact .inl h
    · exact .inr ⟨k, ws, rfl, (appendObject_waitObserves_iff (hth k)).mp hw⟩
  · have hb' := (appendObject_objectOrder_iff (X := X.markCpAsyncArrived i) (L := L)
      (o := .mbar m) (u := (y, true)) (v := (.thread init, true)) (hth init)).mp ⟨rfl, rfl, h⟩
    exact hb'.2.2


theorem finishCpAsyncArrive_memReads {e : Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.finishCpAsyncArrive i m rec).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p => cases p <;> rfl

theorem finishCpAsyncArrive_memWrites {e : Ref} {a : Acc} {bs : List Byte} :
    (X.finishCpAsyncArrive i m rec).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p => cases p <;> rfl

/-- A notification adds no evidence about loads already in the execution. -/
theorem finishCpAsyncArrive_readOk {A : List Assumption} (ho : ObjectsOk X)
    (hr : TcMma.ReadOk L A X) (hte : AsyncCopy.TcEffectsOk X) (hn : X.async.arrived i = false)
    (hid : rec.id = .async i .arriveOn) :
    TcMma.ReadOk L A (X.finishCpAsyncArrive i m rec) := by
  refine (TcMma.ReadPreserved.readOk ⟨Execution.le_finishCpAsyncArrive,
    fun _ => finishCpAsyncArrive_baseCausality_iff hid,
    fun _ => finishCpAsyncArrive_asyncObserved_iff ho hn
        hid,
    fun _ _ h => h, fun _ _ hr => .inl hr, fun _ => finishCpAsyncArrive_mbarExec_iff hid,
    fun _ hq => .inl hq⟩ hr hte) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
  have := len_of_get (X := X) hl
  omega

theorem consistent_finishCpAsyncArrive {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hi : X.AsyncArrive i m true)
    (hn : X.async.arrived i = false)
    (hw : ∀ j, TracksCpAsync X j i → (X.async.copies j).writeBytes.isSome)
    (hid : rec.id = .async i .arriveOn) (ha : rec.action = .arrive 1 0)
    (hc : CheckedLog (X.objects m ++ [rec]))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.finishCpAsyncArrive i m rec)) :
    Consistent L K A mem0 (X.finishCpAsyncArrive i m rec) := by
  have hfr := finishCpAsyncArrive_sinkFrame (m := m) hX hn hid
  have horder := hfr.orderOk hX.orderOk
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hdep : DependencyOk L K (X.finishCpAsyncArrive i m rec) := by
    refine ⟨?_, horder.depAcyclic⟩
    intro e hret n hn'
    rw [finishCpAsyncArrive_needs ho hn hid] at hn'
    have hready := hX.dependency.ready e hret n hn'
    cases n with
    | cond holds => exact hready
    | node fills =>
      obtain ⟨x, hx, hf⟩ := hready
      have hne : x ≠ .async i .arriveOn := by
        rintro rfl
        rcases needs_node_cases hn' hf with ⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨m, r, hr, h⟩
        · cases h
        · cases h
          rcases groupWaitStages_cases X _ k hq with h | h | h | h <;> cases h
        · exact no_arriveOn_record ho hn hr h.symm
      exact ⟨x, (finishCpAsyncArrive_present_old hne).mpr hx, hf⟩
  have reflect {l e f} :
      ByteCausality L (X.finishCpAsyncArrive i m rec) l e f → ByteCausality L X l e f :=
    ByteCausality.of_same_context (X := X) (Y := X.finishCpAsyncArrive i m rec) rfl rfl
      (fun h => (finishCpAsyncArrive_modelCausality_iff hX.tma.2.2.1 hn hid).mp h)
      (fun h => (finishCpAsyncArrive_asyncObserved_iff hX.tma.2.2.1 hn hid).mp h)
  refine {
    thr := hX.thr, outside := hX.outside, ctaBar := hX.ctaBar, shfl := hX.shfl,
    cluster := hX.cluster, elect := hX.elect, vote := hX.vote, warpValue := hX.warpValue,
    warpBar := hX.warpBar, matrix := hX.matrix,
    clc := hX.clc, tensor := hX.tensor, store := hX.store,
    tmemPair := hX.tmemPair, tmemPairResult := hX.tmemPairResult,
    tcCommit := hX.tcCommit,
    tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion,
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl,
    tcRead := finishCpAsyncArrive_readOk ho hX.tcRead hX.tma.2.1 hn hid,
    reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩,
    atomic := atomicOk_congr (X := X) (Y := X.finishCpAsyncArrive i m rec)
      (fun p l n => by cases p <;> exact Iff.rfl) (fun _ _ => rmwStrong_congr rfl rfl)
      (fun p k => by cases p <;> rfl) hX.atomic,
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs h =>
      hX.fenceSc.causal e f hs ((finishCpAsyncArrive_baseCausality_iff hid).mp h)⟩,
    dependency := hdep,
    observation := horder.observation, object := horder.object,
    asyncObject := horder.asyncObject, initFence := horder.initFence,
    asm := hasm, rf := ?_, noFuture := ?_, hidden := ?_, tma := ?_ }
  · intro e a bs hr
    obtain ⟨hlen, hv⟩ := hX.rf e a bs (finishCpAsyncArrive_memReads.mp hr)
    refine ⟨hlen, fun k hk => ?_⟩
    have hh := hv k hk
    cases hs : X.rf e k with
    | none =>
      rw [show (X.finishCpAsyncArrive i m rec).rf e k = X.rf e k from rfl, hs]
      simp only [hs] at hh
      exact hh
    | some w =>
      rw [show (X.finishCpAsyncArrive i m rec).rf e k = X.rf e k from rfl, hs]
      rw [hs] at hh
      obtain ⟨target, bytes, hw, hcover, hbytes⟩ := hh
      exact ⟨target, bytes, finishCpAsyncArrive_memWrites.mpr hw, hcover, hbytes⟩
  · intro e a bs k w hr hk hs hv
    exact hX.noFuture e a bs k w (finishCpAsyncArrive_memReads.mp hr) hk hs
      (reflect hv)
  · intro e a bs k w target bytes hr hk hw hc hv
    have hh := hX.hidden e a bs k w target bytes (finishCpAsyncArrive_memReads.mp hr) hk
      (finishCpAsyncArrive_memWrites.mp hw) hc
          (reflect hv)
    cases hs : X.rf e k with
    | none => simp only [hs] at hh
    | some v =>
      rw [show (X.finishCpAsyncArrive i m rec).rf e k = X.rf e k from rfl, hs]
      rw [hs] at hh
      exact fun h => hh (reflect h)
  · exact finishCpAsyncArrive_tmaOk hX.tma hi hn hw hid ha hc


/-- Perform a pending no-increment arrive-on as its own counted, consistent extension. -/
theorem pending_cpAsyncArrive_extendsInOrder {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (hi : X.AsyncArrive i m true) (hn : X.async.arrived i = false)
    (hw : ∀ j, TracksCpAsync X j i → (X.async.copies j).writeBytes.isSome) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have ho := hX.tma.2.2.1
  obtain ⟨last, hh⟩ := (ho m).1.2
  let r := Step.checkedRecord (.async i .arriveOn) (.arrive 1 0) last
  have hid : r.id = .async i .arriveOn := Step.checkedRecord_id ..
  have ha : r.action = .arrive 1 0 := Step.checkedRecord_action ..
  have hc : CheckedLog (X.objects m ++ [r]) := by
    apply CheckedLog.snoc hh (ho m).1.1
    · intro hmem
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
      exact no_arriveOn_record ho hn hq (hqe.trans hid)
    · exact Step.checkedRecord_ok ..
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hg, hidx⟩ := issuer_thread hX he
  have hle : X.le (X.finishCpAsyncArrive i m r) := Execution.le_finishCpAsyncArrive
  refine ⟨_, consistent_finishCpAsyncArrive hX ⟨pc, he⟩ hn hw hid ha hc
    (hA _ _ hX hle (Execution.notifiedInOrder_of_eq rfl) (Execution.noNewRead_of_tr rfl)), hle,
    ?_⟩
  apply Execution.size_lt_of_asyncSize_lt Execution.le_finishCpAsyncArrive rfl hg hidx
  have hsize : (X.finishCpAsyncArrive i m r).elemSize i = X.elemSize i := rfl
  unfold Execution.asyncSize
  rw [hsize]
  cases hm : X.async.mmaOperands i <;>
    simp [Execution.finishCpAsyncArrive, Execution.appendObject, Execution.markCpAsyncArrived,
      Snapshot.mmaStarted, hn, hm, Nat.add_assoc]


/-- Perform an arrive-on when the assumptions impose no execution constraints. -/
theorem pending_cpAsyncArrive_extends {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hi : X.AsyncArrive i m true) (hn : X.async.arrived i = false)
    (hw : ∀ j, TracksCpAsync X j i → (X.async.copies j).writeBytes.isSome) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  pending_cpAsyncArrive_extendsInOrder (sel := fun _ => false) (fun _ Y _ _ _ _ a h => hA a h Y)
    hX hi hn hw

/-- A maximal execution records the arrive-on once all tracked destinations have been written. -/
theorem Maximal.cpAsync_arrived {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hA : Assumption.WfFree L mem0 A) (hX : Maximal L K A mem0 X)
    (hi : X.AsyncArrive i m true)
    (hw : ∀ j, TracksCpAsync X j i → (X.async.copies j).writeBytes.isSome) :
    X.async.arrived i = true := by
  cases hn : X.async.arrived i with
  | false => exact (hX.not_grows (pending_cpAsyncArrive_extends hA hX.1 hi hn hw)).elim
  | true => rfl

namespace Step

/-- Issue a no-increment arrival without appending an object update at issue. -/
theorem cpAsyncArrive_issue_extends {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {g pc : Nat} (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X)
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨pc, .asyncArrive m true⟩ o)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .asyncArrive m true⟩ (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g ⟨pc, .asyncArrive m true⟩ (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  snoc_counted_extension_reads hX hord hg hrel hrun hl he
    (Kind.WaitFree.mk trivial (fun _ h => by cases h))
    nofun nofun rfl rfl nofun nofun nofun nofun nofun rfl
    (hX.tmaOk_snoc_unobserved (fun _ h => by cases h)
      (objectAction_snoc_new (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)))
    (.snoc_frame_of hX nofun nofun nofun (ClcOk.snoc hX.clc (.inl hne) nofun)
      (hX.tmemPairResult.snoc_not_wr nofun)
      (hX.tcRead_snoc nofun nofun nofun nofun nofun)
      (hX.atomic.snoc hX.store hX.tma.1 nofun)
      (hX.fenceSc_snoc nofun nofun nofun nofun)
      (hX.matrix.snoc rfl) (TensorStore.ReduceOk.snoc_issue hX))
    hasm hsg

end Step

end

end PTX
