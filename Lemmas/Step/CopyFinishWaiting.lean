-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CopyFinishVisibility
public import Lemmas.Order.WaitingClosure
public import Lemmas.Order.NeedFills

@[expose] public section

/-! A copy completion adds a terminal chain of read, write and notification stages. The copy
completes through an mbarrier and writes its destination as one whole, so no wait other than one
recorded after the notification can depend on these stages, and outside them every order relation
of the completed execution is one of the execution before it (`finishCopyRecord_sinkFrame`). -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

private theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

variable {L : Launch} {X : Execution} {i : EvId} {bs : List Byte} {src : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}

def CopyPart (p : Part) : Prop := p = .read .copy ∨ p = .write .copy ∨ p = .notify .copy

def CopyRef (i : EvId) (e : Ref) : Prop := ∃ p, e = .async i p ∧ CopyPart p

def copyStageRank : Part → Nat
  | .read .copy => 0
  | .write .copy => 1
  | .notify .copy => 2
  | _ => 0

def copyNodeRank (p : Part) (b : Bool) : Nat := 2 * copyStageRank p + if b then 1 else 0

theorem unnotified_no_copy_record (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) {p : Part} (hp : CopyPart p)
    {loc : Loc} {r : Record Ref} (hr : r ∈ X.objects loc) : r.id ≠ .async i p := by
  rcases hp with rfl | rfl | rfl
  · intro he
    have hh := ((ho loc).2.1 r hr).1
    simp [he, objectAction] at hh
  · intro he
    have hh := ((ho loc).2.1 r hr).1
    simp [he, objectAction] at hh
  · exact no_copy_notification_record ho hn hr

theorem finishCopyRecord_no_copy_before (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) {p : Part} (hp : CopyPart p)
    {loc : Loc} {f : Ref} :
    ¬ Before ((X.finishCopyRecord i bs src mb rec).objects loc) (.async i p) f := by
  rintro ⟨a, b, ra, rb, ha, hid, hb, _, hab⟩
  by_cases hm : loc = mb
  · subst loc
    have hb' : (X.objects mb ++ [rec])[b]? = some rb := by
      simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy] using hb
    have hbl := (List.getElem?_eq_some_iff.mp hb').1
    have hao : a < (X.objects mb).length := by
      simp only [List.length_append, List.length_singleton] at hbl
      omega
    have ha' : (X.objects mb)[a]? = some ra := by
      simpa only [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy,
        ↓reduceIte, List.getElem?_append_left hao] using ha
    exact unnotified_no_copy_record ho hn hp (List.mem_of_getElem? ha') hid
  · have ha' : (X.objects loc)[a]? = some ra := by
      simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, hm] using ha
    exact unnotified_no_copy_record ho hn hp (List.mem_of_getElem? ha') hid

theorem finishCopyRecord_present_old {e : Ref} (he : ¬ CopyRef i e) :
    (X.finishCopyRecord i bs src mb rec).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hj : j = i
    · subst j
      cases p <;> try rfl
      all_goals first
        | (simp [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCopyRecord,
            Execution.appendObject, Execution.finishCopy]; done)
        | exact (he ⟨_, rfl, by simp [CopyPart]⟩).elim
    · cases p <;> simp only [Execution.RefPresent, Execution.AsyncPresent,
        Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, ite_eq_right hj]
      all_goals rfl

/-- The appended notification is the last record of its history, so the order of a history up to
an old operation is the order before the completion. -/
theorem finishCopyRecord_before_old {m : Loc} {u w : Ref} (hw : rec.id ≠ w) :
    MBarrier.Before ((X.finishCopyRecord i bs src mb rec).objects m) u w ↔
      MBarrier.Before (X.objects m) u w := by
  by_cases hm : m = mb
  · subst m
    rw [show (X.finishCopyRecord i bs src mb rec).objects mb = X.objects mb ++ [rec] by
      simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy]]
    exact Before.snoc_iff hw
  · simp only [Execution.finishCopyRecord, Execution.appendObject, ite_eq_right hm]
    rfl

theorem finishCopyRecord_mbarObserved_old (hid : rec.id = .async i (.notify .copy)) {x w : Ref}
    (hx : ¬ CopyRef i x) (hw : ¬ CopyRef i w) :
    MbarObserved (X.finishCopyRecord i bs src mb rec) x w ↔ MbarObserved X x w := by
  have hnot : ∀ {y : Ref}, ¬ CopyRef i y → rec.id ≠ y := fun hy he =>
    hy ⟨.notify .copy, he.symm.trans hid, Or.inr (Or.inr rfl)⟩
  change MbarObserved ((X.finishCopy i bs src).appendObject mb rec) x w ↔ _
  rw [appendObject_mbarObserved_iff (hnot hx) (hnot hw)]
  unfold MbarObserved
  exact and_congr (finishCopyRecord_present_old (bs := bs) (src := src) (mb := mb) (rec := rec) hx)
    Iff.rfl

/-- The poll needs are those before the completion: the appended notification belongs to no phase
that an earlier poll observed. -/
theorem finishCopyRecord_pollNeeds (ho : ObjectsOk X) (hn : (X.async.copies i).notified = false)
    (hid : rec.id = .async i (.notify .copy)) (e : EvId) (m : Loc) :
    pollNeeds (X.finishCopyRecord i bs src mb rec) e m = pollNeeds X e m := by
  have hobs : ∀ r ∈ X.objects m, MbarObserved (X.finishCopyRecord i bs src mb rec) r.id
      (.thread e) ↔ MbarObserved X r.id (.thread e) := fun r hr =>
    finishCopyRecord_mbarObserved_old hid
      (fun ⟨_, he, hp⟩ => unnotified_no_copy_record ho hn hp hr he)
      (fun ⟨_, he, _⟩ => by cases he)
  have hrec : ¬ MbarObserved (X.finishCopyRecord i bs src mb rec) rec.id (.thread e) := by
    rintro ⟨-, j, m', acq, ws, hj, hw, -⟩
    cases hj
    rw [hid, finishCopyRecord_waitObserves_iff hid] at hw
    obtain ⟨-, k, l, r, waiter, phase, hk, hrid, -⟩ := hw
    exact no_copy_notification_record ho hn (List.mem_of_getElem? hk) hrid
  unfold pollNeeds
  by_cases hm : m = mb
  · subst m
    have hobj : (X.finishCopyRecord i bs src mb rec).objects mb = X.objects mb ++ [rec] := by
      simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy]
    have hr : needsIf (MbarObserved (X.finishCopyRecord i bs src mb rec) rec.id (.thread e))
        [Need.node (· = rec.id)] = [] := by simp [needsIf, hrec]
    rw [hobj, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, hr, List.append_nil]
    exact flatMap_congr_mem fun r hr => @if_congr _ _ _ (Classical.propDecidable _)
      (Classical.propDecidable _) _ _ _ _ (hobs r hr) rfl rfl
  · have hobj : (X.finishCopyRecord i bs src mb rec).objects m = X.objects m := by
      simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, hm]
    rw [hobj]
    exact flatMap_congr_mem fun r hr => @if_congr _ _ _ (Classical.propDecidable _)
      (Classical.propDecidable _) _ _ _ _ (hobs r hr) rfl rfl

/-- The completion changes the needs of no event. -/
theorem finishCopyRecord_needs (ho : ObjectsOk X) (hn : (X.async.copies i).notified = false)
    (hid : rec.id = .async i (.notify .copy)) (e : EvId) :
    Needs L (X.finishCopyRecord i bs src mb rec) e = Needs L X e := by
  unfold Needs
  change (match X.get e with
    | none => []
    | some ev => KindNeeds L (X.finishCopyRecord i bs src mb rec) ev.kind e) = _
  cases X.get e with
  | none => rfl
  | some ev =>
    simp only
    cases ev.kind
    all_goals try rfl
    all_goals try (cases ‹TcKind› <;> rfl)
    simp only [KindNeeds, finishCopyRecord_pollNeeds ho hn hid]

theorem finishCopyRecord_witness_old (ho : ObjectsOk X) (hn : (X.async.copies i).notified = false)
    (hid : rec.id = .async i (.notify .copy)) {x : Ref} (hx : ¬ CopyRef i x) {e : EvId} :
    Witness L (X.finishCopyRecord i bs src mb rec) x e ↔ Witness L X x e := by
  unfold Witness
  rw [finishCopyRecord_needs ho hn hid]
  simp only [finishCopyRecord_present_old hx]

/-- No need is filled by a stage of a copy completed through an mbarrier before its
notification. -/
theorem finishCopyRecord_no_copy_witness (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {s : Spec} {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m) {p : Part}
    (hp : CopyPart p) {e : EvId} :
    ¬ Witness L (X.finishCopyRecord i bs src mb rec) (.async i p) e := by
  rintro ⟨fills, hneed, -, hf⟩
  rw [finishCopyRecord_needs ho hn hid] at hneed
  rcases needs_node_fills hneed hf with ⟨t, ht⟩ | ⟨m', r, hr, hrid⟩ | ⟨k, j, q, hw, hjq⟩
  · cases ht
  · exact unnotified_no_copy_record ho hn hp hr hrid.symm
  · cases hjq
    exact not_groupWaitsFor_of_mbarrier hc hm k e hw

theorem finishCopyRecord_tracksMma :
    TracksMma (X.finishCopyRecord i bs src mb rec) = TracksMma X := rfl

theorem finishCopyRecord_tracksCpAsync :
    TracksCpAsync (X.finishCopyRecord i bs src mb rec) = TracksCpAsync X := rfl

theorem finishCopyRecord_stageEdge_old {e f : Ref} (he : ¬ CopyRef i e) (hf : ¬ CopyRef i f)
    (h : StageEdge (X.finishCopyRecord i bs src mb rec) e f) : StageEdge X e f := by
  have hp : ∀ j p, ¬ CopyRef i (.async j p) →
      ((X.finishCopyRecord i bs src mb rec).AsyncPresent j p ↔ X.AsyncPresent j p) :=
    fun _ _ h => finishCopyRecord_present_old h
  unfold StageEdge at h
  split at h
  all_goals first
    | exact h.elim
    | (simp only [StageEdge]
       simpa only [hp _ _ he, hp _ _ hf, finishCopyRecord_tracksMma,
         finishCopyRecord_tracksCpAsync] using h)

theorem finishCopyRecord_stageOrder_old {u v : Ref × Bool} (hu : ¬ CopyRef i u.1)
    (hv : ¬ CopyRef i v.1) (h : StageOrder (X.finishCopyRecord i bs src mb rec) u v) :
    StageOrder X u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  rcases h with ⟨rfl, rfl, rfl, hp⟩ | ⟨rfl, rfl, h⟩
  · exact .inl ⟨rfl, rfl, rfl, (finishCopyRecord_present_old hu).mp hp⟩
  · exact .inr ⟨rfl, rfl, finishCopyRecord_stageEdge_old hu hv h⟩

theorem finishCopyRecord_depStep_old {K : Kernel} (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {u v : Ref × Bool} (hu : ¬ CopyRef i u.1) (hv : ¬ CopyRef i v.1)
    (h : DepStep L K (X.finishCopyRecord i bs src mb rec) u v) : DepStep L K X u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  rcases h with h | h | ⟨rfl, rfl, j, rfl, hw⟩ | ⟨rfl, rfl, w, j, rfl, rfl, hr⟩
  · exact .inl (finishCopyRecord_stageOrder_old hu hv h)
  · obtain ⟨hb, hb', j, p, rfl, rfl, hr, hp, hk⟩ := h
    exact .inr (.inl ⟨hb, hb', j, p, rfl, rfl, hr, (finishCopyRecord_present_old hv).mp hp, hk⟩)
  · exact .inr (.inr (.inl ⟨rfl, rfl, j, rfl, (finishCopyRecord_witness_old ho hn hid hu).mp hw⟩))
  · exact .inr (.inr (.inr ⟨rfl, rfl, w, j, rfl, rfl, hr⟩))

theorem finishCopyRecord_stageCausality_old (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {u v : Ref × Bool} (hu : ¬ CopyRef i u.1) (hv : ¬ CopyRef i v.1)
    (h : stageCausality L (X.finishCopyRecord i bs src mb rec) u v) : stageCausality L X u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  rcases h with h | ⟨rfl, rfl, a, c, rfl, rfl, hb⟩ | ⟨rfl, rfl, j, rfl, hs⟩
  · exact .inl (finishCopyRecord_stageOrder_old hu hv h)
  · exact .inr (.inl ⟨rfl, rfl, a, c, rfl, rfl, (finishCopyRecord_baseCausality_iff hid).mp hb⟩)
  · obtain ⟨j', p, w, ws, rfl, hp, hobs, hsc, hpo⟩ := hs
    exact .inr (.inr ⟨rfl, rfl, j, rfl, j', p, w, ws, rfl, hp,
      (finishCopyRecord_asyncObserved_iff ho hn hid).mp hobs, hsc, hpo⟩)

theorem finishCopyRecord_syncObserved_old (hid : rec.id = .async i (.notify .copy)) {x w : Ref}
    (hx : ¬ CopyRef i x) (hw : ¬ CopyRef i w)
    (h : SyncObserved L (X.finishCopyRecord i bs src mb rec) x w) : SyncObserved L X x w := by
  rcases h with ⟨hmo, rest⟩ | ⟨j, p, k, g, rfl, rfl, hp, hg, hs⟩
  · exact .inl ⟨(finishCopyRecord_mbarObserved_old hid hx hw).mp hmo, rest⟩
  · exact .inr ⟨j, p, k, g, rfl, rfl, (finishCopyRecord_present_old hx).mp hp, hg, hs⟩

/-- A stage edge leaving a stage of copy `i` enters a later stage of copy `i`: the copy has no
element stage, and it has no arrive-on because it completes through an mbarrier. -/
theorem finishCopyRecord_copy_stageEdge {s : Spec} {m : Loc} (hc : X.Copy i s)
    (hm : s.completion = .mbarrier m) (hel : ∀ k, (X.async.copies i).elemWrites k = none)
    {p : Part} (hp : CopyPart p) {f : Ref}
    (h : StageEdge (X.finishCopyRecord i bs src mb rec) (.async i p) f) :
    ∃ q, f = .async i q ∧ CopyPart q ∧ copyStageRank p < copyStageRank q := by
  have helY : ∀ k, ¬ (X.finishCopyRecord i bs src mb rec).AsyncPresent i (.write (.elem k)) := by
    intro k
    simp [Execution.AsyncPresent, Execution.finishCopyRecord, Execution.appendObject,
      Execution.finishCopy, hel k]
  rcases hp with rfl | rfl | rfl <;> unfold StageEdge at h <;> split at h
  all_goals try (rename_i heq; cases heq)
  all_goals first
    | exact h.elim
    | (obtain ⟨rfl, hk⟩ := h; exact (helY _ hk.2).elim)
    | (obtain ⟨rfl, rfl, -⟩ := h
       exact ⟨_, rfl, by simp [CopyPart], by simp [copyStageRank]⟩)
    | (obtain ⟨rfl, ht, -⟩ := h
       obtain rfl : _ = Target.copy := by simpa [AsyncCopy.Part.target] using ht.symm
       exact ⟨_, rfl, by simp [CopyPart], by simp [copyStageRank]⟩)
    | (obtain ⟨⟨-, -, ⟨s', hc', hs'⟩, -⟩, -⟩ := h
       rw [Execution.Copy.unique (X := X) hc' hc, hm] at hs'
       cases hs')

theorem finishCopyRecord_waits_from_copy (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {s : Spec} {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m)
    (hel : ∀ k, (X.async.copies i).elemWrites k = none) {p : Part} (hp : CopyPart p)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.finishCopyRecord i bs src mb rec) (.async i p, b) v) :
    ∃ q c, v = (.async i q, c) ∧ CopyPart q ∧ copyNodeRank p b < copyNodeRank q c := by
  rcases h with ⟨he, hb, hb', _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨hb, hb', hs⟩ | ⟨_, _, loc, ho'⟩ | ⟨j, k, he, _⟩ |
    ⟨_, _, j, hf, hw⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, hi⟩
  · exact ⟨p, true, Prod.ext he.symm hb', hp, by simp [copyNodeRank, hb]⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · rcases hs with ⟨-, hb2, -⟩ | ⟨-, -, hs⟩
    · rw [hb] at hb2; cases hb2
    · obtain ⟨q, hq, hcq, hlt⟩ := finishCopyRecord_copy_stageEdge hc hm hel hp hs
      refine ⟨q, false, Prod.ext hq hb', hcq, ?_⟩
      simp only [copyNodeRank, hb, ↓reduceIte, Bool.false_eq_true]
      omega
  · exact (finishCopyRecord_no_copy_before ho hn hp ho').elim
  · cases he
  · exact (finishCopyRecord_no_copy_witness ho hn hid hc hm hp hw).elim
  · cases he
  · cases he
  · cases he
  · cases he
  · cases he
  · obtain ⟨-, -, j, q, he, -⟩ := hi
    cases he

/-- The rank of a copy node. -/
def copyRank : Ref × Bool → Nat
  | (.async _ p, b) => copyNodeRank p b
  | _ => 0

/-- **Completing a copy is a sink frame.** The new copy stages only lead forward within that copy,
and its appended notification has no successor in the object history. Outside the copy every
order relation is the one before the completion. -/
theorem finishCopyRecord_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {s : Spec} {m : Loc} (hi : issuedBy X i = some s)
    (hm : s.completion = .mbarrier m) (hw : s.writes = .whole)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy)) :
    SinkFrame L K A X (X.finishCopyRecord i bs src mb rec) (fun n => CopyRef i n.1) := by
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hc : X.Copy i s := issuedBy_some.mp hi
  have hel : ∀ k, (X.async.copies i).elemWrites k = none :=
    fun k => (elems_none_of_whole hX.tma.1 hi hw k).1
  have hnot : ∀ {y : Ref}, ¬ CopyRef i y → rec.id ≠ y := fun hy he =>
    hy ⟨.notify .copy, he.symm.trans hid, Or.inr (Or.inr rfl)⟩
  have hthr : ∀ {t : EvId}, ¬ CopyRef i (.thread t) := fun ⟨_, he, _⟩ => by cases he
  have hclosed : ∃ rank : Ref × Bool → Nat, ∀ u v,
      Waits L (X.finishCopyRecord i bs src mb rec) u v → CopyRef i u.1 →
        CopyRef i v.1 ∧ rank u < rank v := by
    refine ⟨copyRank, fun u v h hu => ?_⟩
    obtain ⟨p, he, hp⟩ := hu
    obtain ⟨e, b⟩ := u
    simp only at he
    subst he
    obtain ⟨q, c, rfl, hq, hlt⟩ := finishCopyRecord_waits_from_copy ho hn hid hc hm hel hp h
    exact ⟨⟨q, rfl, hq⟩, hlt⟩
  have hcause : ∀ u v, ¬ CopyRef i u.1 → ¬ CopyRef i v.1 →
      stageCausality L (X.finishCopyRecord i bs src mb rec) u v →
        Relation.TransGen (stageCausality L X) u v :=
    fun _ _ hu hv h => .single (finishCopyRecord_stageCausality_old ho hn hid hu hv h)
  have hobject : ∀ o u v, ¬ CopyRef i u.1 → ¬ CopyRef i v.1 →
      ObjectOrder L (X.finishCopyRecord i bs src mb rec) o u v → ObjectOrder L X o u v :=
    fun _ _ _ _ hv h => (appendObject_objectOrder_iff (X := X.finishCopy i bs src) (hnot hv)).mp h
  obtain ⟨rank, hrank⟩ := hclosed
  exact {
    closed := ⟨rank, hrank⟩
    cause := hcause
    observed := fun _ _ hx hw h => finishCopyRecord_syncObserved_old hid hx hw h
    object := hobject
    objectSync := fun o u v hu hv h => by
      cases o with
      | mbar l => exact ⟨hobject _ u v hu hv h.1, h.2⟩
      | ctaBar c id => exact hobject (.ctaBar c id) u v hu hv h
      | cluster c => exact hobject (.cluster c) u v hu hv h
      | tmem c => exact hobject (.tmem c) u v hu hv h
    dep := fun _ _ hu hv h => .single (finishCopyRecord_depStep_old ho hn hid hu hv h)
    issue := fun _ _ _ _ _ h => (hthr h).elim
    asyncSelf := fun l j p y hb => by
      rintro ⟨t, rfl, h1, h2⟩
      exact (hX.asyncObject l j p _ ((finishCopyRecord_before_old (hnot hthr)).mp hb)).1
        ⟨t, rfl, h1, h2⟩
    asyncObserved := fun l j p y _ _ h => by
      rcases h with h | ⟨t, ws, rfl, hwo⟩
      · exact .inl h
      · exact .inr ⟨t, ws, rfl, (finishCopyRecord_waitObserves_iff hid).mp hwo⟩
    initFence := fun l init w y hsync hpath hbef => by
      obtain ⟨-, hpathX⟩ := SinkFrame.old_path (S := fun n => CopyRef i n.1) hrank
        (fun _ _ h => stageCausality.waits h) hcause hpath hthr
      exact hX.initFence l init w y hsync hpathX ((finishCopyRecord_before_old (hnot hthr)).mp hbef)
    get := fun _ _ => rfl }

end
end PTX
