-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcCompleteConsistentNotifyFrame
public import Lemmas.Order.WaitingClosure

@[expose] public section

/-! A freshly appended CLC notification is terminal in its object history.
The extra node is therefore a sink of the execution order. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {c : Nat} {mb : Loc} {rec : Record Ref}

/-- No old record can name this unnotified effect, and the appended record
cannot be before anything because it is last. -/
theorem notifyClcRecord_no_notify_before (ho : ObjectsOk X)
    (hn : c∉(X.clc i).notified) {loc : Loc} {f : Ref} :
    ¬Before ((X.notifyClcRecord i c mb rec).objects loc) (.async i (.notify (.cta c))) f := by
  rintro ⟨a,b,ra,rb,ha,hid,hb,_,hab⟩
  by_cases hm : loc=mb
  · subst loc
    have hb' : (X.objects mb++[rec])[b]?=some rb := by
      simpa [Execution.notifyClcRecord,Execution.appendObject,Execution.markClcNotify] using hb
    have hbl := (List.getElem?_eq_some_iff.mp hb').1
    have hao : a<(X.objects mb).length := by
      simp only [List.length_append,List.length_singleton] at hbl
      omega
    have ha' : (X.objects mb)[a]?=some ra := by
      simpa only [Execution.notifyClcRecord,Execution.appendObject,Execution.markClcNotify,
        ↓reduceIte,List.getElem?_append_left hao] using ha
    exact no_clc_notification_record ho hn (List.mem_of_getElem? ha') hid
  · have ha' : (X.objects loc)[a]?=some ra := by
      simpa [Execution.notifyClcRecord,Execution.appendObject,Execution.markClcNotify,hm] using ha
    exact no_clc_notification_record ho hn (List.mem_of_getElem? ha') hid

/-- The new notification fills no need: the needs are those of `X`, which it does not fill. -/
theorem notifyClcRecord_not_witness (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) (w : EvId) :
    ¬ Witness L (X.notifyClcRecord i c mb rec) (.async i (.notify (.cta c))) w :=
  not_witness_of_needRef (notifyClcRecord_needs ho hn hid w) (notifyClcRecord_not_needRef ho hn)

theorem notifyClcRecord_waits_from (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.notifyClcRecord i c mb rec) (.async i (.notify (.cta c)),b) v) :
    v.1=.async i (.notify (.cta c)) ∧ b=false ∧ v.2=true := by
  rcases h with ⟨he,hb,hb',_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨_,_,ha⟩ | ⟨_,_,m,hm⟩ | ⟨j,k,he,_⟩ | ⟨_,_,w,-,hw⟩ |
    ⟨_,_,j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ | ⟨j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨_,_,j,k,he,_⟩ | ⟨_,_,hi⟩
  · exact ⟨he.symm,hb,hb'⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · exfalso
    rcases ha with ⟨-,h0,-⟩ | ⟨-,-,ha⟩
    · simp_all
    · cases hv : v.1 with
      | thread j => rw [hv] at ha; exact ha
      | async j p => rw [hv] at ha; cases p <;> exact ha
  · exact (notifyClcRecord_no_notify_before ho hn hm).elim
  · cases he
  · exact (notifyClcRecord_not_witness ho hn hid w hw).elim
  · cases he
  · cases he
  · cases he
  · cases he
  · cases he
  · obtain ⟨_,_,k,q,he,_⟩ := hi
    cases he

/-- The fresh notification only completes; its appended record has no successor in the
object history and it fills no need. Outside it every order relation is old. -/
theorem notifyClcRecord_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) :
    SinkFrame L K A X (X.notifyClcRecord i c mb rec)
      (CompletionNodes L (X.notifyClcRecord i c mb rec) (· = .async i (.notify (.cta c)))) := by
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hnot : ∀ {w : Ref}, ¬ w=.async i (.notify (.cta c)) → rec.id≠w := fun hw he =>
    hw (he.symm.trans hid)
  have hth : ∀ e, rec.id≠.thread e := fun e h => by rw [hid] at h; cases h
  have hpres : ∀ {e : Ref}, e≠.async i (.notify (.cta c)) →
      (X.notifyClcRecord i c mb rec).RefPresent e → X.RefPresent e :=
    fun he h => (notifyClcRecord_present_old he).mp h
  have hold : ∀ {u : Ref × Bool}, ¬ CompletionNodes L (X.notifyClcRecord i c mb rec)
      (· = .async i (.notify (.cta c))) u → u.1≠.async i (.notify (.cta c)) :=
    fun hu he => hu (.inl he)
  have hobject : ∀ o (u v : Ref × Bool), v.1≠.async i (.notify (.cta c)) →
      ObjectOrder L (X.notifyClcRecord i c mb rec) o u v → ObjectOrder L X o u v :=
    fun o u v hv h => (appendObject_objectOrder_iff (X := X.markClcNotify i c) (hnot hv)).mp h
  refine sinkFrame_completion (· = .async i (.notify (.cta c))) (fun _ h => by cases h)
    (fun u v hu h => ?_) (fun w x hx hw => (notifyClcRecord_not_witness ho hn hid w (hx ▸ hw)).elim)
    (fun u v hu hv hc => ?_) (fun x w hx hw h => ?_)
    (fun o u v _ hv h => hobject o u v (hold hv) h) (fun o u v _ hv h => ?_)
    (fun u v hu hv hc => ?_) (fun m j p y hb => ?_) (fun m j p y _ _ h => ?_) hX.initFence
    (fun _ _ _ h => h) (fun m y init h => ?_) (fun _ => rfl)
  · obtain ⟨e, b⟩ := u
    change e = _ at hu
    subst hu
    exact .inl (notifyClcRecord_waits_from ho hn hid h)
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | ⟨h1, h2, j, k, h3, h4, hc⟩ | ⟨h1, h2, k, h3, d, p, w, ws, h5, h6, h7, h8⟩
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.notifyClcRecord i c mb rec)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl ⟨h1, h2, j, k, h3, h4,
        (notifyClcRecord_baseCausality hid).mp hc⟩))
    · exact .single (.inr (.inr ⟨h1, h2, k, h3, d, p, w, ws, h5, h6,
        (notifyClcRecord_observed ho hn hid).mp h7, h8⟩))
  · have hx' : x≠.async i (.notify (.cta c)) := hold hx
    have hw' : w≠.async i (.notify (.cta c)) := hold hw
    rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · have h' := (appendObject_mbarObserved_iff (X := X.markClcNotify i c) (hnot hx')
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
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.notifyClcRecord i c mb rec)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl (IssueStage.transfer (X := X)
        (Y := X.notifyClcRecord i c mb rec) (fun _ => rfl) (hpres (hold hv)) hc)))
    · rw [notifyClcRecord_needs ho hn hid] at hn'
      exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, fills, hn', hpres (hold hu) hx, hf⟩)))
    · exact .single (.inr (.inr (.inr hc)))
  · by_cases hy : rec.id = y
    · rintro ⟨k, rfl, -⟩
      exact hth k hy
    · have hb' := (appendObject_objectOrder_iff (X := X.markClcNotify i c) (L := L)
        (o := .mbar m) (u := (.async j p, true)) (v := (y, true)) hy).mp ⟨rfl, rfl, hb⟩
      exact (hX.asyncObject m j p y hb'.2.2).1
  · rcases h with h | ⟨k, ws, rfl, hw⟩
    · exact .inl h
    · exact .inr ⟨k, ws, rfl, (appendObject_waitObserves_iff (hth k)).mp hw⟩
  · have hb' := (appendObject_objectOrder_iff (X := X.markClcNotify i c) (L := L)
      (o := .mbar m) (u := (y, true)) (v := (.thread init, true)) (hth init)).mp ⟨rfl, rfl, h⟩
    exact hb'.2.2

end
end PTX
