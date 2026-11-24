-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcCompleteConsistentWriteWaiting
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.MBarrier.MBarrierPhase
public import Lemmas.Tcgen05.TcReadSemanticFrame
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Order.Order
public import Lemmas.Order.CompletionFrame

@[expose] public section

section
/-! The CLC notification and its actual checked object transition are one
extension. Object faults are represented, not filtered or assumed absent. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

def Execution.markClcNotify (X : Execution) (i : EvId) (c : Nat) : Execution :=
  { X with clc := fun j => if j=i then
      {X.clc j with notified:=insert c (X.clc j).notified} else X.clc j }

def Execution.notifyClcRecord (X : Execution) (i : EvId) (c : Nat)
    (m : Loc) (rec : Record Ref) : Execution :=
  (X.markClcNotify i c).appendObject m rec

def clcCompletionRecord (before : Option State) (i : EvId) (c : Nat) : Record Ref :=
  match perform before (.completeTx 16) with
  | .ok reply => ⟨.async i (.notify (.cta c)),.completeTx 16,reply,none⟩
  | .error fault => ⟨.async i (.notify (.cta c)),.completeTx 16,⟨before,none,none⟩,some fault⟩

theorem clcCompletionRecord_id (before : Option State) (i : EvId) (c : Nat) :
    (clcCompletionRecord before i c).id=.async i (.notify (.cta c)) := by
  unfold clcCompletionRecord
  split <;> rfl

theorem clcCompletionRecord_action (before : Option State) (i : EvId) (c : Nat) :
    (clcCompletionRecord before i c).action=.completeTx 16 := by
  unfold clcCompletionRecord
  split <;> rfl

theorem clcCompletionRecord_ok (before : Option State) (i : EvId) (c : Nat) :
    RecordOk before (clcCompletionRecord before i c) := by
  unfold clcCompletionRecord
  split <;> rename_i h <;> simp [RecordOk,h]

variable {X : Execution} {i : EvId} {c : Nat} {mb : Loc} {rec : Record Ref}

theorem notifyClcRecord_action_old {m : Loc} {id : Ref}
    (hid : id≠.async i (.notify (.cta c))) :
    objectAction (X.notifyClcRecord i c mb rec) (X.notifyClcRecord i c mb rec).async m id=
      objectAction X X.async m id := by
  cases id with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case notifyCta d =>
      by_cases hj : j=i
      · subst j
        have hd : d≠c := by intro hd; subst d; exact hid rfl
        simp only [objectAction,Execution.notifyClcRecord,Execution.appendObject,
          Execution.markClcNotify,↓reduceIte]
        simp only [Finset.mem_insert,hd,false_or]
        rfl
      · simp only [objectAction,Execution.notifyClcRecord,Execution.appendObject,
          Execution.markClcNotify,ite_eq_right hj]
        rfl

theorem notifyClcRecord_action_notify {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) (hc : c∈targets) (m : Loc) :
    objectAction (X.notifyClcRecord i c mb rec) (X.notifyClcRecord i c mb rec).async m
      (.async i (.notify (.cta c)))=
      if m={s.mbar with cta:=c} then some (.completeTx 16) else none := by
  obtain ⟨pc,he⟩ := hi
  change (X.tr i.1)[i.2]?=some ⟨pc,.clcIssue s targets⟩ at he
  simp [objectAction,Execution.notifyClcRecord,Execution.appendObject,
    Execution.markClcNotify,Execution.get,he,hc]

theorem no_clc_notification_record (ho : ObjectsOk X)
    (hn : c∉(X.clc i).notified) {m : Loc} {q : Record Ref}
    (hq : q∈X.objects m) : q.id≠.async i (.notify (.cta c)) := by
  intro hid
  have hs := ((ho m).2.1 q hq).1
  rw [hid] at hs
  cases he : X.get i with
  | none => simp [objectAction,he] at hs
  | some ev =>
    rcases ev with ⟨pc,kind⟩
    cases kind <;> simp [objectAction,he,hn] at hs

/-- The appended completion record is the result of the actual object state. -/
theorem notifyClcRecord_checked (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (m : Loc) : CheckedLog (X.objects m++[
      clcCompletionRecord (stateBefore (X.objects m) (X.objects m).length) i c]) := by
  have hp := (ho m).1.prefix (Nat.le_refl (X.objects m).length)
  rw [List.take_length] at hp
  apply CheckedLog.snoc hp (ho m).1.1
  · intro hid
    obtain ⟨q,hq,hqid⟩ := List.mem_map.mp hid
    exact no_clc_notification_record ho hn hq
      (hqid.trans (clcCompletionRecord_id _ _ _))
  · exact clcCompletionRecord_ok _ _ _

theorem notifyClcRecord_objects (ho : ObjectsOk X) {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) (hct : c∈targets)
    (hmb : mb={s.mbar with cta:=c}) (hn : c∉(X.clc i).notified)
    (hid : rec.id = .async i (.notify (.cta c))) (ha : rec.action = .completeTx 16)
    (hc : CheckedLog (X.objects mb ++ [rec])) :
    ObjectsOk (X.notifyClcRecord i c mb rec) := by
  intro loc
  by_cases hm : loc = mb
  · subst loc
    refine ⟨by simpa [Execution.notifyClcRecord, Execution.appendObject,
        Execution.markClcNotify] using hc,
      ?_, ?_⟩
    · intro r hr
      have hr' : r ∈ X.objects mb ++ [rec] := by
        simpa [Execution.notifyClcRecord, Execution.appendObject, Execution.markClcNotify] using hr
      rcases List.mem_append.mp hr' with hold | hnew
      · obtain ⟨ha', hp⟩ := (ho mb).2.1 r hold
        refine ⟨?_, hp⟩
        rw [notifyClcRecord_action_old (no_clc_notification_record ho hn hold)]
        exact ha'
      · have he := List.mem_singleton.mp hnew
        subst r
        refine ⟨?_, ?_⟩
        · rw [hid, notifyClcRecord_action_notify hi hct, ite_eq_left hmb, ha]
        · intro p ok hp; rw [ha] at hp; cases hp
    · intro id act hact
      by_cases he : id = .async i (.notify (.cta c))
      · exact ⟨rec, by simp [Execution.notifyClcRecord, Execution.appendObject,
          Execution.markClcNotify], hid.trans he.symm⟩
      · rw [notifyClcRecord_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho mb).2.2 id act hact
        exact ⟨r, by simp [Execution.notifyClcRecord, Execution.appendObject,
          Execution.markClcNotify, hr], hrid⟩
  · have hlog : (X.notifyClcRecord i c mb rec).objects loc = X.objects loc := by
      simp [Execution.notifyClcRecord, Execution.appendObject, Execution.markClcNotify, hm]
    refine ⟨by rw [hlog]; exact (ho loc).1, ?_, ?_⟩
    · intro r hr
      rw [hlog] at hr
      obtain ⟨ha', hp⟩ := (ho loc).2.1 r hr
      refine ⟨?_, hp⟩
      rw [notifyClcRecord_action_old (no_clc_notification_record ho hn hr)]
      exact ha'
    · intro id act hact
      by_cases he : id = .async i (.notify (.cta c))
      · subst id
        rw [notifyClcRecord_action_notify hi hct, ite_eq_right (by rwa [←hmb])] at hact
        cases hact
      · rw [notifyClcRecord_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho loc).2.2 id act hact
        exact ⟨r, hlog ▸ hr, hrid⟩

end
end PTX
end

section
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {c : Nat} {mb : Loc} {rec : Record Ref}

theorem markClcNotify_clcOk {s : Clc.Spec} {targets : List Nat}
    (hX : ClcOk L X) (hi : X.ClcIssue i s targets) (hw : c∈(X.clc i).written) :
    ClcOk L (X.markClcNotify i c) := by
  refine ⟨hX.1,hX.2.1,?_,?_,hX.2.2.2.2⟩
  · intro j he
    by_cases hj : j=i
    · subst j
      exact ⟨s,targets,hi⟩
    · exact hX.2.2.1 j (by simpa only [Execution.markClcNotify,ite_eq_right hj] using he)
  · intro j t ts hj
    obtain ⟨he,hnd,htarget⟩ := hX.2.2.2.1 j t ts hj
    by_cases hji : j=i
    · subst j
      refine ⟨⟨hX.1,?_,?_,?_⟩,hnd,htarget⟩
      · simpa [Execution.markClcNotify] using he.result
      · simpa [Execution.markClcNotify] using he.writes
      · intro d hd
        have hd' : d=c ∨ d∈(X.clc i).notified := by
          simpa [Execution.markClcNotify] using hd
        rcases hd' with rfl | hd
        · simpa [Execution.markClcNotify] using hw
        · simpa [Execution.markClcNotify] using he.notified d hd
    · simpa only [Execution.markClcNotify,ite_eq_right hji] using ⟨he,hnd,htarget⟩

theorem markClcNotify_le : X.le (X.markClcNotify i c) := by
  have h := Execution.le_refl X
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    ?_,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Execution.markClcNotify,↓reduceIte]
    exact ⟨fun _ h => h,fun _ h => h,Finset.subset_insert _ _⟩
  · simpa only [Execution.markClcNotify,ite_eq_right hj] using Clc.Extends.refl (X.clc j)

theorem notifyClcRecord_le : X.le (X.notifyClcRecord i c mb rec) :=
  Execution.le_trans markClcNotify_le (Execution.le_appendObject _ _ _)

theorem markClcNotify_asyncSize {j : EvId} (hn : c∉(X.clc i).notified) :
    (X.markClcNotify i c).asyncSize j=if j=i then X.asyncSize j+1 else X.asyncSize j := by
  have hres (k : EvId) : ((X.markClcNotify i c).clc k).resolved=(X.clc k).resolved := by
    by_cases hk : k=i <;> simp [Execution.markClcNotify,hk]
  have hwr (k : EvId) : ((X.markClcNotify i c).clc k).written=(X.clc k).written := by
    by_cases hk : k=i <;> simp [Execution.markClcNotify,hk]
  have hnf (k : EvId) : ((X.markClcNotify i c).clc k).notified=
      if k=i then insert c (X.clc k).notified else (X.clc k).notified := by
    by_cases hk : k=i <;> simp [Execution.markClcNotify,hk]
  have helem (k : EvId) : (X.markClcNotify i c).elemSize k=X.elemSize k := by
    obtain ⟨a, b⟩ := k
    rfl
  have hasync : (X.markClcNotify i c).async=X.async := rfl
  have htensor : (X.markClcNotify i c).tensor=X.tensor := rfl
  have hstores : (X.markClcNotify i c).tensorStores=X.tensorStores := rfl
  have htc : (X.markClcNotify i c).tcNotified=X.tcNotified := rfl
  rw [Execution.asyncSize,Execution.asyncSize,hres j,hwr j,hnf j,helem j,hasync,htensor,
    hstores,htc]
  by_cases hj : j=i
  · subst j
    simp only [↓reduceIte,Finset.card_insert_of_notMem hn]
    omega
  · simp only [hj,↓reduceIte]
 theorem markClcNotify_size {L : Launch} {X : Execution} {i : EvId} {c : Nat}
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) (hn : c∉(X.clc i).notified) :
    (X.markClcNotify i c).size L=X.size L+1 := by
  have hs (j : EvId) := markClcNotify_asyncSize (X:=X) (i:=i) (j:=j) (c:=c) hn
  have heq (g k : Nat) : (g,k)=i ↔ g=i.1 ∧ k=i.2 := Prod.ext_iff
  have hthread (g : Nat) :
      ((List.range (X.tr g).length).map fun k => (X.markClcNotify i c).asyncSize (g,k)).sum=
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+
          (if g=i.1 then 1 else 0) := by
    simp_rw [hs,heq]
    by_cases hg' : g=i.1
    · subst g
      simp only [true_and,↓reduceIte]
      exact sum_range_bump _ _ _ |>.trans (by rw [ite_eq_left hi])
    · simp only [hg',false_and,Nat.add_zero,↓reduceIte]
  unfold Execution.size Execution.threadSize
  change ((List.range L.threads).map fun g =>
    (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map fun k => (X.markClcNotify i c).asyncSize (g,k)).sum).sum+
      X.pairSize L=_
  simp_rw [hthread]
  have hb := sum_range_bump
    (fun g => (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum) i.1 L.threads
  rw [ite_eq_left hg] at hb
  have hh : ∀g, (X.tr g).countP Event.counts+
      (((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+
        (if g=i.1 then 1 else 0))=
      if g=i.1 then (X.tr g).countP Event.counts+
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+1
      else (X.tr g).countP Event.counts+
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum := by
    intro g
    split_ifs <;> omega
  simp_rw [hh]
  rw [hb]
  omega

end
end PTX
end

section
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {c : Nat} {mb : Loc} {rec : Record Ref}

theorem notifyClcRecord_baseCausality {e f : EvId} (hid : rec.id=.async i (.notify (.cta c))) :
    baseCausality L (X.notifyClcRecord i c mb rec) e f ↔ baseCausality L X e f := by
  have hneq (w : EvId) : rec.id≠.thread w := by rw [hid]; intro h; cases h
  exact (appendObject_baseCausality_iff (fun w _ _ => hneq w)).trans Iff.rfl

theorem notifyClcRecord_observesMma {mma w : EvId} {acq : Bool} {ws : MbarScope}
    (hid : rec.id=.async i (.notify (.cta c))) :
    AsyncObserved (X.notifyClcRecord i c mb rec) mma .mmaDone w acq ws ↔
      AsyncObserved X mma .mmaDone w acq ws := by
  have hneq : rec.id≠.thread w := by rw [hid]; intro h; cases h
  exact (appendObject_asyncObserved_iff hneq).trans Iff.rfl

theorem notifyClcRecord_readOk {A : List Assumption}
    (hid : rec.id=.async i (.notify (.cta c))) :
    TcMma.ReadOk L A (X.notifyClcRecord i c mb rec) ↔ TcMma.ReadOk L A X := by
  exact (show TcMma.SemanticFrame L X (X.notifyClcRecord i c mb rec) from
    ⟨fun _ => rfl,fun _ => rfl,rfl,rfl,
      fun _ _ => notifyClcRecord_baseCausality hid,fun _ _ _ _ => notifyClcRecord_observesMma hid,
      fun _ w =>
        (TcMma.appendObject_mbarExec_iff (by rw [hid]; intro h; cases h)).trans Iff.rfl⟩).readOk

theorem notifyClcRecord_memWrites {e : Ref} {a : Acc} {bs : List Byte} :
    (X.notifyClcRecord i c mb rec).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => exact Iff.rfl
  | async j p =>
    cases p <;> try exact Iff.rfl
    case writeCta d =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemWrites,Clc.ResponseWrite,Execution.notifyClcRecord,
          Execution.appendObject,Execution.markClcNotify,↓reduceIte]
        rfl
      · simp only [Execution.MemWrites,Execution.notifyClcRecord,
          Execution.appendObject,Execution.markClcNotify,ite_eq_right hj]
        rfl

 theorem markClcNotify_observed {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope}
    (ho : ObjectsOk X) (hn : c∉(X.clc i).notified) :
    AsyncObserved (X.markClcNotify i c) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  cases p <;> try rfl
  all_goals
    rename_i d
    by_cases hj : j=i
    · subst j
      by_cases hd : d=c
      · subst d
        constructor
        · rintro ⟨n,m,⟨rfl,-⟩,-,k,l,r,q,phase,hk,hidn,_⟩
          exact (no_clc_notification_record ho hn (List.mem_of_getElem? hk) hidn).elim
        · rintro ⟨n,m,⟨rfl,s,targets,hi,hct,hnot,hm⟩,-⟩
          exact (hn hnot).elim
      · simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
          Execution.markClcNotify,↓reduceIte,
          Finset.mem_insert,hd,false_or]
        rfl
    · simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
        Execution.markClcNotify,ite_eq_right hj]
      rfl

theorem notifyClcRecord_observed {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope}
    (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) :
    AsyncObserved (X.notifyClcRecord i c mb rec) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  have hneq : rec.id≠.thread w := by rw [hid]; intro h; cases h
  exact (appendObject_asyncObserved_iff hneq).trans (markClcNotify_observed ho hn)

/-- The stages that a group wait waits for are not CLC notifications, so their presence is
unchanged. -/
theorem notifyClcRecord_groupPresent (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages (X.notifyClcRecord i c mb rec) j k,
        (X.notifyClcRecord i c mb rec).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl <;> exact Iff.rfl

theorem notifyClcRecord_finished {j w : EvId} {p : Part}
    (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) :
    AsyncFinished L (X.notifyClcRecord i c mb rec) j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      notifyClcRecord_groupPresent j k)
    (exists_congr fun _ => and_congr_left' (notifyClcRecord_observed ho hn hid))

 theorem notifyClcRecord_onlyFinished {j w : EvId} {p : Part} :
    AsyncOnlyFinished (X.notifyClcRecord i c mb rec) j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ => notifyClcRecord_groupPresent j _

theorem notifyClcRecord_before {l : Loc} {a b : EvId × Part}
    (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) :
    AsyncBefore L (X.notifyClcRecord i c mb rec) l a b ↔ AsyncBefore L X l a b := by
  simp only [AsyncBefore,notifyClcRecord_finished ho hn hid,
    notifyClcRecord_onlyFinished,notifyClcRecord_baseCausality hid]
  rfl

theorem notifyClcRecord_present_memory {j : EvId} {p : Part}
    (hp : ∀d,p≠.notify (.cta d)) :
    (X.notifyClcRecord i c mb rec).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try exact Iff.rfl
  case notifyCta d => exact (hp _ rfl).elim
  all_goals
    by_cases hj : j=i <;> simp [Execution.AsyncPresent,Execution.notifyClcRecord,
      Execution.appendObject,Execution.markClcNotify,hj]

theorem notifyClcRecord_modelCausality {l : Loc} {e f : Ref}
    (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) :
    modelCausality L (X.notifyClcRecord i c mb rec) l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  · exact or_congr (notifyClcRecord_baseCausality hid) Iff.rfl
  · simp only [modelCausality,ProxyBefore,notifyClcRecord_baseCausality hid]
    rfl
  · have hcb (j : EvId) (p : Part) (w f : EvId) :
        ObservedCompletionBefore L (X.notifyClcRecord i c mb rec) l j p w f ↔
          ObservedCompletionBefore L X l j p w f :=
      observedCompletionBefore_congr rfl rfl (notifyClcRecord_baseCausality hid)
        (by simp only [ProxyBefore,notifyClcRecord_baseCausality hid]; rfl)
    simp only [modelCausality,notifyClcRecord_finished ho hn hid,hcb]
    rfl
  · refine and_congr_right fun _ => ?_
    apply AsyncChain.congr_on_edges (fun _ _ => notifyClcRecord_before ho hn hid)
    intro a b hedge
    apply notifyClcRecord_present_memory
    intro d hp
    obtain ⟨footprint,write,hi,_⟩ := hedge.1
    rw [hp] at hi
    cases hi.2

 theorem notifyClcRecord_rf {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) : RfWf mem0 (X.notifyClcRecord i c mb rec) := by
  intro e a bs he
  have hold : X.MemReads e a bs := he
  obtain ⟨hlen,hvalues⟩ := hX.rf e a bs hold
  refine ⟨hlen,?_⟩
  intro k hk
  have hv := hvalues k hk
  change match X.rf e k with
    | none => _
    | some w => _
  cases hsrc : X.rf e k with
  | none => simp only [hsrc] at hv ⊢; exact hv
  | some w =>
    rw [hsrc] at hv
    obtain ⟨dst,bytes,hw,hcover,hval⟩ := hv
    exact ⟨dst,bytes,notifyClcRecord_memWrites.mpr hw,hcover,hval⟩

theorem notifyClcRecord_present_old {e : Ref} (he : e≠.async i (.notify (.cta c))) :
    (X.notifyClcRecord i c mb rec).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hj : j=i
    · subst j
      cases p <;> try exact Iff.rfl
      case pos.notifyCta d =>
        have hd : d≠c := by intro hd; subst d; exact he rfl
        simp [Execution.RefPresent,Execution.AsyncPresent,Execution.notifyClcRecord,
          Execution.appendObject,Execution.markClcNotify,hd]
      all_goals simp [Execution.RefPresent,Execution.AsyncPresent,Execution.notifyClcRecord,
        Execution.appendObject,Execution.markClcNotify]
    · cases p <;> simp [Execution.RefPresent,Execution.AsyncPresent,Execution.notifyClcRecord,
        Execution.appendObject,Execution.markClcNotify,hj]
      all_goals rfl

/-- The needs of every event are unchanged: the new record is observed by no wait, and the
presence of every recorded update is old. -/
theorem notifyClcRecord_needs (ho : ObjectsOk X) (hn : c∉(X.clc i).notified)
    (hid : rec.id=.async i (.notify (.cta c))) (e : EvId) :
    Needs L (X.notifyClcRecord i c mb rec) e = Needs L X e := by
  refine (appendObject_needs (X := X.markClcNotify i c)
    (fun l q hq h => no_clc_notification_record ho hn hq (h.trans hid))
    (fun e h => by rw [hid] at h; cases h) e).trans ?_
  refine needs_congr (X := X) (Y := X.markClcNotify i c) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e m => pollNeeds_congr (X := X) (Y := X.markClcNotify i c) (fun _ => rfl)
      (fun m r hr w => and_congr ?_ Iff.rfl) e m) e
  exact notifyClcRecord_present_old (mb := mb) (rec := rec) (no_clc_notification_record ho hn hr)

/-- The new notification fills no need of `X`: it is no thread node, no stage a group wait waits
for and no recorded update of `X`. -/
theorem notifyClcRecord_not_needRef (ho : ObjectsOk X) (hn : c∉(X.clc i).notified) :
    ¬ NeedRef X (.async i (.notify (.cta c))) := by
  rintro (⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨m, r, hr, h⟩)
  · cases h
  · cases h
    rcases groupWaitStages_cases X _ k hq with h | h | h | h <;> cases h
  · exact no_clc_notification_record ho hn hr h.symm

/-- Only the execution-order obligation remains separate from this actual
notification frame. Every old memory observation and object source is retained. -/
theorem consistent_notifyClcRecord {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {s : Clc.Spec} {targets : List Nat}
    (hX : Consistent L K A mem0 X) (hi : X.ClcIssue i s targets) (hct : c∈targets)
    (hw : c∈(X.clc i).written) (hn : c∉(X.clc i).notified)
    (hmb : mb={s.mbar with cta:=c}) (hid : rec.id=.async i (.notify (.cta c)))
    (ha : rec.action=.completeTx 16) (hc : CheckedLog (X.objects mb++[rec]))
    (hac : OrderOk L K A (X.notifyClcRecord i c mb rec))
    (hasm : ∀a∈A,a.wf L mem0 (X.notifyClcRecord i c mb rec)) :
    Consistent L K A mem0 (X.notifyClcRecord i c mb rec) := by
  have ho : ObjectsOk X := hX.tma.2.2.1
  have hdep : DependencyOk L K (X.notifyClcRecord i c mb rec) := by
    refine ⟨?_, hac.depAcyclic⟩
    intro e hret n hn'
    rw [notifyClcRecord_needs ho hn hid] at hn'
    have hready := hX.dependency.ready e hret n hn'
    cases n with
    | cond holds => exact hready
    | node fills =>
      obtain ⟨x, hx, hf⟩ := hready
      have hne : x≠.async i (.notify (.cta c)) := by
        rintro rfl
        exact notifyClcRecord_not_needRef ho hn (needs_node_cases hn' hf)
      exact ⟨x, (notifyClcRecord_present_old hne).mpr hx, hf⟩
  refine { hX with
    clc := markClcNotify_clcOk hX.clc hi hw
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
    rf := notifyClcRecord_rf hX
    dependency := hdep
    observation := hac.observation
    object := hac.object
    asyncObject := hac.asyncObject
    initFence := hac.initFence
    noFuture := NoFuture.of_frame hX.noFuture (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.notifyClcRecord i c mb rec) rfl rfl
        (fun h => (notifyClcRecord_modelCausality ho hn hid).mp h)
        (fun h => (notifyClcRecord_observesMma hid).mp h))
    hidden := Hidden.of_frame hX.hidden (fun _ _ _ h => h)
      (fun _ _ _ h => notifyClcRecord_memWrites.mp h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.notifyClcRecord i c mb rec) rfl rfl
        (fun h => (notifyClcRecord_modelCausality ho hn hid).mp h)
        (fun h => (notifyClcRecord_observesMma hid).mp h))
    tcRead := (notifyClcRecord_readOk hid).mpr hX.tcRead
    tma := ⟨hX.tma.1,hX.tma.2.1,
      notifyClcRecord_objects ho hi hct hmb hn hid ha hc,hX.tma.2.2.2⟩
    reduce := ⟨hX.reduce.values, hX.reduce.copies⟩
    atomic := ⟨hX.atomic.unique, hX.atomic.acyclic⟩
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs h =>
      hX.fenceSc.causal e f hs ((notifyClcRecord_baseCausality hid).mp h)⟩
    asm := hasm }

end
end PTX
end
