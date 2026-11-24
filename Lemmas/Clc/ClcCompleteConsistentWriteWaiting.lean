-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcCompleteConsistentResolve
public import Lemmas.Clc.ClcCompleteConsistentReadFrame
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Execution.EffectFrame
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Order.CompletionFrame
public import Lemmas.Order.OrderFrame
public import Lemmas.Async.SyncObservedFrame

@[expose] public section

section
/-! A CLC response stage, the resolution of a request or the write of its response at one target
CTA, is a sink of every order. It is not a stage a group wait waits for and not the id of a
recorded object update, so it fills no need (DEP-ORDER) and no object orders it; its only stage
successor (the write after the resolution, the notification after the write) is absent. The
extension changes only the CLC rows, so outside the new stage every order relation is that of
`X` (`sinkFrame_clcStage`). -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution} {C : EvId → Clc.Effects}
  {i : EvId} {p : Part}

set_option quotPrecheck false in
local notation "XC" => ({ X with clc := C } : Execution)

/-- A stage a group wait waits for is no CLC response stage. -/
theorem clcStage_not_groupWaitStage {Y : Execution} (hp : p = .resolve ∨ ∃ c, p = .write (.cta c))
    {j : EvId} {k : GroupWait} {q : Part} (hq : q ∈ GroupWaitStages Y j k) : q ≠ p := by
  rintro rfl
  rcases groupWaitStages_cases _ _ _ hq with rfl | rfl | rfl | rfl <;>
    rcases hp with h | ⟨c, h⟩ <;> cases h

/-- A CLC response stage fills no need: it is no thread node, no stage a group wait waits for and
no recorded object update. -/
theorem clcStage_not_needRef (hobj : ObjectsOk X) (hp : p = .resolve ∨ ∃ c, p = .write (.cta c)) :
    ¬ NeedRef XC (.async i p) := by
  rintro (⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨m, r, hr, h⟩)
  · cases h
  · obtain ⟨-, rfl⟩ := Ref.async.inj h
    exact clcStage_not_groupWaitStage hp hq rfl
  · rcases record_id_cases hobj hr with ⟨t, ht⟩ | ⟨j, ht⟩ | ⟨j, ht⟩ | ⟨j, c, ht⟩ | ⟨j, ht⟩ |
      ⟨j, rk, ht⟩ <;> rw [ht] at h <;> cases h <;> rcases hp with h | ⟨c, h⟩ <;> cases h

/-- The needs of every event are those of `X` when the presence of every recorded object update
is that of `X`. -/
theorem clc_needs (hobj : ObjectsOk X) (hpres : ∀ u, u ≠ .async i p → ((XC).RefPresent u ↔
      X.RefPresent u)) (hp : p = .resolve ∨ ∃ c, p = .write (.cta c)) (e : EvId) :
    Needs L XC e = Needs L X e :=
  needs_congr (X := X) (Y := XC) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e m => pollNeeds_congr (X := X) (Y := XC) (fun _ => rfl)
      (fun _ r hr _ => and_congr (hpres r.id fun h =>
        clcStage_not_needRef (C := C) hobj hp (.inr (.inr ⟨_, r, hr, h.symm⟩))) Iff.rfl) e m) e

/-- The copy release synchronization reads only the notifications of copies and tensor loads,
which the CLC rows do not change. -/
theorem clc_copyReleaseSync {n : Ref} {f : EvId} (h : CopyReleaseSync L XC n f) :
    CopyReleaseSync L X n f := by
  obtain ⟨j, q, w, ws, rfl, hq, ho, hs, hpo⟩ := h
  rcases hq with rfl | rfl
  · exact ⟨j, _, w, ws, rfl, .inl rfl, ho, hs, hpo⟩
  · exact ⟨j, _, w, ws, rfl, .inr rfl, ho, hs, hpo⟩

/-- **A CLC response stage is a sink frame.** -/
theorem sinkFrame_clcStage (hobj : ObjectsOk X) (hao : AsyncObjectOrdered L X)
    (hinit : InitFenceOrdered L X) (hp : p = .resolve ∨ ∃ c, p = .write (.cta c))
    (hpres : ∀ u, u ≠ .async i p → ((XC).RefPresent u ↔ X.RefPresent u))
    (hnext : ∀ f, ¬ StageEdge XC (.async i p) f) :
    SinkFrame L K A X XC (fun n => n.1 = .async i p) := by
  have hpres' : ∀ u, ¬ u = .async i p → ((XC).RefPresent u ↔ X.RefPresent u) := hpres
  have hedge : ∀ e f, ¬ e = .async i p → ¬ f = .async i p → StageEdge XC e f → StageEdge X e f :=
    fun e f he hf h => StageEdge.transfer (X := X) (Y := XC) (fun _ _ h => h) (fun _ _ h => h)
      (hpres e he).mp (hpres f hf).mp h
  refine sinkFrame_new_effect (R := X.rf) (T := X.tensor) (S := X.tensorStores)
    (· = .async i p) (fun _ h => by cases h) ?_ hao hinit
    (fun u v hu hv h => stageCausality_frame (N := (· = .async i p)) hpres' hedge
      (fun _ _ => baseCausality_new_effect (fun _ _ => rfl)) (fun _ _ h => clc_copyReleaseSync h)
      hu hv h)
    (fun x w hx _ h => syncObserved_frame (N := (· = .async i p)) hpres' hx h)
    (fun u v hu hv h => depStep_frame (N := (· = .async i p)) hpres' hedge
      (clc_needs hobj hpres hp) hu hv h)
  rintro ⟨e, b⟩ ⟨f, b'⟩ he h
  simp only at he
  subst he
  rcases h with ⟨he, hb, hb', -⟩ | ⟨-, -, j, k, he, -⟩ |
    ⟨j, k, he, -⟩ | ⟨-, -, j, k, he, -⟩ | ⟨-, -, j, k, he, -⟩ |
    ⟨hb, -, hs | hs⟩ | ⟨-, -, m, j, k, r, q, hr, hid, -⟩ | ⟨j, k, he, -⟩ |
    ⟨-, -, w, -, fills, hn, -, hf⟩ |
    ⟨-, -, j, k, he, -⟩ | ⟨-, -, j, k, he, -⟩ | ⟨j, k, he, -⟩ | ⟨-, -, j, k, he, -⟩ |
    ⟨-, -, j, k, he, -⟩ | ⟨-, -, hi⟩
  · exact ⟨he.symm, hb, hb'⟩
  all_goals try cases he
  · obtain ⟨-, h, -⟩ := hs
    rw [hb] at h
    cases h
  · exact (hnext f hs.2.2).elim
  · exact (clcStage_not_needRef (C := C) hobj hp
      (.inr (.inr ⟨m, r, List.mem_of_getElem? hr, hid.symm⟩))).elim
  · exact (clcStage_not_needRef (C := C) hobj hp (needs_node_cases hn hf)).elim
  · obtain ⟨-, -, j, q, he, -⟩ := hi
    cases he

end
end PTX
end

section
/-! Resolution adds no new asynchronous memory junction. The only new stage is the CLC
resolution, which is not a byte-access effect and fills no need. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {r : ClcResponse}

 theorem resolveClc_observed {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.resolveClc i r) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  cases p <;> try exact Iff.rfl
  all_goals
    by_cases hj : j=i
    · simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
        Execution.resolveClc,ite_eq_left hj]
      rfl
    · simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
        Execution.resolveClc,ite_eq_right hj]
      rfl

 theorem resolveClc_present_memory {j : EvId} {p : Part} (hp : p≠.resolve) :
    (X.resolveClc i r).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try exact Iff.rfl
  case resolve => exact (hp rfl).elim
  all_goals by_cases hj : j=i <;> simp [Execution.AsyncPresent,Execution.resolveClc,hj]

 theorem resolveClc_finished {j w : EvId} {p : Part} :
    AsyncFinished L (X.resolveClc i r) j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      forall₂_congr fun _ hq =>
        resolveClc_present_memory (clcStage_not_groupWaitStage (.inl rfl) hq))
    (exists_congr fun _ => and_congr_left' resolveClc_observed)

 theorem resolveClc_onlyFinished {j w : EvId} {p : Part} :
    AsyncOnlyFinished (X.resolveClc i r) j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun _ hq =>
      resolveClc_present_memory (clcStage_not_groupWaitStage (.inl rfl) hq)

 theorem resolveClc_before {l : Loc} {a b : EvId × Part} :
    AsyncBefore L (X.resolveClc i r) l a b ↔ AsyncBefore L X l a b := by
  simp only [AsyncBefore,resolveClc_finished,resolveClc_onlyFinished]
  rfl

 theorem resolveClc_modelCausality {l : Loc} {e f : Ref} :
    modelCausality L (X.resolveClc i r) l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  · exact Iff.rfl
  · exact Iff.rfl
  · simp only [modelCausality,resolveClc_finished]
    rfl
  · refine and_congr_right fun _ => ?_
    apply AsyncChain.congr_on_edges
      (fun _ _ => resolveClc_before)
    intro a b hedged
    apply resolveClc_present_memory
    intro hp
    have hc := hedged.1
    rcases hc with ⟨footprint,write,hi,_⟩
    rw [hp] at hi
    cases hi.2

 theorem resolveClc_objectAction {m : Loc} {e : Ref} :
    objectAction (X.resolveClc i r) (X.resolveClc i r).async m e=
      objectAction X X.async m e := by
  cases e with
  | thread j => rfl
  | async j p =>
    have hn : ((X.resolveClc i r).clc j).notified=(X.clc j).notified := by
      by_cases hj : j=i <;> simp [Execution.resolveClc,hj]
    cases p <;> try rfl
    case notifyCta c =>
      simp only [objectAction,hn]
      rfl

 theorem resolveClc_tma (hX : TmaOk X) : TmaOk (X.resolveClc i r) := by
  refine ⟨hX.1,hX.2.1,?_,hX.2.2.2⟩
  intro m
  obtain ⟨hc,hm,hcov⟩ := hX.2.2.1 m
  refine ⟨hc,?_,?_⟩
  · intro q hq
    have hh := hm q hq
    exact ⟨resolveClc_objectAction.trans hh.1,hh.2⟩
  · intro e action he
    rw [resolveClc_objectAction] at he
    exact hcov e action he

theorem resolveClc_present_old {e : Ref} (he : e≠.async i .resolve) :
    (X.resolveClc i r).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hp : p=.resolve
    · subst p
      have hj : j≠i := by intro hj; subst j; exact he rfl
      simp only [Execution.RefPresent,Execution.AsyncPresent,Execution.resolveClc,ite_eq_right hj]
    · exact resolveClc_present_memory hp

/-- Every node present in `X` is present after the resolution. -/
theorem resolveClc_present_mono (hn : (X.clc i).resolved=none) {e : Ref} (h : X.RefPresent e) :
    (X.resolveClc i r).RefPresent e := by
  by_cases he : e=.async i .resolve
  · subst he
    simp [Execution.RefPresent,Execution.AsyncPresent,hn] at h
  · exact (resolveClc_present_old he).mpr h

/-- The resolution has no present stage successor: no response is written before it. -/
theorem resolveClc_no_next {s : Clc.Spec} {targets : List Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hn : (X.clc i).resolved=none) (f : Ref) :
    ¬ StageEdge (X.resolveClc i r) (.async i .resolve) f := by
  intro h
  cases f with
  | thread j => exact h
  | async j q =>
    cases q <;> try exact h
    case writeCta c =>
      obtain ⟨rfl, -, hw⟩ := h
      have hw' : c∈(X.clc i).written := by
        simpa [Execution.AsyncPresent,Execution.resolveClc] using hw
      exact clc_unresolved_unwritten hX hi hn c hw'

/-- The fresh resolve stage is a sink of the execution order. -/
theorem resolveClc_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0} {s : Clc.Spec}
    {targets : List Nat} (hX : Consistent L K A mem0 X) (hi : X.ClcIssue i s targets)
    (hn : (X.clc i).resolved=none) :
    SinkFrame L K A X (X.resolveClc i r) (fun n => n.1=.async i .resolve) :=
  sinkFrame_clcStage (C := (X.resolveClc i r).clc) hX.tma.2.2.1 hX.asyncObject hX.initFence
    (.inl rfl) (fun _ he => resolveClc_present_old he) (resolveClc_no_next hX.clc hi hn)

/-- Resolving a real request is a full Consistent extension. The fresh stage is a sink of every
order and fills no need, while all old reads and sources are preserved. -/
theorem consistent_resolveClc_checked {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {s : Clc.Spec} {targets : List Nat}
    (hX : Consistent L K A mem0 X) (hi : X.ClcIssue i s targets)
    (hn : (X.clc i).resolved=none) (hr : Clc.Result L i X.clcState r)
    (hasm : ∀a∈A,a.wf L mem0 (X.resolveClc i r)) :
    Consistent L K A mem0 (X.resolveClc i r) := by
  have hord := (resolveClc_sinkFrame (r := r) hX hi hn).orderOk hX.orderOk
  refine { hX with
    clc := resolveClc_clcOk hX.clc hi hn hr
    rf := resolveClc_rf hX hi hn
    dependency := ⟨ready_congr
      (clc_needs (C := (X.resolveClc i r).clc) hX.tma.2.2.1
        (fun _ he => resolveClc_present_old he) (.inl rfl))
      (fun _ h => h) (fun _ _ _ _ _ hx => resolveClc_present_mono hn hx) hX.dependency.ready,
      hord.depAcyclic⟩
    observation := hord.observation
    object := hord.object
    asyncObject := hord.asyncObject
    initFence := hord.initFence
    noFuture := NoFuture.of_frame hX.noFuture (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.resolveClc i r) rfl rfl
        (fun h => resolveClc_modelCausality.mp h) (fun h => h))
    hidden := Hidden.of_frame hX.hidden (fun _ _ _ h => h)
      (fun _ _ _ h => (resolveClc_memWrites hX.clc hi hn).mp h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.resolveClc i r) rfl rfl
        (fun h => resolveClc_modelCausality.mp h) (fun h => h))
    tcRead := (TcMma.readOk_clc X.clcState _).mpr hX.tcRead
    tma := resolveClc_tma hX.tma
    reduce := ⟨hX.reduce.values, hX.reduce.copies⟩
    atomic := ⟨hX.atomic.unique, hX.atomic.acyclic⟩
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, hX.fenceSc.causal⟩
    asm := hasm }

end
end PTX
end

section
/-! Add one real response replica after arbitration. Publication remains a
separate notification effect; the old target has not yet been notified. -/
namespace PTX
noncomputable section

def Execution.writeClc (X : Execution) (i : EvId) (c : Nat) : Execution :=
  { X with clc := fun j =>
      if j=i then {X.clc j with written:=insert c (X.clc j).written} else X.clc j }

 theorem writeClc_clcOk {L : Launch} {X : Execution} {i : EvId} {r : ClcResponse}
    {s : Clc.Spec} {targets : List Nat} {c : Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hr : (X.clc i).resolved=some r) (hc : c∈targets) :
    ClcOk L (X.writeClc i c) := by
  refine ⟨hX.1,hX.2.1,?_,?_,hX.2.2.2.2⟩
  · intro j he
    by_cases hj : j=i
    · subst j
      exact ⟨s,targets,hi⟩
    · exact hX.2.2.1 j (by simpa only [Execution.writeClc,ite_eq_right hj] using he)
  · intro j t ts hj
    obtain ⟨he,hnd,htarget⟩ := hX.2.2.2.1 j t ts hj
    by_cases hji : j=i
    · subst j
      have ht : t=s ∧ ts=targets := by
        obtain ⟨pc,hpc⟩ := hi
        obtain ⟨pc',hpc'⟩ := hj
        have hh := Option.some.inj (hpc'.symm.trans hpc)
        have hk := (Event.mk.inj hh).2
        exact Kind.clcIssue.inj hk
      rcases ht with ⟨rfl,rfl⟩
      refine ⟨⟨hX.1,?_,?_,?_⟩,hnd,htarget⟩
      · simpa [Execution.writeClc] using he.result
      · intro d hd
        have hd' : d=c ∨ d∈(X.clc i).written := by
          simpa [Execution.writeClc] using hd
        rcases hd' with rfl | hd'
        · exact ⟨(htarget d).mp hc,by simp [Execution.writeClc,hr]⟩
        · exact ⟨(he.writes d hd').1,by simp [Execution.writeClc,hr]⟩
      · intro d hd
        have hd' : d∈(X.clc i).notified := by simpa [Execution.writeClc] using hd
        have hw := he.notified d hd'
        simpa [Execution.writeClc] using
          (Finset.mem_insert_of_mem hw : d∈insert c (X.clc i).written)
    · simpa only [Execution.writeClc,ite_eq_right hji] using ⟨he,hnd,htarget⟩

 theorem writeClc_not_notified {L : Launch} {X : Execution} {i : EvId}
    {s : Clc.Spec} {targets : List Nat} {c : Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hn : c∉(X.clc i).written) :
    c∉(X.clc i).notified := fun h => hn ((hX.2.2.2.1 i s targets hi).1.notified c h)

 theorem writeClc_le (X : Execution) (i : EvId) (c : Nat) : X.le (X.writeClc i c) := by
  have h := Execution.le_refl X
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    ?_,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Execution.writeClc,↓reduceIte]
    exact ⟨fun _ h => h,Finset.subset_insert _ _,fun _ h => h⟩
  · simpa only [Execution.writeClc,ite_eq_right hj] using Clc.Extends.refl (X.clc j)

 theorem writeClc_asyncSize {X : Execution} {i j : EvId} {c : Nat}
    (hn : c∉(X.clc i).written) :
    (X.writeClc i c).asyncSize j=if j=i then X.asyncSize j+1 else X.asyncSize j := by
  have hres (k : EvId) : ((X.writeClc i c).clc k).resolved=(X.clc k).resolved := by
    by_cases hk : k=i <;> simp [Execution.writeClc,hk]
  have hwr (k : EvId) : ((X.writeClc i c).clc k).written=
      if k=i then insert c (X.clc k).written else (X.clc k).written := by
    by_cases hk : k=i <;> simp [Execution.writeClc,hk]
  have hnf (k : EvId) : ((X.writeClc i c).clc k).notified=(X.clc k).notified := by
    by_cases hk : k=i <;> simp [Execution.writeClc,hk]
  have helem (k : EvId) : (X.writeClc i c).elemSize k=X.elemSize k := by
    obtain ⟨a, b⟩ := k
    rfl
  have hasync : (X.writeClc i c).async=X.async := rfl
  have htensor : (X.writeClc i c).tensor=X.tensor := rfl
  have hstores : (X.writeClc i c).tensorStores=X.tensorStores := rfl
  have htc : (X.writeClc i c).tcNotified=X.tcNotified := rfl
  rw [Execution.asyncSize,Execution.asyncSize,hres j,hwr j,hnf j,helem j,hasync,htensor,
    hstores,htc]
  by_cases hj : j=i
  · subst j
    simp only [↓reduceIte,Finset.card_insert_of_notMem hn]
    omega
  · simp only [hj,↓reduceIte]

 theorem writeClc_size {L : Launch} {X : Execution} {i : EvId} {c : Nat}
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) (hn : c∉(X.clc i).written) :
    (X.writeClc i c).size L=X.size L+1 := by
  have hs (j : EvId) := writeClc_asyncSize (X:=X) (i:=i) (j:=j) (c:=c) hn
  have heq (g k : Nat) : (g,k)=i ↔ g=i.1 ∧ k=i.2 := Prod.ext_iff
  have hthread (g : Nat) :
      ((List.range (X.tr g).length).map fun k => (X.writeClc i c).asyncSize (g,k)).sum=
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
      ((List.range (X.tr g).length).map fun k => (X.writeClc i c).asyncSize (g,k)).sum).sum+
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
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {c : Nat}

 theorem writeClc_observed {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.writeClc i c) j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  cases p <;> try exact Iff.rfl
  all_goals
    by_cases hj : j=i
    · simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
        Execution.writeClc,ite_eq_left hj]
      rfl
    · simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
        Execution.writeClc,ite_eq_right hj]
      rfl

 theorem writeClc_present_old {e : Ref} (he : e≠.async i (.write (.cta c))) :
    (X.writeClc i c).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hj : j=i
    · subst j
      cases p <;> try exact Iff.rfl
      case pos.writeCta d =>
        have hd : d≠c := by intro hd; subst d; exact he rfl
        simp [Execution.RefPresent,Execution.AsyncPresent,Execution.writeClc,hd]
      all_goals simp [Execution.RefPresent,Execution.AsyncPresent,Execution.writeClc]
    · cases p <;> simp [Execution.RefPresent,Execution.AsyncPresent,Execution.writeClc,hj]
      all_goals rfl

 theorem writeClc_finished {j w : EvId} {p : Part} :
    AsyncFinished L (X.writeClc i c) j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      forall₂_congr fun _ hq => writeClc_present_old fun h =>
        clcStage_not_groupWaitStage (.inr ⟨c, rfl⟩) hq (Ref.async.inj h).2)
    (exists_congr fun _ => and_congr_left' writeClc_observed)

 theorem writeClc_onlyFinished {j w : EvId} {p : Part} :
    AsyncOnlyFinished (X.writeClc i c) j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun _ hq => writeClc_present_old fun h =>
      clcStage_not_groupWaitStage (.inr ⟨c, rfl⟩) hq (Ref.async.inj h).2

 theorem writeClc_before {l : Loc} {a b : EvId × Part} :
    AsyncBefore L (X.writeClc i c) l a b ↔ AsyncBefore L X l a b := by
  simp only [AsyncBefore,writeClc_finished,writeClc_onlyFinished]
  rfl

 theorem writeClc_no_finished (hn : c∉(X.clc i).notified) (w : EvId) :
    ¬AsyncFinished L (X.writeClc i c) i (.write (.cta c)) w := by
  rintro (⟨k,hv,-⟩ | ⟨ws,⟨n,m,⟨-,s,targets,_,_,hnotify,_⟩,_⟩,_⟩)
  · cases k with
    | bulk mode => cases mode <;> simp [GroupWaitVisible] at hv
    | cpAsync => simp [GroupWaitVisible] at hv
  have hnotify' : c∈(X.clc i).notified := by
    simpa [Execution.writeClc] using hnotify
  exact hn hnotify'

 theorem writeClc_no_before (hn : c∉(X.clc i).notified)
    {l : Loc} {b : EvId × Part} :
    ¬AsyncBefore L (X.writeClc i c) l (i,.write (.cta c)) b := by
  rintro ⟨_,_,⟨w,hw,_⟩ | ⟨w,hw,_⟩⟩
  · exact writeClc_no_finished hn w hw
  · exact absurd hw.1 (by simp [GroupWaitVisible])

 theorem writeClc_modelCausality (hn : c∉(X.clc i).notified) {l : Loc} {e f : Ref} :
    modelCausality L (X.writeClc i c) l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  · exact Iff.rfl
  · exact Iff.rfl
  · simp only [modelCausality,writeClc_finished]
    rfl
  · refine and_congr_right fun _ => ?_
    apply AsyncChain.congr_on_edges (fun _ _ => writeClc_before)
    intro a b hedged
    have he : Ref.async a.1 a.2≠.async i (.write (.cta c)) := by
      intro he
      have ha : a=(i,.write (.cta c)) := by
        have h := Ref.async.inj he
        exact Prod.ext h.1 h.2
      rw [ha] at hedged
      exact writeClc_no_before hn hedged
    exact writeClc_present_old he

 theorem writeClc_no_visible (hn : c∉(X.clc i).notified) {l : Loc} {e : Ref} :
    ¬modelCausality L (X.writeClc i c) l (.async i (.write (.cta c))) e := by
  cases e with
  | thread j =>
    rintro ⟨_,w,hw,_⟩
    exact writeClc_no_finished hn w hw
  | async j p =>
    intro h
    obtain ⟨b,hb⟩ := AsyncChain.first h.2
    exact writeClc_no_before hn hb

 theorem writeClc_memWrites_old {e : Ref} {a : Acc} {bs : List Byte}
    (he : e≠.async i (.write (.cta c))) :
    (X.writeClc i c).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try exact Iff.rfl
    case writeCta d =>
      by_cases hj : j=i
      · subst j
        have hd : d≠c := by intro hd; subst d; exact he rfl
        simp [Execution.MemWrites,Clc.ResponseWrite,Execution.writeClc,hd] ; rfl
      · simp only [Execution.MemWrites,Execution.writeClc,ite_eq_right hj]
        rfl

 theorem writeClc_rf {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) : RfWf mem0 (X.writeClc i c) := by
  intro e a bs he
  obtain ⟨hlen,hvalues⟩ := hX.rf e a bs he
  refine ⟨hlen,?_⟩
  intro k hk
  have hv := hvalues k hk
  change match X.rf e k with | none => _ | some w => _
  cases hsrc : X.rf e k with
  | none => simp only [hsrc] at hv ⊢; exact hv
  | some w =>
    rw [hsrc] at hv
    obtain ⟨dst,bytes,hw,hcover,hval⟩ := hv
    exact ⟨dst,bytes,Execution.le_memWrites (writeClc_le X i c) hw,hcover,hval⟩

 theorem writeClc_hidden (hX : Hidden L X) (hn : c∉(X.clc i).notified) :
    Hidden L (X.writeClc i c) := by
  have reflect {l e f} : ByteCausality L (X.writeClc i c) l e f → ByteCausality L X l e f :=
    ByteCausality.of_same_context (X := X) (Y := X.writeClc i c) rfl rfl
      (fun h => (writeClc_modelCausality hn).mp h) (fun h => h)
  intro e a bs k w dst bytes he hk hw hc hv
  by_cases hwi : w=.async i (.write (.cta c))
  · subst w
    obtain ⟨_, edge⟩ := hv.starts
    exact (writeClc_no_visible hn edge).elim
  · have hold := hX e a bs k w dst bytes he hk (writeClc_memWrites_old hwi |>.mp hw) hc
      (reflect hv)
    change match X.rf e k with | none => False | some w' => _
    cases hsrc : X.rf e k with
    | none => simp only [hsrc] at hold
    | some w' =>
      simp only [hsrc] at hold
      exact fun hh => hold (reflect hh)

end
end PTX
end

section
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {c : Nat}

/-- Every node present in `X` is present after the response write. -/
theorem writeClc_present_mono (hn : c∉(X.clc i).written) {e : Ref} (h : X.RefPresent e) :
    (X.writeClc i c).RefPresent e := by
  by_cases he : e=.async i (.write (.cta c))
  · subst he
    exact (hn h).elim
  · exact (writeClc_present_old he).mpr h

/-- The response write has no present stage successor: its notification has not occurred. -/
theorem writeClc_no_next {s : Clc.Spec} {targets : List Nat} (hX : ClcOk L X)
    (hi : X.ClcIssue i s targets) (hn : c∉(X.clc i).written) (f : Ref) :
    ¬ StageEdge (X.writeClc i c) (.async i (.write (.cta c))) f := by
  intro h
  cases f with
  | thread j => exact h
  | async j q =>
    cases q <;> try exact h
    case notifyCta d =>
      obtain ⟨rfl, ht, -, hw⟩ := h
      simp only [Part.target, Option.some.injEq, Target.cta.injEq] at ht
      subst ht
      have hw' : c∈(X.clc i).notified := by
        simpa [Execution.AsyncPresent,Execution.writeClc] using hw
      exact writeClc_not_notified hX hi hn hw'
    all_goals
      obtain ⟨-, ht, -⟩ := h
      simp [Part.target] at ht

/-- The fresh response write is a sink of the execution order. -/
theorem writeClc_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0} {s : Clc.Spec}
    {targets : List Nat} (hX : Consistent L K A mem0 X) (hi : X.ClcIssue i s targets)
    (hn : c∉(X.clc i).written) :
    SinkFrame L K A X (X.writeClc i c) (fun n => n.1=.async i (.write (.cta c))) :=
  sinkFrame_clcStage (C := (X.writeClc i c).clc) hX.tma.2.2.1 hX.asyncObject hX.initFence
    (.inr ⟨c, rfl⟩) (fun _ he => writeClc_present_old he) (writeClc_no_next hX.clc hi hn)

theorem writeClc_objectAction {m : Loc} {e : Ref} :
    objectAction (X.writeClc i c) (X.writeClc i c).async m e=
      objectAction X X.async m e := by
  cases e with
  | thread j => rfl
  | async j p =>
    have hn : ((X.writeClc i c).clc j).notified=(X.clc j).notified := by
      by_cases hj : j=i <;> simp [Execution.writeClc,hj]
    cases p <;> try rfl
    case notifyCta d =>
      simp only [objectAction,hn]
      rfl

 theorem writeClc_tma (hX : TmaOk X) : TmaOk (X.writeClc i c) := by
  refine ⟨hX.1,hX.2.1,?_,hX.2.2.2⟩
  intro m
  obtain ⟨hc,hm,hcov⟩ := hX.2.2.1 m
  refine ⟨hc,?_,?_⟩
  · intro q hq
    have hh := hm q hq
    exact ⟨writeClc_objectAction.trans hh.1,hh.2⟩
  · intro e action he
    rw [writeClc_objectAction] at he
    exact hcov e action he

/-- A resolved request may write one unrecorded target replica without changing
any old read source. The fresh write is not yet published by a notification. -/
theorem consistent_writeClc_checked {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {s : Clc.Spec} {targets : List Nat} {response : ClcResponse}
    (hX : Consistent L K A mem0 X) (hi : X.ClcIssue i s targets)
    (hr : (X.clc i).resolved=some response) (hc : c∈targets)
    (hn : c∉(X.clc i).written)
    (hasm : ∀a∈A,a.wf L mem0 (X.writeClc i c)) :
    Consistent L K A mem0 (X.writeClc i c) := by
  have hnotify := writeClc_not_notified hX.clc hi hn
  have hord := (writeClc_sinkFrame hX hi hn).orderOk hX.orderOk
  exact { hX with
    clc := writeClc_clcOk hX.clc hi hr hc
    rf := writeClc_rf hX
    dependency := ⟨ready_congr
      (clc_needs (C := (X.writeClc i c).clc) hX.tma.2.2.1
        (fun _ he => writeClc_present_old he) (.inr ⟨c, rfl⟩))
      (fun _ h => h) (fun _ _ _ _ _ hx => writeClc_present_mono hn hx) hX.dependency.ready,
      hord.depAcyclic⟩
    observation := hord.observation
    object := hord.object
    asyncObject := hord.asyncObject
    initFence := hord.initFence
    noFuture := NoFuture.of_frame hX.noFuture (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.writeClc i c) rfl rfl
        (fun h => (writeClc_modelCausality hnotify).mp h) (fun h => h))
    hidden := writeClc_hidden hX.hidden hnotify
    tcRead := (TcMma.readOk_clc X.clcState _).mpr hX.tcRead
    tma := writeClc_tma hX.tma
    reduce := ⟨hX.reduce.values, hX.reduce.copies⟩
    atomic := ⟨hX.atomic.unique, hX.atomic.acyclic⟩
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, hX.fenceSc.causal⟩
    asm := hasm }

end
end PTX
end
