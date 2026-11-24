-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorStoreCompleteConsistent
public import Lemmas.Async.AsyncChain
public import Lemmas.Order.Order

@[expose] public section

namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
  {rf : Ref → Nat → Option Ref}
local notation "Y" => X.recordStoreEffects i o rf

theorem store_unfinished_no_readDone {X : Execution} {i : EvId}
    (hn : (X.tensorStores i).any (fun old => old.effects.readsDone)=false) :
    ¬X.AsyncPresent i .readsDone := by
  rintro ⟨old,ho,hdone⟩
  simp [ho,hdone] at hn

theorem store_unfinished_no_fullDone {X : Execution} {i : EvId}
    (hn : (X.tensorStores i).any (fun old => old.effects.fullDone)=false) :
    ¬X.AsyncPresent i .fullDone := by
  rintro ⟨old,ho,hdone⟩
  simp [ho,hdone] at hn

theorem storeByteFrame_readDone
    (hold : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    (hn : o.effects.readsDone=false) (j : EvId) :
    (Y).AsyncPresent j .readsDone ↔ X.AsyncPresent j .readsDone := by
  by_cases hj : j=i
  · subst j
    exact ⟨fun h => (store_unfinished_no_readDone
      (by simp [Execution.recordStoreEffects,hn]) h).elim,
      fun h => (store_unfinished_no_readDone hold h).elim⟩
  · simp only [Execution.AsyncPresent,Execution.recordStoreEffects,ite_eq_right hj]

theorem storeByteFrame_fullDone
    (hold : (X.tensorStores i).any (fun old => old.effects.fullDone)=false)
    (hn : o.effects.fullDone=false) (j : EvId) :
    (Y).AsyncPresent j .fullDone ↔ X.AsyncPresent j .fullDone := by
  by_cases hj : j=i
  · subst j
    exact ⟨fun h => (store_unfinished_no_fullDone
      (by simp [Execution.recordStoreEffects,hn]) h).elim,
      fun h => (store_unfinished_no_fullDone hold h).elim⟩
  · simp only [Execution.AsyncPresent,Execution.recordStoreEffects,ite_eq_right hj]

/-- The stages that a group wait waits for are the completion flags, whose presence is unchanged,
and the copy stages. -/
theorem storeByteFrame_groupPresent
    (holdR : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    (holdF : (X.tensorStores i).any (fun old => old.effects.fullDone)=false)
    (hnR : o.effects.readsDone=false) (hnF : o.effects.fullDone=false) (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages Y j k, (Y).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl
    · exact storeByteFrame_readDone holdR hnR j
    · exact storeByteFrame_fullDone holdF hnF j
    · exact Iff.rfl
    · exact Iff.rfl

theorem storeByteFrame_finished
    (holdR : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    (holdF : (X.tensorStores i).any (fun old => old.effects.fullDone)=false)
    (hnR : o.effects.readsDone=false) (hnF : o.effects.fullDone=false)
    (j : EvId) (p : Part) (w : EvId) :
    AsyncFinished L Y j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
    storeByteFrame_groupPresent holdR holdF hnR hnF j k) Iff.rfl

theorem storeByteFrame_onlyFinished
    (holdR : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    (holdF : (X.tensorStores i).any (fun old => old.effects.fullDone)=false)
    (hnR : o.effects.readsDone=false) (hnF : o.effects.fullDone=false)
    (j : EvId) (p : Part) (w : EvId) :
    AsyncOnlyFinished Y j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ =>
    storeByteFrame_groupPresent holdR holdF hnR hnF j _

theorem storeByteFrame_covers (j : EvId) (p : Part) (l : Loc) :
    AsyncCovers Y j p l ↔ AsyncCovers X j p l := by cases p <;> rfl

theorem storeByteFrame_present_other {j : EvId} {p : Part} (hj : j≠i) :
    (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  all_goals simp only [Execution.AsyncPresent,Execution.recordStoreEffects,ite_eq_right hj]

theorem storeByteFrame_chain
    (holdR : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    (holdF : (X.tensorStores i).any (fun old => old.effects.fullDone)=false)
    (hnR : o.effects.readsDone=false) (hnF : o.effects.fullDone=false)
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (l : Loc) (a b : EvId × Part) : AsyncChain L Y l a b ↔ AsyncChain L X l a b := by
  have hd (a b : EvId × Part) : AsyncBefore L Y l a b ↔ AsyncBefore L X l a b :=
    AsyncBefore.congr (fun j p => storeByteFrame_covers j p l)
      (storeByteFrame_finished holdR holdF hnR hnF)
      (storeByteFrame_onlyFinished holdR holdF hnR hnF)
      (fun _ _ _ _ => recordStoreEffects_baseCausality_iff hrf) (fun _ _ _ _ => Iff.rfl)
  apply AsyncChain.congr_on_edges hd
  rintro ⟨j,p⟩ b hedge
  by_cases hj : j=i
  · subst j
    -- A group wait waits for the read completion of a tensor store, which is absent.
    have hgroup : ∀ k, (∃ pc addr s, X.get i = some ⟨pc, .tensorStore addr s⟩) →
        ¬ ∀ q ∈ GroupWaitStages Y i k, (Y).AsyncPresent i q := by
      rintro k ⟨pc, addr, s, hg⟩ hall
      refine store_unfinished_no_readDone (X := Y) (by simp [Execution.recordStoreEffects,hnR])
        (hall .readsDone ?_)
      change Part.readsDone ∈ GroupWaitStages X i k
      unfold GroupWaitStages
      rw [hg]
      rcases k with ⟨_ | _ | _⟩ | _ <;> simp
    cases p <;> try exact Iff.rfl
    all_goals first
      | (obtain ⟨acc,w,hi,_⟩ := hedge.1; exact (show False from hi.2).elim)
      | (obtain ⟨acc,w',⟨-,s,addr,⟨pc,hg⟩,-⟩,-⟩ := hedge.1
         exfalso
         rcases hedge.2.2 with ⟨w,⟨k,-,-,hall⟩ | ⟨ws,⟨n,m,hN,-⟩,-⟩,-⟩ | ⟨w,⟨-,-,hall⟩,-⟩
         · exact hgroup k ⟨pc, addr, s, hg⟩ hall
         · exact hN
         · exact hgroup _ ⟨pc, addr, s, hg⟩ hall)
  · exact storeByteFrame_present_other hj

theorem storeByteFrame_modelCausality
    (holdR : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    (holdF : (X.tensorStores i).any (fun old => old.effects.fullDone)=false)
    (hnR : o.effects.readsDone=false) (hnF : o.effects.fullDone=false)
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (l : Loc) (e f : Ref) : modelCausality L Y l e f ↔ modelCausality L X l e f := by
  cases e with
  | thread e =>
    cases f with
    | thread f => exact or_congr (recordStoreEffects_baseCausality_iff hrf) Iff.rfl
    | async j p =>
      have hc := storeByteFrame_covers (X:=X) (i:=i) (o:=o) (rf:=rf) j p l
      simp only [modelCausality,hc]
      unfold ProxyBefore
      simp only [recordStoreEffects_baseCausality_iff hrf]
      rfl
  | async j p =>
    cases f with
    | thread f =>
      have hc := storeByteFrame_covers (X:=X) (i:=i) (o:=o) (rf:=rf) j p l
      have hp : ∀ e f, ProxyBefore L Y e f l ↔ ProxyBefore L X e f l := by
        intro e f
        unfold ProxyBefore
        simp only [recordStoreEffects_baseCausality_iff hrf]
        rfl
      have hcb (w : EvId) :
          ObservedCompletionBefore L Y l j p w f ↔
            ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr rfl rfl (recordStoreEffects_baseCausality_iff hrf) (hp w f)
      simp only [modelCausality,hc,storeByteFrame_finished holdR holdF hnR hnF,hcb]
    | async k q =>
      exact and_congr_right fun _ => storeByteFrame_chain holdR holdF hnR hnF hrf l (j,p) (k,q)

end
end PTX
