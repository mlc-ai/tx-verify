-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Common.FollowHead
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

private theorem child_prev {K A L g} {P : Code K A L g} {ι} {R : ι → Code K A L g}
    {exit : P.D → Option ι} {s e i d} (later : d≠(R i).init)
    (step : (P.glue R exit).next s e=some (some (.inr ⟨i,d⟩))) :
    ∃ old, s=.inr ⟨i,old⟩ ∧ (R i).next old e=some (some d) := by
  rcases s with s|⟨j,s⟩
  · obtain ⟨_,_,eq⟩ := Code.glue_inl_some step
    unfold Code.enter at eq
    split at eq <;> cases eq
    exact (later rfl).elim
  · obtain ⟨_,move,eq⟩ := Code.glue_inr_some step
    cases eq
    exact ⟨s,rfl,move⟩

private theorem epi_pred {Q L g w ent d n ev s} (later : d≠{})
    (step : (thread Q L g).next s ev=some (some (epiState w ent d n))) :
    ∃ old cnt, s=epiState w ent old cnt ∧
      Epilogue.Control.next (epiEntry ent (g%L.block)) L g old ev=some (some d) := by
  obtain ⟨s,cnt⟩ := s
  have outer := (Code.counted_next_some step).1
  obtain ⟨sub,rfl,hs⟩ := child_prev (by intro bad; contradiction) outer
  obtain ⟨soft,rfl,ht⟩ := child_prev (by intro bad; contradiction) hs
  obtain ⟨old,rfl,move⟩ := child_prev later ht
  exact ⟨old,cnt,rfl,move⟩

/-- Recover a local step into a noninitial Softmax state, before the epilogue handoff. -/
private theorem soft_pred {Q L g w ent d n ev s} (later : d≠{})
    (step : (thread Q L g).next s ev=some (some (softState w ent d n))) :
    ∃ old cnt, s=softState w ent old cnt ∧
      Softmax.Control.next ent L g old ev=some (some d) := by
  obtain ⟨s,cnt⟩ := s
  have outer := (Code.counted_next_some step).1
  obtain ⟨sub,rfl,hs⟩ := child_prev (by intro bad; contradiction) outer
  obtain ⟨old,rfl,ht⟩ := child_prev (by intro bad; exact later (Sum.inl.inj bad)) hs
  rcases old with old|⟨_,old⟩
  · obtain ⟨dn,move,eq⟩ := Code.glue_inl_some ht
    unfold Code.enter at eq
    split at eq <;> cases eq
    exact ⟨old,cnt,rfl,move⟩
  · obtain ⟨_,_,eq⟩ := Code.glue_inr_some ht
    cases eq

private theorem trace_pred {Q L g X k} {state : (thread Q L g).D}
    (hk : k≤(X.tr g).length) (later : state≠(thread Q L g).init)
    (live : Frame.stateAt (thread Q L) X g k=some (some state)) :
    ∃ u s ev, u+1=k ∧ Frame.stateAt (thread Q L) X g u=some (some s) ∧
      X.get (g,u)=some ev ∧ (thread Q L g).next s ev=some (some state) := by
  cases k with
  | zero =>
    rw [Frame.stateAt_zero] at live
    exact (later (Option.some.inj (Option.some.inj live)).symm).elim
  | succ u =>
    have get := List.getElem?_eq_getElem (l := X.tr g) (i := u) (by omega)
    rw [Frame.stateAt_succ get] at live
    rcases prev : Frame.stateAt (thread Q L) X g u with _|_|s <;> rw [prev] at live <;>
      try solve | cases live
    exact ⟨u,s,_,rfl,prev,get,live⟩

private theorem start_fst {Q L g} : (thread Q L g).init.1=Sum.inl (Startup.init L g) :=
  enter_inl enterOf_init

/-- Inverting the nested handoffs preserves the actual event and trace index. -/
theorem epi_prev {Q L g X w ent k d n} (hk : k≤(X.tr g).length) (later : d≠{})
    (live : Frame.stateAt (thread Q L) X g k=some (some (epiState w ent d n))) :
    ∃ u old cnt ev, u+1=k ∧ Frame.stateAt (thread Q L) X g u=some (some (epiState w ent old cnt))
      ∧ X.get (g,u)=some ev ∧ Epilogue.Control.next (epiEntry ent (g%L.block)) L g old ev=
        some (some d) := by
  obtain ⟨u,s,ev,eq,prev,get,next⟩ := trace_pred hk (by
    intro h
    have bad := (congrArg Prod.fst h).trans start_fst
    cases bad) live
  obtain ⟨old,cnt,rfl,move⟩ := epi_pred later next
  exact ⟨u,old,cnt,ev,eq,prev,get,move⟩

/-- Inverting the nested handoffs preserves the actual event and trace index. -/
theorem soft_prev {Q L g X w ent k d n} (hk : k≤(X.tr g).length) (later : d≠{})
    (live : Frame.stateAt (thread Q L) X g k=some (some (softState w ent d n))) :
    ∃ u old cnt ev, u+1=k ∧ Frame.stateAt (thread Q L) X g u=some (some (softState w ent old cnt))
      ∧ X.get (g,u)=some ev ∧ Softmax.Control.next ent L g old ev=
        some (some d) := by
  obtain ⟨u,s,ev,eq,prev,get,next⟩ := trace_pred hk (by
    intro h
    have bad := (congrArg Prod.fst h).trans start_fst
    cases bad) live
  obtain ⟨old,cnt,rfl,move⟩ := soft_pred later next
  exact ⟨u,old,cnt,ev,eq,prev,get,move⟩

end PTX.Kernels.InklingRelDecode.Proof
