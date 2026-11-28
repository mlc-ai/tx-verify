-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Staged.Early
public import Lemmas.Kernel.Source.WarpColl

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- Before the first shuffle a transition either ends the lane or stays in startup. -/
private theorem before_step (s : Startup.D) (e : Event) (hn : Execution.isShfl e = false) :
    Startup.succ L g s e = none ∨ ∃ t, Startup.succ L g s e = some (some t) ∧
      Startup.enterOf t = none := by
  obtain ⟨pc,kind⟩ := e
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> simp only [Startup.succ]
  all_goals repeat' split
  all_goals first | exact .inl rfl | exact .inr ⟨_,rfl,rfl⟩ |
    simp_all [Execution.isShfl]

/-- A prefix containing no shuffle has yet to cross the startup handoff. -/
private theorem before_first (hc : ((X.tr g).take k).countP Execution.isShfl = 0) :
    Frame.stateAt (thread Q L) X g k = none ∨ ∃ s n,
      Frame.stateAt (thread Q L) X g k = some (some (.inl s,n)) ∧ Startup.enterOf s = none := by
  induction k with
  | zero =>
    refine .inr ⟨Startup.init L g,fun _ => 0,?_,enterOf_init⟩
    rw [Frame.stateAt_zero]
    change some (some (Code.enter _ _ _ _,_)) = _
    rw [enter_inl enterOf_init]
  | succ k ih =>
    by_cases hk : (X.tr g).length ≤ k
    · have hk' : (X.tr g).length ≤ k+1 := by omega
      rw [List.take_of_length_le hk'] at hc
      have ih' := ih (by rwa [List.take_of_length_le hk])
      rwa [Frame.stateAt_of_le hk, ←Frame.stateAt_of_le (k := k+1) hk'] at ih'
    have he := List.getElem?_eq_getElem (l := X.tr g) (i := k) (by omega)
    rw [List.take_add_one,he,Option.toList_some,List.countP_append,List.countP_singleton] at hc
    rcases ih (by omega) with dead | ⟨s,n,live,-⟩
    · left
      rw [Frame.stateAt_succ he,dead]
      rfl
    have hn : Execution.isShfl ((X.tr g)[k]) = false := by split at hc <;> simp_all
    rcases before_step (L := L) (g := g) s _ hn with dead | ⟨t,ht,active⟩
    · left
      rw [Frame.stateAt_succ he,live]
      change (thread Q L g).next _ _ = _
      rw [next_start,dead]
      rfl
    · refine .inr ⟨t,Code.bump cls n ((X.tr g)[k]),?_,active⟩
      rw [Frame.stateAt_succ he,live]
      exact to_state ht active

private theorem first_kind (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {e : Event} (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hc : ((X.tr g).take k).countP Execution.isShfl = 0) :
    e.kind ≠ .exit ∧ (Execution.isShfl e = true →
      ∃ recv ok, e = ⟨17,.shfl .idx (b32 (g%L.block/32)) 0 31 recv ok⟩) := by
  rcases before_first (Q := Q) hc with dead | ⟨s,n,live,active⟩
  · rcases Frame.firedU (fun g hg => thread_sound hp hg) hX he with ⟨_,_,hs,-⟩ | ⟨-,pc,f,hf⟩
    · rw [dead] at hs
      cases hs
    · exact absurd (by rw [hf]) (hu f)
  have ev := start_ev hp hX he live hu
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> simp only [Startup.Ev] at ev
  · subst ev; exact ⟨by simp,by simp [Execution.isShfl]⟩
  · obtain ⟨_,_,rfl⟩ := ev; exact ⟨by simp,by simp [Execution.isShfl]⟩
  · subst ev; exact ⟨by simp,by simp [Execution.isShfl]⟩
  · obtain ⟨_,_,rfl,-⟩ := ev; exact ⟨by simp,by simp [Execution.isShfl]⟩
  · subst ev; exact ⟨by simp,by simp [Execution.isShfl]⟩
  · subst ev; exact ⟨by simp,by simp [Execution.isShfl]⟩
  · obtain ⟨recv,ok,rfl⟩ := ev; exact ⟨by simp,fun _ => ⟨recv,ok,rfl⟩⟩
  · cases active

/-- The first shuffle receives its own warp index. The source is still in startup
at ordinal zero, including when considering the alternative of an early exit. -/
theorem startup_recv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {recv : Value} {ok : Bool}
    (he : X.get (g,k) = some ⟨17,.shfl .idx (b32 (g%L.block/32)) 0 31 recv ok⟩)
    (hc : ((X.tr g).take k).countP Execution.isShfl = 0) : recv = b32 (g%L.block/32) := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have sl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨-,warp,-⟩ := Frame.lane_facts hb (Frame.lt_of_get hX he) rfl sl
  obtain ⟨-,src | exited⟩ := hX.shfl _ _ 0 _ _ _ _ _ _ _ he ⟨⟨_,_,_,_,_,_,_,he⟩,hc⟩
  · obtain ⟨j,pc,b,c,r,o,ord,source⟩ := src
    obtain ⟨recv',ok',eq⟩ := (first_kind hp hX source (by simp) ord.2).2 rfl
    simp only [Event.mk.injEq,Kind.shfl.injEq] at eq
    obtain ⟨-, -, val,-⟩ := eq
    rw [val,warp]
  · obtain ⟨j,pc,ex,ord⟩ := exited
    exact ((first_kind hp hX ex (by simp) (by omega)).1 rfl).elim

end
end PTX.Kernels.InklingRelDecode.Proof
