-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Coverage
public import Kernels.FlashKdaFwd.Packed.Producer.Guard
public import Kernels.FlashKdaFwd.Packed.Prefix
public import Lemmas.Flow.ContinuingEvent

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.EventFrame

theorem reachable {base : Nat → Nat → Nat} {L : Launch} {g : Nat} {t u : TState}
    {es : List Event} (tid : (L.tidOf g).x = 129)
    (path : Flow.TraceReach kernel (Prologue.assumptions base) L g t es u)
    (init : Facts t) : Facts u := by
  induction path with
  | refl => exact init
  | @tau s _ _ _ h _ ih =>
    apply ih
    by_cases guard : special s.pc
    · exact tau_special base tid init guard h
    · exact tau_ordinary base init guard (fun _ p => (certified p).1) h
  | @event s _ _ _ _ h _ ih =>
    by_cases guard : special s.pc
    · exact (no_guard_event base guard h).elim
    · exact ih (event_ordinary base init guard (fun _ p => (certified p).1) h)

theorem elected_suffix (base : Nat → Nat → Nat) (L : Launch) (v : BitVec 64)
    (host : L.params (Prologue.param 15) = some v) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) {es : List Event} {o : Option TState}
    (trace : Run kernel (Prologue.assumptions base) L 129 {}
      (⟨32,.elect 0xffffffff 0 1⟩ :: es) o) {i : Nat} {e : Event}
    (event : es[i]? = some e) : allowed e.pc := by
  obtain ⟨t,u,one,steps,pc,_,flag⟩ :=
    Entry.selected_lane base L ⟨1,by decide⟩ v host block threads
  have tid : (L.tidOf 129).x = 129 := by rw [Launch.tidOf,block,threads]; rfl
  cases trace with
  | last => simp at event
  | step silent fire rest =>
    have same : some _ = some t := (Run.step silent fire (.nil _)).det one
    cases Option.some.inj same
    have rest' := rest.after_local_nonempty (run_rtg steps)
      (fun empty => by simp [empty] at event)
    obtain ⟨s,_,path,fired⟩ := rest'.before_event event
    rw [estep_source_pc fired]
    exact (reachable tid path (start pc flag)).position

theorem excluded_copies (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0) (X : Execution)
    (v : BitVec 64) (host : L.params (Prologue.param 15) = some v) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (ctas : 0 < L.grid)
    (consistent : Consistent L kernel (Prologue.assumptions base) mem X)
    (elected : X.Elect (129,0) 32 0xffffffff 0 1) {j : Nat} {e : Event}
    (event : X.get (129,j) = some e) :
    ¬ ((1456 ≤ e.pc ∧ e.pc < 1863) ∨ (1882 ≤ e.pc ∧ e.pc < 2072)) := by
  obtain ⟨o,trace⟩ := consistent.thr 129 (by unfold Launch.threads; rw [block]; omega)
  change (X.tr 129)[0]? = some _ at elected
  change (X.tr 129)[j]? = some e at event
  cases history : X.tr 129 with
  | nil => simp [history] at elected
  | cons first es =>
    simp only [history,List.getElem?_cons_zero,Option.some.injEq] at elected
    subst first
    rw [history] at trace event
    cases j with
    | zero => cases event; decide
    | succ i =>
      have facts := elected_suffix base L v host block threads trace event
      unfold allowed at facts
      omega

theorem completion_without_copies (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (post : FinalMem → Prop) (correct : Correct kernel (Prologue.assumptions base) L mem post)
    (v : BitVec 64) (host : L.params (Prologue.param 15) = some v) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) (ctas : 0 < L.grid) (grid : L.clusterGridValid) :
    ∃ X, Consistent L kernel (Prologue.assumptions base) mem X ∧ Complete L X ∧
      X.Elect (129,0) 32 0xffffffff 0 1 ∧ ∀ j e, X.get (129,j) = some e →
        ¬ ((1456 ≤ e.pc ∧ e.pc < 1863) ∨ (1882 ≤ e.pc ∧ e.pc < 2072)) := by
  let lane : Fin 32 := ⟨1,by decide⟩
  obtain ⟨X,valid,complete,first⟩ :=
    Entry.completion_with_leader base L mem post correct lane v host block threads ctas grid
  exact ⟨X,valid,complete,first lane,fun _ _ =>
    excluded_copies base L mem X v host block threads ctas valid (first lane)⟩

end FlashKda.Packed.ProducerControl
