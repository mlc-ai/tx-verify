-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Execution.ShapeExecution

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption

/-- The decoded branch stays above the given instruction boundary. -/
def staysPastEvent (floor : Nat) : Op → Bool
  | .bra dst _ => decide (floor ≤ dst)
  | .brx .. => false
  | _ => true

private theorem ordinaryEventCode :
    kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by
  decide +kernel

variable {l : Launch}

private theorem eventTailStepOfCode {g : Nat} {s u : TState} {e : Option Event} {floor : Nat}
    (hTail : ∀ ins, kernel.code[s.pc]? = some ins → staysPastEvent floor ins.op = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop) (hp : floor ≤ s.pc)
    (hs : WStep kernel Assumptions.all l g s e u) : floor ≤ u.pc := by
  rcases hs with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨ins, hCode, _, hExec⟩ := Softmax.tauScoreSource ht
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact hp.trans (Nat.le_succ _)
    · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg, hSite, hMatch, hSeg⟩
      · have hAudit := hTail _ hCode
        have hNext := hFrame.pc
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
        case bra dst uni => simpa only [staysPastEvent, hop, decide_eq_true_eq, hNext] using hAudit
        case brx => simp [hop, staysPastEvent] at hAudit
        all_goals omega
      · exact (Softmax.scoreSegmentFrame hSeg).1.symm ▸ hSegments _ hp hSite seg hMatch
  · obtain ⟨ins, hCode, hNoLocal, hFire⟩ := estep_event_source he
    have hAudit := List.all_eq_true.mp ordinaryEventCode ins (List.mem_of_getElem? hCode)
    have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hNoLocal, Bool.false_or] using hAudit)
    rcases callbackFrame_fires hFrame hFire with hNext | hSame <;> omega

private theorem eventTailStep {g : Nat} {s u : TState} {e : Option Event} {floor : Nat}
    (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop) (hp : floor ≤ s.pc)
    (hs : WStep kernel Assumptions.all l g s e u) : floor ≤ u.pc :=
  eventTailStepOfCode (fun ins hIns => by
    have hm : ins ∈ kernel.code.drop floor := by
      apply List.mem_of_getElem? (i := s.pc - floor)
      rwa [List.getElem?_drop, Nat.add_sub_of_le hp]
    exact List.all_eq_true.mp hTail ins hm) hSegments hp hs

/-- Events in a checked suffix stay above a floor respected by the segments reached there. -/
theorem eventTailEventsOfSegmentFloor {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {floor : Nat}
    (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop)
    (hw : Walk kernel Assumptions.all l g s events visits) (hp : floor ≤ s.pc)
    : ∀ e ∈ events, floor ≤ e.pc := by
  induction hw with
  | stop => simp
  | tau h _ ih => exact ih (eventTailStep hTail hSegments hp (.inl ⟨rfl, h⟩))
  | ev h _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (estep_source_pc h).symm ▸ hp
    · exact ih (eventTailStep hTail hSegments hp (.inr ⟨_, rfl, h⟩)) e he
  | last h =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact (estep_source_pc h).symm ▸ hp

/-- A checked span keeps its recorded events above the branch floor. The walk's
visit bound lets the instruction audit end at the next checkpoint. -/
theorem eventTailEventsInSpan {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    {floor stop : Nat}
    (hTail : ((kernel.code.drop floor).take (stop - floor)).all
      (fun i => staysPastEvent floor i.op) = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop)
    (hw : Walk kernel Assumptions.all l g s events visits) (hScope : ∀ v ∈ visits, v.pc < stop)
    (hp : floor ≤ s.pc) :
    ∀ e ∈ events, floor ≤ e.pc := by
  have step {t u : TState} {ev : Option Event} (hLo : floor ≤ t.pc) (hHi : t.pc < stop)
      (hs : WStep kernel Assumptions.all l g t ev u) : floor ≤ u.pc := by
    apply eventTailStepOfCode _ hSegments hLo hs
    intro ins hCode
    have hm : ins ∈ (kernel.code.drop floor).take (stop - floor) := by
      apply List.mem_of_getElem? (i := t.pc - floor)
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact List.all_eq_true.mp hTail ins hm
  induction hw with
  | stop => simp
  | tau ht _ ih =>
    exact ih (fun v hv => hScope v (List.mem_cons_of_mem _ hv))
      (step hp (hScope _ List.mem_cons_self) (.inl ⟨rfl,ht⟩))
  | ev he _ ih =>
    intro e hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · exact (estep_source_pc he).symm ▸ hp
    · exact ih (fun v hv => hScope v (List.mem_cons_of_mem _ hv))
        (step hp (hScope _ List.mem_cons_self) (.inr ⟨_,rfl,he⟩)) e hMem
  | last he =>
    intro e hMem
    obtain rfl := List.mem_singleton.mp hMem
    exact (estep_source_pc he).symm ▸ hp

private theorem segmentFloorOfAudit {floor : Nat}
    (hAudit : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true) :
    ∀ site ∈ Assumptions.swExp2Sites, ∀ seg,
      cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop := by
  intro site hSite seg hMatch
  have h := List.all_eq_true.mp hAudit _ hSite
  rw [hMatch] at h
  exact of_decide_eq_true h

/-- A returning step respects a checked branch and segment floor. -/
theorem eventTailStepOfAudit {g : Nat} {s u : TState} {e : Option Event} {floor : Nat}
    (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true) (hp : floor ≤ s.pc) (hs : WStep kernel Assumptions.all l g s e u)
    : floor ≤ u.pc :=
  eventTailStep hTail (fun site _ => segmentFloorOfAudit hSegments site) hp hs

/-- Events in a checked suffix stay at or above its decoded branch floor. -/
theorem eventTailEvents {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    {floor : Nat} (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true) (hw : Walk kernel Assumptions.all l g s events visits)
    (hp : floor ≤ s.pc) :
    ∀ e ∈ events, floor ≤ e.pc :=
  eventTailEventsOfSegmentFloor hTail (fun site _ => segmentFloorOfAudit hSegments site) hw hp

private theorem noEarlyEventAfterFloor {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {floor : Nat}
    (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop)
    (hw : Walk kernel Assumptions.all l g s events visits) {score query : Event}
    (hScore : floor ≤ score.pc) (hQuery : query.pc < floor) {i j : Nat}
    (hi : events[i]? = some score) (hj : events[j]? = some query) : j < i := by
  induction hw generalizing i j with
  | stop => simp at hi
  | tau _ _ ih => exact ih hi hj
  | ev h hw ih =>
    cases i with
    | zero =>
      have hEqual := Option.some.inj hi
      have hp := (estep_source_pc h).symm ▸ (hEqual.symm ▸ hScore)
      cases j with
      | zero =>
        have hPc := congrArg Event.pc (Option.some.inj (hi.symm.trans hj))
        omega
      | succ j =>
        have hMem := List.mem_of_getElem? (List.getElem?_cons_succ.symm.trans hj)
        have hNext := eventTailStep hTail hSegments
          hp (.inr ⟨_, rfl, h⟩)
        have hBound := eventTailEventsOfSegmentFloor hTail hSegments hw hNext _ hMem
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact Nat.succ_lt_succ (ih
          (List.getElem?_cons_succ.symm.trans hi) (List.getElem?_cons_succ.symm.trans hj))
  | last _ =>
    cases i <;> cases j <;> simp_all
    omega

/-- If all returning transitions stay above a boundary, a recorded event below it
preceded a recorded event at or above it in the same lane. -/
theorem traceOrderOfSegmentFloor {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {floor : Nat}
    (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : ∀ site, floor ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop) {g early late : Nat}
    {first last : Event} (hFirst : X.get (g,early) = some first)
    (hLast : X.get (g,late) = some last) (hLo : first.pc < floor) (hHi : floor ≤ last.pc)
    : early < late := by
  have hg := event_thread_lt hX hFirst
  obtain ⟨_, hRun⟩ := hX.thr g hg
  obtain ⟨_, hw⟩ := Mma.walkFromRun hRun
  exact noEarlyEventAfterFloor hTail hSegments hw hHi hLo hLast hFirst

/-- If all returning transitions stay above a boundary, a recorded event below it
preceded a recorded event at or above it in the same lane. -/
theorem traceOrderOfPcFloor {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {floor : Nat}
    (hTail : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true) {g early late : Nat} {first last : Event}
    (hFirst : X.get (g,early) = some first) (hLast : X.get (g,late) = some last)
    (hLo : first.pc < floor) (hHi : floor ≤ last.pc) : early < late :=
  traceOrderOfSegmentFloor hX hTail (fun site _ => segmentFloorOfAudit hSegments site)
    hFirst hLast hLo hHi

end PTX.Kernels.TmlFa4Fwd.Thread
