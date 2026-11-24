-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue

noncomputable section

private def finalTail (pc : Nat) : Prop :=
  (7742 ≤ pc ∧ pc ≤ 7747) ∨ pc = 9205

private instance (pc : Nat) : Decidable (finalTail pc) :=
  inferInstanceAs (Decidable ((7742 ≤ pc ∧ pc ≤ 7747) ∨ pc = 9205))

private def tailControl (i : Instr) (pc : Nat) : Bool :=
  (i.guard.isNone || decide (finalTail (pc+1))) &&
    (!i.op.isLocal || match i.op with
      | .brx .. => false
      | _ => decide (finalTail (nextPc i.op pc))) &&
    (i.op.isLocal || decide (pc = 7746 ∨ pc = 7747 ∨ pc = 9205))

private theorem tailCode {pc : Nat} {i : Instr}
    (hp : finalTail pc) (hc : kernel.code[pc]? = some i) : tailControl i pc = true := by
  rcases hp with h | rfl
  · have hAll : (((kernel.code.drop 7742).take 6).zipIdx 7742).all
        (fun (ins,j) => tailControl ins j) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    apply List.all_eq_true.mp hAll (i,pc)
    apply List.mem_of_getElem? (i := pc - 7742)
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le h.1,hc]
    rfl
  · rw [Flow.code_9205] at hc
    obtain rfl := Option.some.inj hc
    rfl

private theorem tailTau {l : Launch} {g : Nat} {s u : TState}
    (hs : finalTail s.pc) (h : Tau kernel Assumptions.all l g s u) : finalTail u.pc := by
  obtain ⟨i, hc, _, hStep⟩ := Softmax.tauScoreSource h
  have hCode := tailCode hs hc
  simp only [tailControl, Bool.and_eq_true] at hCode
  rcases hStep with ⟨rfl, hGuard⟩ | ⟨_, hLocal, hExec⟩
  · have hSkip := hCode.1.1
    simp only [Bool.or_eq_true] at hSkip
    rcases hSkip with h | h
    · rw [Option.isNone_iff_eq_none.mp h] at hGuard
      cases hGuard
    · exact of_decide_eq_true h
  · rcases Softmax.scoreExecLocal hExec with hFrame | ⟨_, hSite, _, _⟩
    · have hOp := hCode.1.2
      simp only [hLocal, Bool.not_true, Bool.false_or] at hOp
      have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, BrxTarget, or_false] at hOp hPc
      all_goals first | cases hOp | exact hPc.symm ▸ (of_decide_eq_true hOp)
    · rcases hs with h | h <;>
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite <;>
        omega

private theorem tailLocal {l : Launch} {g : Nat} {s u : TState}
    (hs : finalTail s.pc) (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    finalTail u.pc := by
  induction ht with
  | refl => exact hs
  | tail _ h ih => exact tailTau ih h

private theorem tailCannotContinueAtExit {l : Launch} {g : Nat} {s u : TState} {ev : Event}
    (hp : s.pc = 9205) (he : EStep kernel Assumptions.all l g s ev (some u)) : False := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [hp, Flow.code_9205] at hc
  obtain rfl := Option.some.inj hc
  cases hf.2

private theorem returnLocals {l : Launch} {g : Nat} {s u : TState}
    (hp : s.pc = 9205) (h : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    u = s := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨_, ht, _⟩
  · rfl
  · obtain ⟨ins, hc, _, hStep⟩ := Softmax.tauScoreSource ht
    rw [hp, Flow.code_9205] at hc
    obtain rfl := Option.some.inj hc
    rcases hStep with ⟨_, hg⟩ | ⟨_, hc, _⟩
    · cases hg
    · cases hc

private theorem firstAfterReturn {l : Launch} {g : Nat} {s : TState} {e : Event}
    {es : List Event} {o : Option TState} (hp : s.pc = 9205)
    (hr : Run kernel Assumptions.all l g s (e :: es) o) : e.pc = 9205 := by
  cases hr with
  | step hLocal he _ =>
    obtain rfl := returnLocals hp hLocal
    exact (tailCannotContinueAtExit hp he).elim
  | last hLocal he =>
    obtain rfl := returnLocals hp hLocal
    exact (estep_source_pc he).trans hp

private theorem firstTailEvent {l : Launch} {g : Nat} {s : TState} {e : Event}
    {es : List Event} {o : Option TState} (hs : finalTail s.pc)
    (hr : Run kernel Assumptions.all l g s (e :: es) o) :
    (e.pc = 7746 ∨ e.pc = 7747) ∨ (es = [] ∧ finalTail e.pc) := by
  cases hr with
  | step hLocal he _ =>
    have hTail := tailLocal hs hLocal
    obtain ⟨ins, hc, hNotLocal, _⟩ := estep_event_source he
    have hCode := tailCode hTail hc
    simp only [tailControl, Bool.and_eq_true, hNotLocal, Bool.false_or] at hCode
    rcases of_decide_eq_true hCode.2 with h | h | h
    · exact .inl (.inl ((estep_source_pc he).trans h))
    · exact .inl (.inr ((estep_source_pc he).trans h))
    · exact (tailCannotContinueAtExit h he).elim
  | last hLocal he =>
    exact .inr ⟨rfl, (estep_source_pc he).symm ▸ tailLocal hs hLocal⟩

private theorem afterFinalArrivalPc {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {count : Option Nat} {target : Event}
    (hFirst : BarrierArrival X (g,i) 2 count .arrive) (hBefore : i < j)
    (hj : X.get (g,j) = some target) :
    (7742 ≤ target.pc ∧ target.pc ≤ 7745) ∨ target.pc = 9205 := by
  obtain ⟨⟨pc, _⟩, hi, rfl⟩ := hFirst
  have hCount := actualNamedBarrierCountById hp hX hi
  have hSite := actualNamedBarrier hp hX hi
  have hPc : pc = 7741 ∨ pc = 9204 := by
    have audit : namedBarrierSites.all (fun pc =>
        !(decide (namedBarrierCount pc = some 416) && decide (namedBarrierMode pc = .arrive)) ||
          decide (pc = 7741 ∨ pc = 9204)) = true := by decide
    have h := List.all_eq_true.mp audit _ hSite.1
    have hc : namedBarrierCount pc = some 416 := hSite.2.1.symm.trans hCount
    simpa only [hc, hSite.2.2.1.symm, decide_true, Bool.true_and, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] using h
  have hLength : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
  have hPast : i+1 < (X.tr g).length := by omega
  obtain ⟨_, hr⟩ := hX.thr g (Step.CtaBar.thread_lt_of_get hX hi)
  obtain ⟨s, u, he, hTail⟩ := hr.after_event hi hPast
  have hSource := estep_source_pc he
  change pc = s.pc at hSource
  have hAdvance : u.pc = pc+1 := by
    rcases hPc with rfl | rfl
    · have h := followsMarkedBarrier hSource.symm Flow.code_7741 rfl he
      rw [← hSource] at h
      exact h
    · have h := followsMarkedBarrier hSource.symm Flow.code_9204 rfl he
      rw [← hSource] at h
      exact h
  have hTailPc : finalTail u.pc := by
    rw [hAdvance]
    rcases hPc with rfl | rfl <;> decide
  have hNonempty : (X.tr g).drop (i+1) ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hPast (List.drop_eq_nil_iff.mp h)
  cases hEvents : (X.tr g).drop (i+1) with
  | nil => exact (hNonempty hEvents).elim
  | cons e rest =>
    rw [hEvents] at hTail
    have hCurrent : X.get (g,i+1) = some e := by
      change (X.tr g)[i+1]? = some e
      rw [show (X.tr g)[i+1]? = ((X.tr g).drop (i+1))[0]? by simp, hEvents]
      rfl
    have hLater : ((X.tr g).drop (i+1))[j-(i+1)]? = some target := by
      rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
      exact hj
    have noCorrectionEntry (h : 7746 ≤ e.pc ∧ e.pc ≤ 7747) : False := by
      rcases hPc with hFirst | hLast
      · obtain ⟨warp, _, pos, state, _, hPos, hAt, hRun⟩ :=
          Softmax.softmaxBodySuffix hp hX hi (by change 3420 ≤ pc; omega)
            (by change pc < 7742; omega)
        let w := Fin.castLE (by decide : 8 ≤ 16) warp
        have hPc : registerHintPc w + 1 = 3103 := by
          dsimp only [w]
          fin_cases warp <;> rfl
        obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
        have hMem : e ∈ (X.tr g).drop pos := by
          apply List.mem_of_getElem? (i := i + 1 - pos)
          rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
          exact hCurrent
        have hRole := roleBodyEventPcs w (hPc.symm ▸ hAt) hWalk e hMem
        unfold roleBodyPc at hRole
        have hw : w.val < 8 := warp.isLt
        rcases hRole with hp | hR
        · omega
        · split_ifs at hR <;> omega
      · have hStart : u.pc = 9205 := by omega
        have hRet := firstAfterReturn hStart hTail
        omega
    rcases firstTailEvent hTailPc hTail with h | ⟨hRest,hEvent⟩
    · exact (noCorrectionEntry (by rcases h with h | h <;> omega)).elim
    · subst rest
      rw [hEvents] at hLater
      have heq := List.getElem?_eq_some_iff.mp hLater
      have idx : j-(i+1) = 0 := by simp at heq; omega
      rw [idx, List.getElem?_cons_zero] at hLater
      obtain rfl := Option.some.inj hLater
      rcases hEvent with h | h
      · by_cases hi : e.pc ≤ 7745
        · exact .inl ⟨h.1, hi⟩
        · exact (noCorrectionEntry ⟨by omega, h.2⟩).elim
      · exact .inr h

private theorem localTerminalFault {l : Launch} {g : Nat} {s : TState} {tmpl : Tmpl}
    (hLo : 7742 ≤ s.pc) (hHi : s.pc ≤ 7745)
    (hOut : out kernel Assumptions.all l g s = .ev tmpl) : ∃ f, tmpl = .ub f := by
  have hLocal (ins : Instr) (h : kernel.code[s.pc]? = some ins) : ins.op.isLocal = true := by
    have hCode : ((kernel.code.drop 7742).take 4).all (·.op.isLocal) = true := by decide +kernel
    apply List.all_eq_true.mp hCode ins
    apply List.mem_of_getElem? (i := s.pc - 7742)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, h]
  unfold out at hOut
  split at hOut
  · cases hOut; exact ⟨_, rfl⟩
  · split at hOut
    · cases hOut; exact ⟨_, rfl⟩
    · rename_i ins hc
      split at hOut
      · cases hOut; exact ⟨_, rfl⟩
      · cases hOut
      · rw [ite_eq_left (hLocal ins hc)] at hOut
        split at hOut
        · cases hOut
        · cases hOut; exact ⟨_, rfl⟩

/-- The final allocation arrival leaves no further operation in this lane except exit. -/
theorem finalArrivalTerminates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {count : Option Nat} {e : Event}
    (hArrive : BarrierArrival X (g,i) 2 count .arrive) (hBefore : i < j)
    (he : X.get (g,j) = some e) : e.kind = .exit ∨ ∃ fault, e.kind = .ub fault := by
  rcases afterFinalArrivalPc hp hX hArrive hBefore he with ⟨hLo, hHi⟩ | hs
  · obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
    obtain ⟨t, _, tmpl, hOut, hf⟩ := hr.estep (List.mem_of_getElem? he)
    have hPc : t.pc = e.pc := (fires_source_pc hf).symm
    obtain ⟨f, rfl⟩ := localTerminalFault (hPc.symm ▸ hLo) (hPc.symm ▸ hHi) hOut
    exact .inr ⟨f, congrArg Event.kind hf.1⟩
  · rcases get_source hX he with hFault | ⟨_, _, _, _, hc, hf⟩
    · exact .inr hFault
    rw [hs, Flow.code_9205] at hc
    obtain rfl := Option.some.inj hc.symm
    exact .inl (congrArg Event.kind hf.1)

/-- A barrier-2 arrival is terminal for its softmax or correction lane. -/
theorem noBarrierAfterFinalArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {count nextCount : Option Nat} {mode : BarMode}
    (hFirst : BarrierArrival X (g,i) 2 count .arrive) (hBefore : i < j)
    (hNext : BarrierArrival X (g,j) 2 nextCount mode) : False := by
  obtain ⟨⟨_, _⟩, hGet, rfl⟩ := hNext
  rcases finalArrivalTerminates hp hX hFirst hBefore hGet with hExit | ⟨_, hFault⟩
  · cases hExit
  · cases hFault

/-- Asymmetric arrivals use the terminal handoff or a producer's statistics barrier. -/
theorem asymmetricArrivalId {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {id : Nat} {count : Option Nat} (h : BarrierArrival X i id count .arrive) :
    id = 2 ∨ 3 ≤ id ∧ id < 11 := by
  obtain ⟨⟨pc, _⟩, he, rfl⟩ := h
  obtain ⟨hSite, hCount, hMode, _, _, _, hTerminal⟩ := actualNamedBarrier hp hX he
  have audit : namedBarrierSites.all (fun pc =>
      !decide (namedBarrierMode pc = .arrive) ||
      decide (namedBarrierCount pc = some 416 ∨ pc ∈ Softmax.softmaxStatsSites)) = true := by
    decide
  have hClass := List.all_eq_true.mp audit pc hSite
  simp only [hMode.symm, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hClass
  rcases hClass with hc | hs
  · exact .inl (hTerminal (hCount.trans hc))
  · have hId := Softmax.actualSoftmaxStatsBarrierId hp hX hs he
    have hPc : 3420 ≤ pc ∧ pc < 7742 := by
      simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hs
      omega
    rcases i with ⟨g, j⟩
    obtain ⟨w, hw, _⟩ := Softmax.softmaxBodySuffix hp hX he hPc.1 hPc.2
    change id = 3 + warpIndex l g at hId
    exact .inr ⟨by omega, by have := w.isLt; omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
