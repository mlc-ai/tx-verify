-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Lemmas.Execution.ExecutionGrowth
import Lemmas.Flow.Final
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

private def branchTargetInCode : Op → Bool
  | .bra dst _ => decide (dst < 9206)
  | .brx .. => false
  | _ => true

private theorem checkedBranches :
    kernel.code.all (fun ins => branchTargetInCode ins.op) = true := by
  decide +kernel

private theorem checkedSegmentStops :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (seg.stop < 9206)
      | none => false) = true := by decide +kernel

private theorem checkedEvents :
    kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by
  decide +kernel

private theorem exitStops {l : Launch} {g : Nat} {s : TState} (hp : s.pc = 9205) :
    ∃ m, out kernel Assumptions.all l g s = .ev m ∧
      ∀ e u, ¬ Fires s.pc m e (some u) := by
  cases hf : s.fault with
  | none =>
    refine ⟨.exit, ?_, ?_⟩
    · rw [out, hf, hp, Flow.code_9205]
      rfl
    · rintro e u ⟨_, hn⟩
      cases hn
  | some f =>
    refine ⟨.ub f, by simp [out, hf], ?_⟩
    rintro e u ⟨_, hn⟩
    cases hn

private theorem stepWithinCode {l : Launch} {g : Nat} {s u : TState} {event : Option Event}
    (hp : s.pc < 9206) (hs : WStep kernel Assumptions.all l g s event u) : u.pc < 9206 := by
  have hBody : s.pc < 9205 := by
    by_contra! hEnd
    obtain ⟨m, hm, hTerminal⟩ := exitStops (l := l) (g := g) (s := s) (by omega)
    rcases hs with ⟨rfl, hTau⟩ | ⟨e, rfl, ⟨tmpl, hOut, hFire⟩⟩
    · unfold Tau at hTau
      rw [hm] at hTau
      cases hTau
    · cases Out.ev.inj (hOut.symm.trans hm)
      exact hTerminal e u hFire
  rcases hs with ⟨rfl, hTau⟩ | ⟨e, rfl, hEv⟩
  · obtain ⟨ins, hCode, _, hExec⟩ := Softmax.tauScoreSource hTau
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · change s.pc + 1 < 9206
      omega
    · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg, hSite, hMatch, hSeg⟩
      · have hAudit := List.all_eq_true.mp checkedBranches ins (List.mem_of_getElem? hCode)
        have hNext := hFrame.pc
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
        case bra dst uni =>
          simpa only [branchTargetInCode, hop, decide_eq_true_eq, hNext] using hAudit
        case brx => simp [hop, branchTargetInCode] at hAudit
        all_goals omega
      · have hAudit := List.all_eq_true.mp checkedSegmentStops _ hSite
        rw [hMatch] at hAudit
        exact (Softmax.scoreSegmentFrame hSeg).1.symm ▸ of_decide_eq_true hAudit
  · obtain ⟨ins, hCode, hNoLocal, hFire⟩ := estep_event_source hEv
    have hAudit := List.all_eq_true.mp checkedEvents ins (List.mem_of_getElem? hCode)
    have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hNoLocal, Bool.false_or] using hAudit)
    rcases callbackFrame_fires hFrame hFire with hNext | hSame <;> omega

private theorem walkWithinCode {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (hp : s.pc < 9206)
    (hw : Walk kernel Assumptions.all l g s events visits) : ∀ e ∈ events, e.pc < 9206 := by
  induction hw with
  | stop => simp
  | tau ht _ ih => exact ih (stepWithinCode hp (.inl ⟨rfl, ht⟩))
  | ev ht _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (estep_source_pc ht).symm ▸ hp
    · exact ih (stepWithinCode hp (.inr ⟨_, rfl, ht⟩)) e he
  | last ht =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact (estep_source_pc ht).symm ▸ hp

private theorem rulesPresent : kernel.code.all (fun ins => ins.op.rule.isSome) = true := by
  decide +kernel

/-- An observed instruction fault at an instruction with a supported decoded rule. -/
@[no_expose] def DecodedFault (X : Execution) (i : EvId) (f : Fault) : Prop :=
  ∃ site ins, X.get i = some ⟨site, .ub f⟩ ∧
    kernel.code[site]? = some ins ∧ ins.op.rule.isSome = true

/-- Actual faults occur at decoded instructions. Every continuing thread step stays in
the code, including every checked branch, segment and returning event. -/
theorem decodedFaultOfUb {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (hUb : HasUb X) :
    ∃ i f, DecodedFault X i f := by
  obtain ⟨i, site, f, hGet⟩ := hUb
  have hg := event_thread_lt hX hGet
  obtain ⟨_, hRun⟩ := hX.thr i.1 hg
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
  have hPc := walkWithinCode (by decide : 0 < 9206) hWalk _ (List.mem_of_getElem? hGet)
  have hBound : site < kernel.code.length := by
    rw [Decoded.code_length]
    exact hPc
  refine ⟨i, f, site, kernel.code[site], hGet, List.getElem?_eq_getElem hBound, ?_⟩
  exact List.all_eq_true.mp rulesPresent _ (List.getElem_mem hBound)

/-- A prefix fault remains the final event of its lane in every consistent
extension, ruling out a normal exit. -/
theorem DecodedFault.contradictsExitsInExtension {l : Launch} {m : Mem0} {X Y : Execution}
    (hY : Consistent l kernel Assumptions.all m Y) (hPrefix : X.le Y)
    (hExits : ∀ g < l.threads, Exited Y g) {i : EvId} {f : Fault} (hFault : DecodedFault X i f) :
    False := by
  obtain ⟨g,j⟩ := i
  obtain ⟨site,_,he,_,_⟩ := hFault
  have hGet := Execution.le_get hPrefix he
  have hg := event_thread_lt hY hGet
  obtain ⟨_,hRun⟩ := hY.thr g hg
  have hLast := Flow.Run.end_last hRun hGet (.inl ⟨f,rfl⟩)
  obtain ⟨exitSite,hExit⟩ := (hExits g hg).lastEvent hY hg
  rw [List.getLast?_eq_getElem?, ← hLast, Nat.add_sub_cancel] at hExit
  change (Y.tr g)[j]? = some ⟨site, .ub f⟩ at hGet
  rw [hGet] at hExit
  cases hExit

end PTX.Kernels.TmlFa4Fwd.Thread
