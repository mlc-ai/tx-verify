-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopLocal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Epilogue

noncomputable section

/-- A packet interval bounded by an unguarded shuffle and its commit. -/
def outsideCopySequence (entry commit pc : Nat) : Prop := pc ≤ entry ∨ commit ≤ pc

instance (entry commit pc : Nat) : Decidable (outsideCopySequence entry commit pc) :=
  inferInstanceAs (Decidable (pc ≤ entry ∨ commit ≤ pc))

def staysOutsideCopySequence (entry commit : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (outsideCopySequence entry commit dst)
  | .brx .. => false
  | _ => true

/-- The code audit for a packet whose later visit must cross another shuffle. -/
structure CopyQuietAudit (entry commit : Nat) : Prop where
  scope : 174 ≤ entry ∧ entry < commit ∧ commit ≤ 1901
  shuffle : ∃ op, kernel.code[entry]? = some ⟨none, op⟩ ∧ op.isShfl = true ∧ op.isLocal = false
  branches : (kernel.code.zipIdx).all (fun (i, pc) =>
    !decide (outsideCopySequence entry commit pc) || staysOutsideCopySequence entry commit i.op) =
      true
  segments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (outsideCopySequence entry commit seg.stop)
    | none => false) = true

private theorem outsideEventCode :
    kernel.code.all (fun i => i.op.isLocal || ordinaryEvent i.op) = true := by
  decide +kernel

private theorem outsideSucc {entry commit pc : Nat}
    (h : outsideCopySequence entry commit pc) (hFirst : pc ≠ entry) :
    outsideCopySequence entry commit (pc + 1) := by
  unfold outsideCopySequence at *
  omega

variable {l : Launch}

private theorem outsideCopyStep {g entry commit : Nat} {s u : TState} {event : Option Event}
    (audit : CopyQuietAudit entry commit) (hOutside : outsideCopySequence entry commit s.pc)
    (hs : WStep kernel Assumptions.all l g s event u)
    (hQuiet : event.toList.countP Execution.isShfl = 0) :
    outsideCopySequence entry commit u.pc := by
  have hFirst : s.pc ≠ entry := by
    intro hPc
    obtain ⟨op, hCode, hShuffle, hLocal⟩ := audit.shuffle
    have hScope := audit.scope
    have hCore := loaderOutCore (l := l) (g := g) (t := s) (by omega) (by omega)
    rcases hs with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
    · have ht' : Tau kernel [] l g s u := by unfold Tau at ht ⊢; rwa [← hCore]
      exact tau_core_not_event (hPc.symm ▸ hCode) hLocal ht'
    · have he' : EStep kernel [] l g s e (some u) := by
        obtain ⟨tmpl, hOut, hf⟩ := he
        exact ⟨tmpl, hCore.symm.trans hOut, hf⟩
      obtain ⟨ins, hc, _, hf⟩ := estep_event_source he'
      rw [hPc, hCode] at hc
      obtain rfl := Option.some.inj hc.symm
      have hEvent := (shuffle_fires_next hShuffle hf).1
      simp [hEvent] at hQuiet
  have hForward := outsideSucc hOutside hFirst
  rcases hs with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨ins, hCode, _, hExec⟩ := Softmax.tauScoreSource ht
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact hForward
    · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg, hSite, hMatch, hSeg⟩
      · have hMember : (ins, s.pc) ∈ kernel.code.zipIdx := by
          apply List.mem_of_getElem? (i := s.pc)
          simp [hCode]
        have hAudit := List.all_eq_true.mp audit.branches _ hMember
        simp only [hOutside, decide_true, Bool.not_true, Bool.false_or] at hAudit
        have hNext := hFrame.pc
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
        case bra dst uni =>
          simpa only [staysOutsideCopySequence, hop, decide_eq_true_eq, hNext] using hAudit
        case brx => simp [hop, staysOutsideCopySequence] at hAudit
        all_goals exact hNext.symm ▸ hForward
      · have hAudit := List.all_eq_true.mp audit.segments _ hSite
        rw [hMatch] at hAudit
        exact (Softmax.scoreSegmentFrame hSeg).1.symm ▸ of_decide_eq_true hAudit
  · obtain ⟨ins, hCode, hNoLocal, hFire⟩ := estep_event_source he
    have hAudit := List.all_eq_true.mp outsideEventCode ins (List.mem_of_getElem? hCode)
    have hFrame := ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hNoLocal, Bool.false_or] using hAudit)
    rcases callbackFrame_fires hFrame hFire with hNext | hSame
    · exact hNext.symm ▸ hOutside
    · exact hSame.symm ▸ hForward

private theorem outsideCopyObserved {g entry commit : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hWalk : Walk kernel Assumptions.all l g s events visits)
    (audit : CopyQuietAudit entry commit) (hOutside : outsideCopySequence entry commit s.pc)
    {j : Nat} {e : Event} (he : events[j]? = some e)
    (hQuiet : (events.take j).countP Execution.isShfl = 0) :
    outsideCopySequence entry commit e.pc := by
  induction hWalk generalizing j with
  | stop => simp at he
  | tau h _ ih => exact ih (outsideCopyStep audit hOutside (.inl ⟨rfl, h⟩) rfl) he hQuiet
  | ev h _ ih =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      exact (estep_source_pc h).symm ▸ hOutside
    | succ j =>
      simp only [List.take_succ_cons, List.countP_cons] at hQuiet
      split at hQuiet
      · omega
      · rename_i hNot
        exact ih (outsideCopyStep audit hOutside (.inr ⟨_, rfl, h⟩) (by simp [hNot]))
          (List.getElem?_cons_succ.symm.trans he) hQuiet
  | last h =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      exact (estep_source_pc h).symm ▸ hOutside
    | succ j => simp at he

/-- If a packet has ended, reaching another copy in its interval requires another shuffle. -/
theorem copyNoQuietReentry {g entry commit : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hWalk : Walk kernel Assumptions.all l g s events visits)
    (audit : CopyQuietAudit entry commit) (hStart : commit ≤ s.pc) {j : Nat} {e : Event}
    (he : events[j]? = some e) (hInside : entry < e.pc ∧ e.pc < commit) :
    0 < (events.take j).countP Execution.isShfl := by
  by_contra! hQuiet
  rcases outsideCopyObserved hWalk audit (.inr hStart) he (by omega) with h | h <;> omega

/-- A copy with no intervening shuffle belongs to the current packet slice,
including its final pair before the packet commit. -/
theorem copyQuietSlice {g start entry commit : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (audit : CopyQuietAudit entry commit) (hStart : 174 ≤ start)
    (hAudit : ∀ bound, ((kernel.code.drop start).take (commit - start)).all
      (fun ins => loaderPipelineCutOp start commit bound [] ins.op) = true)
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hPc : start ≤ s.pc ∧ s.pc ≤ commit)
    (hShape : RingShape s) {j : Nat} {e : Event} (he : events[j]? = some e)
    (hInside : entry < e.pc ∧ e.pc < commit) (hQuiet : (events.take j).countP Execution.isShfl = 0)
    :
    e ∈ loaderSliceEvents start commit visits := by
  have advance {t u : TState} {ev : Option Event} (hHere : start ≤ t.pc ∧ t.pc < commit)
      (hShape : RingShape t) (hStep : WStep kernel Assumptions.all l g t ev u) :
      (start ≤ u.pc ∧ u.pc ≤ commit) ∧ RingShape u := by
    obtain ⟨hLo, hHi, hu, _⟩ := pipelineCutStep (F := []) hStart audit.scope.2.2
      hHere (hAudit u.pc) hStep hShape trivial
    exact ⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, hu⟩
  induction hWalk generalizing j with
  | stop => simp at he
  | @tau t u es vs ht hw ih =>
    have hi : t.pc < commit := by
      by_contra! hi
      have hNo := copyNoQuietReentry (.tau ht hw) audit hi he hInside
      omega
    obtain ⟨hu, hKeep⟩ := advance ⟨hPc.1, hi⟩ hShape (.inl ⟨rfl, ht⟩)
    simpa [loaderSliceEvents, visit, hPc.1, hi] using ih hu hKeep he hQuiet
  | @ev t u here es vs hEvent hw ih =>
    have hi : t.pc < commit := by
      by_contra! hi
      have hNo := copyNoQuietReentry (.ev hEvent hw) audit hi he hInside
      omega
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      simp [loaderSliceEvents, visit, hPc.1, hi]
    | succ j =>
      obtain ⟨hu, hKeep⟩ := advance ⟨hPc.1, hi⟩ hShape (.inr ⟨here, rfl, hEvent⟩)
      have hZero : (es.take j).countP Execution.isShfl = 0 := by
        simp only [List.take_succ_cons, List.countP_cons] at hQuiet
        split at hQuiet <;> omega
      have hMember := ih hu hKeep (List.getElem?_cons_succ.symm.trans he) hZero
      simp [loaderSliceEvents, visit, hPc.1, hi, List.mem_filterMap] at hMember ⊢
      exact .inr hMember
  | @last t here hEvent =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      have hi : t.pc < commit := (estep_source_pc hEvent) ▸ hInside.2
      simp [loaderSliceEvents, visit, hPc.1, hi]
    | succ j => simp at he

end
end PTX.Kernels.TmlFa4Fwd.Loader
