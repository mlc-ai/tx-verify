-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.MmaPvTrace
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Lemmas.Order.ElectOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPollOrdinalReturn
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.TcIssueProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Correction Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Correction (OpeningTripCursor)

/-- MMA and its mbarrier retries preserve the warp collective ordinals. -/
def PvOrdinalsPreserved (X : Execution) (g first last : Nat) : Prop :=
  ((X.tr g).take last).countP Execution.isShfl = ((X.tr g).take first).countP Execution.isShfl ∧
    ((X.tr g).take last).countP isFullWarpVote = ((X.tr g).take first).countP isFullWarpVote ∧
    elections X g last = elections X g first

theorem PvOrdinalsPreserved.trans {X : Execution} {g a b c : Nat}
    (hAB : PvOrdinalsPreserved X g a b) (hBC : PvOrdinalsPreserved X g b c) :
    PvOrdinalsPreserved X g a c :=
  ⟨hBC.1.trans hAB.1,hBC.2.1.trans hAB.2.1,hBC.2.2.trans hAB.2.2⟩

/-- A PV segment consumes only its own tail object, and only when it actually
crosses the tail acquire. -/
def PvPollDelta (X : Execution) (g first last : Nat) (tail : Loc) (crossed : Bool) : Prop :=
  ∀ other, okPolls other ((X.tr g).take last) =
    okPolls other ((X.tr g).take first) + if crossed = true ∧ other = tail then 1 else 0

theorem PvPollDelta.refl (X : Execution) (g first : Nat) (tail : Loc) :
    PvPollDelta X g first first tail false := by intro other; simp

theorem PvPollDelta.transOfNotBoth {X : Execution} {g a b c : Nat} {tail : Loc} {u v : Bool}
    (hAB : PvPollDelta X g a b tail u) (hBC : PvPollDelta X g b c tail v)
    (hDisjoint : ¬ (u = true ∧ v = true)) : PvPollDelta X g a c tail (u || v) := by
  intro other
  rw [hBC other,hAB other]
  cases u <;> cases v <;> simp_all

private theorem pvResumeOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (block : Fin 4) (step : Fin 8) (use phase : Nat) (accumulated lead : Bool)
    {extra : List (Nat × Value)}
    (c : OpeningTripCursor l X g (pvPc block step)
      (pvIssueFrame l block use phase accumulated lead step ++ extra)) :
    (lead = true → X.get (g,c.pos) = some (pvIssueEvent l g block step use accumulated)) ∧
      ∃ after : OpeningTripCursor l X g (pvPc block step+1)
        (pvIssueFrame l block use phase accumulated lead step ++ extra),
        after.pos = c.pos+(if lead then 1 else 0) ∧ PvOrdinalsPreserved X g c.pos after.pos ∧
          ∀ other, okPolls other ((X.tr g).take after.pos) =
            okPolls other ((X.tr g).take c.pos) := by
  obtain ⟨hPred,hFacts⟩ :=
    pvFrameOperands block use phase accumulated lead step
      ((holds_append ..).mp c.checkpoint.2.2.2.2).1
  cases lead
  · exact ⟨(fun h => by cases h),
      ⟨c.pos,c.before,next c.ready,c.ending,c.positive,c.bounded,c.released,c.checkpoint.next,
        c.recorded,c.remaining,c.localSteps.tail (pvSkip block step c.checkpoint hPred)⟩,
      by simp,⟨rfl,rfl,rfl⟩,fun _ => rfl⟩
  · have hOut := pvIssueOut hp hg block step use accumulated (c.checkpoint.mono (hFacts rfl))
    have hn := Next.mk c.localSteps hOut
    obtain ⟨he,hPast,hSuffix⟩ := Step.tc_issue_of_maximal hMax hg hn rfl
      c.recorded c.remaining c.positive c.bounded c.released
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
    have hGet : X.get (g,c.pos) = some (pvIssueEvent l g block step use accumulated) := by
      rw [he,c.checkpoint.1]
      rfl
    exact ⟨fun _ => hGet,
      ⟨c.pos+1,next c.ready,next c.ready,c.ending,Nat.succ_pos _,len_of_get he,
        releasedIfLast hGet (by intro h; cases h),c.checkpoint.next,hPast,hSuffix,.refl⟩,rfl,
      ⟨countP_take_succ_false hGet rfl,countP_take_succ_false hGet rfl,
        countP_take_succ_false hGet rfl⟩,
      fun _ => countP_take_succ_false hGet rfl⟩

/-- A tail credit is required only at an actual final state blocked at the tail poll. -/
def PvTailReadyAtFrontier (l : Launch) (X : Execution) (g : Nat) (block : Fin 4)
    (phase : Nat) (F : List (Nat × Value)) : Prop :=
  ∀ {t u}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u →
    At u (waitSite (pvTailWait block)).pc F →
    let log := X.objects ⟨.shared,g/l.block,pvTailAddress l block⟩
    ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2

/-- The tail can be proved available by a final ready state or by the exact
count on the actual prefix, whenever no remaining event consumes that count. -/
def PvTailReadyWithOrdinal (l : Launch) (X : Execution) (g : Nat) (block : Fin 4)
    (phase : Nat) (F : List (Nat × Value)) (pos : Nat) : Prop :=
  PvTailReadyAtFrontier l X g block phase F ∨
    let loc : Loc := ⟨.shared,g/l.block,pvTailAddress l block⟩
    okPolls loc (X.tr g) = okPolls loc ((X.tr g).take pos) →
      let log := X.objects loc
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (block : Fin 4)
    (step : Fin 7) (use phase : Nat) (accumulated lead : Bool) (hParity : phase < 2)
    {extra : List (Nat × Value)}
    (hExtra : ∀ pair ∈ extra, pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b ∧
      pair.1 ≠ (waitSite (pvTailWait block)).result)
    (c : OpeningTripCursor l X g (pvPc block (pvPrev step)+1)
      (pvIssueFrame l block use phase accumulated lead (pvPrev step) ++ extra))
include hp hMax hg block step use phase accumulated lead hParity hExtra c

/-- Reframe the first tail-block issue after a local advance or the recorded tail acquire. -/
theorem pvAdvanceOfMaximalWithPollCounts
    (hReady : step.val = 5 → PvTailReadyWithOrdinal l X g block phase extra c.pos) :
    ∃ after : OpeningTripCursor l X g (pvPc block (pvNext step))
        (pvIssueFrame l block use phase accumulated lead (pvNext step) ++ extra),
      c.pos ≤ after.pos ∧ PvOrdinalsPreserved X g c.pos after.pos ∧
        PvPollDelta X g c.pos after.pos
          ⟨.shared,g/l.block,pvTailAddress l block⟩ (step.val == 5) := by
  let F := pvIssueFrame l block use phase accumulated lead (pvPrev step) ++ extra
  have hGap := pvGap block step
  have hAligned : ∃ cd : OpeningTripCursor l X g (pvAdvancePc block step-2) F,
      cd.ending = c.ending ∧ c.pos ≤ cd.pos ∧ PvOrdinalsPreserved X g c.pos cd.pos ∧
        PvPollDelta X g c.pos cd.pos ⟨.shared,g/l.block,pvTailAddress l block⟩
          (step.val == 5) := by
    by_cases h : step.val = 5
    · rw [ite_eq_left h] at hGap
      let site := pvTailWait block
      have hWidth : pvTailAddress l block < 2^32 := by
        have := hp.shared.2.1
        have := (pvSite block).stage.isLt
        unfold pvTailAddress
        omega
      have hAlign : pvTailAddress l block%8 = 0 := by
        have := hp.shared.1
        unfold pvTailAddress
        omega
      have hBase : ((waitSite site).base,b32 (pvTailAddress l block)) ∈ F := by
        simp [site,F,pvIssueFrame,pvCarry]
      have hPhase : ((waitSite site).phase,b32 phase) ∈ F := by simp [site,F,pvIssueFrame,pvCarry]
      have hFresh (item : Nat × Value) (hm : item ∈ F) : item.1 ≠ (waitSite site).result := by
        rcases List.mem_append.mp hm with hf | hx
        · exact pvBlockFrameTail block use phase accumulated lead _ item hf
        · exact (hExtra item hx).2.2
      let atPoll : OpeningTripCursor l X g (waitSite site).pc F :=
        ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,hGap.1 ▸ c.checkpoint,
          c.recorded,c.remaining,c.localSteps⟩
      let ev (ok : Bool) : Event :=
        ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,pvTailAddress l block⟩ phase ok true .cta⟩
      have hActual : ∃ after : OpeningTripCursor l X g ((waitSite site).pc+3) F,
          after.ending = c.ending ∧ ∃ n tail, after.pos = c.pos+n+1 ∧
            (X.tr g).drop c.pos = List.replicate n (ev false) ++ ev true :: tail := by
        rcases hReady h with hFrontier | hOrdinal
        · obtain ⟨n,_,_,_,_,_,_,_,hTrace⟩ :=
            waitOfMaximalWithTrace hMax hg site hWidth hAlign hParity
              hFresh hBase hPhase (fun hRun hLocal hAt =>
              hFrontier hRun hLocal (hAt.mono ((holds_append ..).mp hAt.2.2.2.2).2))
              c.positive c.bounded c.released atPoll.checkpoint
              c.recorded c.remaining c.localSteps
          obtain ⟨returned,hPos,hEnd⟩ :=
            replayPollFromTrace site hWidth hAlign hParity hFresh hBase hPhase atPoll hTrace
          exact ⟨returned,hEnd,n,_,hPos,hTrace⟩
        · obtain ⟨returned,_,hEnd,_,_,n,tail,hPos,hTrace⟩ :=
            pollOrdinalReturnedWithTraceOfMaximal hMax hg site hWidth hAlign hParity
              hFresh hBase hPhase atPoll rfl hOrdinal
          exact ⟨returned,hEnd,n,tail,hPos,hTrace⟩
      obtain ⟨returned,hEnd,n,tail,hPos,hTrace⟩ := hActual
      let retries := List.replicate n (ev false) ++ [ev true]
      have hLen : retries.length = n+1 := by simp [retries]
      have hSplit : (X.tr g).drop c.pos = retries ++ tail := by
        simpa only [retries,List.append_assoc,List.singleton_append,ev] using hTrace
      have hCounts (test : Event → Bool) (hf : test (ev false) = false)
          (ht : test (ev true) = false) :
          ((X.tr g).take (c.pos+n+1)).countP test = ((X.tr g).take c.pos).countP test := by
        have hNone : retries.countP test = 0 := by simp [retries,hf,ht]
        rw [Nat.add_assoc,List.take_add,hSplit,← hLen,List.take_append_length,
          List.countP_append,hNone,Nat.add_zero]
      refine ⟨⟨returned.pos,returned.before,returned.ready,returned.ending,returned.positive,
        returned.bounded,returned.released,hGap.2 ▸ returned.checkpoint,returned.recorded,
        returned.remaining,returned.localSteps⟩,hEnd,by change c.pos ≤ returned.pos; omega,?_,?_⟩
      · rw [hPos]
        exact ⟨hCounts _ rfl rfl,hCounts _ rfl rfl,hCounts _ rfl rfl⟩
      · intro other
        rw [hPos,Nat.add_assoc,List.take_add,hSplit,←hLen,List.take_append_length]
        simp [h,retries,okPolls,List.countP_append,List.countP_replicate,okPoll,
          sourceWaitSuccess,ev,eq_comm]
    · rw [ite_eq_right h] at hGap
      exact ⟨⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,
        hGap ▸ c.checkpoint,c.recorded,c.remaining,c.localSteps⟩,rfl,le_rfl,⟨rfl,rfl,rfl⟩,
        by simpa only [beq_eq_false_iff_ne.mpr h] using PvPollDelta.refl X g c.pos _⟩
  obtain ⟨cd,_hEnd,hPos,hCounts,hPoll⟩ := hAligned
  obtain ⟨u,hu,hr⟩ := pvAdvanceLocalFramed hp (g := g) block step use phase accumulated lead
    (fun pair h => ⟨(hExtra pair h).1,(hExtra pair h).2.1⟩) cd.checkpoint
  exact ⟨⟨cd.pos,cd.before,u,cd.ending,cd.positive,cd.bounded,cd.released,hu,cd.recorded,
    cd.remaining,cd.localSteps.trans hr⟩,hPos,hCounts,hPoll⟩

end

/-- All remaining fragments are issued by the elected lane. Other lanes skip the same
fragments while consuming their own tail acquire. -/
theorem pvLanePacketOfMaximalWithPollCounts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (block : Fin 4) (use phase : Nat) (accumulated lead : Bool)
    (hParity : phase < 2) (start : Fin 8) {extra : List (Nat × Value)}
    (hExtra : ∀ pair ∈ extra, pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b ∧
      pair.1 ≠ (waitSite (pvTailWait block)).result)
    (c : OpeningTripCursor l X g (pvPc block start)
      (pvIssueFrame l block use phase accumulated lead start ++ extra))
    (hReady : start.val ≤ 5 → PvTailReadyWithOrdinal l X g block phase extra c.pos) :
    ∃ after : OpeningTripCursor l X g (pvPc block 7+1)
        (pvIssueFrame l block use phase accumulated lead 7 ++ extra),
      PvOrdinalsPreserved X g c.pos after.pos ∧ c.pos ≤ after.pos ∧
        PvPollDelta X g c.pos after.pos ⟨.shared,g/l.block,pvTailAddress l block⟩
          (decide (start.val ≤ 5)) ∧
        ∀ step : Fin 8, start.val ≤ step.val → lead = true → ∃ j,
          c.pos ≤ j ∧ j < after.pos ∧ X.get (g,j) =
            some (pvIssueEvent l g block step use accumulated) := by
  obtain ⟨he,next,hPos,hResume,hResumePolls⟩ :=
    pvResumeOfMaximal hp hMax hg block start use phase accumulated lead c
  have hNext : c.pos ≤ next.pos := by rw [hPos]; exact Nat.le_add_right ..
  by_cases hLast : start = 7
  · subst start
    refine ⟨next,hResume,hNext,?_,?_⟩
    · intro other
      simpa using hResumePolls other
    intro step hStep hLead
    have hEq : step = 7 := Fin.ext (by have := step.isLt; omega)
    subst step
    exact ⟨c.pos,le_rfl,by rw [hPos,ite_eq_left hLead]; exact Nat.lt_succ_self _,he hLead⟩
  · have hStep : start.val < 7 := by
      have hVal := start.isLt
      have hNot : start.val ≠ 7 := fun h => hLast (Fin.ext h)
      omega
    let index : Fin 7 := ⟨start.val,hStep⟩
    let loc : Loc := ⟨.shared,g/l.block,pvTailAddress l block⟩
    obtain ⟨advanced,hAdvance,hPassed,hAdvancedPolls⟩ :=
      pvAdvanceOfMaximalWithPollCounts hp hMax hg block index use phase accumulated lead
        hParity hExtra next (fun hs => by
          have hb : start.val ≤ 5 := by change start.val = 5 at hs; omega
          have ha := hReady hb
          unfold PvTailReadyWithOrdinal at ha ⊢
          dsimp only
          have hEq := hResumePolls loc
          dsimp only [loc] at hEq
          rw [hEq]
          exact ha)
    have hInc : (pvNext index).val = start.val+1 := rfl
    have hRec : (pvNext index).val > start.val := by omega
    have hReadyNext (hNotPassed : (pvNext index).val ≤ 5) :
        PvTailReadyWithOrdinal l X g block phase extra advanced.pos := by
      have hb := hReady (by omega)
      have hn : index.val ≠ 5 := by change start.val ≠ 5; omega
      have hSame := hAdvancedPolls loc
      rw [beq_eq_false_iff_ne.mpr hn] at hSame
      simp only [Bool.false_eq_true, false_and, ite_false, Nat.add_zero,hResumePolls loc] at hSame
      unfold PvTailReadyWithOrdinal at hb ⊢
      dsimp only
      dsimp only [loc] at hSame
      rw [hSame]
      exact hb
    obtain ⟨after,hCounts,hEnd,hPolls,hEvents⟩ :=
      pvLanePacketOfMaximalWithPollCounts hp hMax hg block use phase accumulated lead hParity
        (pvNext index) hExtra advanced hReadyNext
    have hDisjoint : ¬ ((index.val == 5) = true ∧ decide ((pvNext index).val ≤ 5) = true) := by
      intro ⟨hNow,hLater⟩
      have hEq := beq_iff_eq.mp hNow
      change start.val = 5 at hEq
      have hLe := of_decide_eq_true hLater
      omega
    have hMark : (index.val == 5 || decide ((pvNext index).val ≤ 5)) =
        decide (start.val ≤ 5) := by
      rw [hInc]
      change (start.val == 5 || decide (start.val+1 ≤ 5)) = decide (start.val ≤ 5)
      suffices ∀ q : Fin 8, (q.val == 5 || decide (q.val+1 ≤ 5)) = decide (q.val ≤ 5) by
        exact this start
      decide
    rw [← hMark]
    refine ⟨after,hResume.trans (hPassed.trans hCounts),hNext.trans (hAdvance.trans hEnd),?_,?_⟩
    · intro other
      rw [((hAdvancedPolls.transOfNotBoth hPolls hDisjoint) other),hResumePolls other]
    · intro step hStep hLead
      by_cases hEq : step = start
      · subst step
        exact ⟨c.pos,le_rfl,
          (show c.pos < next.pos by rw [hPos,ite_eq_left hLead]; exact Nat.lt_succ_self _).trans_le
            (hAdvance.trans hEnd),he hLead⟩
      · have hNe : step.val ≠ start.val := fun h => hEq (Fin.ext h)
        obtain ⟨j,hj,hFin,hEvent⟩ := hEvents step (by omega) hLead
        exact ⟨j,hNext.trans (hAdvance.trans hj),hFin,hEvent⟩
termination_by 7-start.val
decreasing_by
  change 7 - (start.val+1) < 7 - start.val
  omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (block : Fin 4)
    (use phase : Nat) (accumulated lead : Bool) (hParity : phase < 2) (start : Fin 8)
    {extra : List (Nat × Value)}
    (hExtra : ∀ pair ∈ extra, pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b ∧
      pair.1 ≠ (waitSite (pvTailWait block)).result)
    (c : OpeningTripCursor l X g (pvPc block start)
      (pvIssueFrame l block use phase accumulated lead start ++ extra))
include hp hMax hg block use phase accumulated lead hParity start hExtra c

end

end PTX.Kernels.TmlFa4Fwd.Mma
