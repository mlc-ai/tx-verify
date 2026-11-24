-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitOpening
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

private def openingElection (stage : Fin 2) : Fin 20 :=
  commitElection (qkCommitSite (initialQkBlock stage))

private def openingFloor (stage : Fin 2) : Nat := (electSite (openingElection stage)).pc + 1

private theorem openingElectionAudit :
    ∀ stage : Fin 2, let site := electSite (openingElection stage)
      kernel.code[site.pc]? =
        some ⟨none, .warp ⟨.elect, none, [site.result, some site.pred], [], some (.imm (-1))⟩⟩ :=
  by
    intro stage
    fin_cases stage
    · exact Flow.code_2205
    · exact Flow.code_2267

private theorem openingBranchAudit :
    ∀ stage : Fin 2, (kernel.code.drop (openingFloor stage)).all
      (fun i => staysPastEvent (openingFloor stage) i.op) = true := by decide +kernel

private theorem openingSegmentAudit :
    ∀ stage : Fin 2, Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (openingFloor stage ≤ seg.stop)
      | none => false) = true := by decide +kernel

private theorem openingElectionNotRepeated {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g a b mask mask' inst inst' leader leader' : Nat}
    (ha : X.Elect (g,a) (electSite (openingElection stage)).pc mask inst leader)
    (hb : X.Elect (g,b) (electSite (openingElection stage)).pc mask' inst' leader')
    (hab : a < b) : False := by
  let site := electSite (openingElection stage)
  let e : Event := ⟨site.pc, .elect mask' inst' leader'⟩
  obtain ⟨o, run⟩ := hX.thr g (event_thread_lt hX ha)
  have hbLen : b < (X.tr g).length := len_of_get hb
  obtain ⟨s, u, hStep, hSuffix⟩ := run.after_event ha (by omega)
  obtain ⟨ins, hCode, _, hFire⟩ := EventFrame.estep_event_source hStep
  have hPc : s.pc = site.pc := (EventFrame.estep_source_pc hStep).symm
  rw [hPc, openingElectionAudit stage] at hCode
  obtain rfl := Option.some.inj hCode.symm
  obtain ⟨_, _, _, _, hAfter⟩ := fires_elect hFire
  have hFloor : openingFloor stage ≤ u.pc := by
    change site.pc + 1 ≤ u.pc
    rw [hAfter]
    cases site.result <;> simp [next, setReg, hPc]
  have hm : e ∈ (X.tr g).drop (a + 1) := by
    apply List.mem_of_getElem? (i := b - (a + 1))
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega : a + 1 ≤ b)]
  obtain ⟨_, hWalk⟩ := walkFromRun hSuffix
  have hLate := eventTailEvents (floor := openingFloor stage)
    (openingBranchAudit stage) (openingSegmentAudit stage) hWalk hFloor e hm
  change site.pc + 1 ≤ site.pc at hLate
  omega

/-- The initial score commit has ordinal zero at either stage's physical score object. -/
theorem openingScoreOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {stage : Fin 2} {spec : TcCommit.Spec}
    (hInitial : OpeningScoreCommit X (g,index) stage spec) :
    scoreCommitOrdinal l X (g/l.block) stage (g,index) = 0 := by
  have hGet := hInitial.decoded
  obtain ⟨hPos, inst, leader, hElection, _⟩ :=
    scoreCommitLeader hp hX (initialQkBlock stage) hGet
  apply List.countP_eq_zero.mpr
  intro e he
  obtain ⟨j, hLookup⟩ := List.mem_iff_getElem?.mp he
  have hBefore : j < index := by
    have hLen := (List.getElem?_eq_some_iff.mp hLookup).1
    simp only [List.length_take] at hLen
    omega
  have hActual : X.get (g,j) = some e := by
    change (X.tr g)[j]? = some e
    rwa [List.getElem?_take_of_lt hBefore] at hLookup
  by_contra hMarked
  have hMark : scoreCommitOn (scoreReadyObject l (g/l.block) stage) e = true :=
    by simpa only [Bool.not_eq_false] using hMarked
  obtain ⟨site, kind⟩ := e
  cases kind <;> simp only [scoreCommitOn, Bool.false_eq_true] at hMark
  case tc op =>
    cases op <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hMark
    case commit earlier =>
      have hScore : ScoreCommit l X (g,j) (g/l.block) stage earlier 0 :=
        ⟨⟨site, hActual⟩, hMark⟩
      obtain ⟨block, hStage, hDecoded⟩ := scoreCommitSite hp hX hScore
      by_cases hOpening : block.val < 2
      · have hBlock : block = initialQkBlock stage := Fin.ext (by
          change block.val = stage.val
          omega)
        subst block
        obtain ⟨hPos', inst', leader', hEarlier, _⟩ :=
          scoreCommitLeader hp hX (initialQkBlock stage) hDecoded
        exact openingElectionNotRepeated hX stage hEarlier hElection (by omega)
      · have hFloor : openingFloor stage ≤ (commitSite (qkCommitSite block)).pc := by
          fin_cases stage <;> fin_cases block <;> first | decide | contradiction
        have hEarly := traceOrderOfPcFloor hX (openingBranchAudit stage)
          (openingSegmentAudit stage) hElection hDecoded (Nat.lt_succ_self _) hFloor
        omega

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
