-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryDrainRelease
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
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
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitTargets
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryReleaseOnce
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The physical commit that returns one of the CTA's query planes to the loader. -/
def QueryReturn (l : Launch) (X : Execution) (i : EvId) (stage : Fin 2)
    (spec : TcCommit.Spec) (rank : Fin 16) : Prop :=
  X.Commit i spec ∧ TcCommit.target spec rank = some (Loader.queryEmptyObject l (i.1/l.block) stage)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem queryReturnSite {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hi : QueryReturn l X i stage spec rank) :
    X.get i = some ⟨(commitSite (queryReleaseSite stage)).pc, .tc (.commit spec)⟩ := by
  obtain ⟨⟨pc, he⟩, ht⟩ := hi
  rcases inCommitSites hX he with hFixed | hRing
  · have hLoc := mmaFixedCommitExactAddress hp hX he hFixed ht
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (16 + 8 * stage.val) = l.sharedBase + fixedMmaCommitOffset pc at hAddr
    have audit : ∀ pc ∈ fixedCommits, ∀ s : Fin 2, 16 + 8 * s.val = fixedMmaCommitOffset pc →
        pc = (commitSite (queryReleaseSite s)).pc := by decide
    rwa [audit pc hFixed stage (Nat.add_left_cancel hAddr)] at he
  · obtain ⟨slot, hLoc⟩ := mmaRingCommitAddress hp hX he hRing ht
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (16 + 8 * stage.val) = l.sharedBase + (8 * slot.val + 56) at hAddr
    have := stage.isLt
    omega

private theorem queryReturnActor {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hi : QueryReturn l X i stage spec rank) :
    i.1 < l.threads ∧ warpIndex l i.1 = 12 ∧
      ∃ k source inst, X.Elect (i.1,k) source (2 ^ 32 - 1) inst (laneOf l i.1) := by
  obtain ⟨g,j⟩ := i
  have he := queryReturnSite hp hX hi
  let pc := (commitSite (queryReleaseSite stage)).pc
  have hAudit : ∀ stage : Fin 2,
      let pc := (commitSite (queryReleaseSite stage)).pc
      1908 ≤ pc ∧ pc < 2768 ∧ pc ∉ registerHintSites := by decide
  obtain ⟨hLo, hHi, hHint⟩ := hAudit stage
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < pc; omega) hHint
  change roleBodyPc (warpIndex l g) pc at hRole
  have hw : warpIndex l g = 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨_, inst, leader, hElect, hLane⟩ := queryReleaseLeader hp hX stage he
  exact ⟨event_thread_lt hX he, hw, j-1, _, inst, hLane.symm ▸ hElect⟩

private theorem queryReturnRank {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hi : QueryReturn l X i stage spec rank) : rank = 0 := by
  obtain ⟨_, hSingle⟩ := commitTargetSingle hp hX hi.1
  have ht := hi.2
  rw [hSingle rank] at ht
  split at ht
  · rename_i h
    exact Fin.ext h
  · cases ht

/-- A physical query return is unique at its stage and CTA. -/
theorem queryReturnUnique {i j : EvId} {stage : Fin 2} {a b : TcCommit.Spec} {rank other : Fin 16}
    (hi : QueryReturn l X i stage a rank) (hj : QueryReturn l X j stage b other)
    (hCta : i.1 / l.block = j.1 / l.block) : i = j ∧ rank = other :=
  ⟨queryReleaseEventUnique hp hX stage hCta (queryReturnSite hp hX hi) (queryReturnSite hp hX hj),
    (queryReturnRank hp hX hi).trans (queryReturnRank hp hX hj).symm⟩

/-- The query return issuer first acquired Q0 for the same active tile. -/
theorem queryReturnInitialAcquire {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hi : QueryReturn l X i stage spec rank) :
    ∃ wait e, wait.1 = i.1 ∧ X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (wait.1 / l.block) 0) 0 true true .cta := by
  obtain ⟨g, j⟩ := i
  have he := queryReturnSite hp hX hi
  have range : ∀ stage : Fin 2,
      let pc := (commitSite (queryReleaseSite stage)).pc
      2145 ≤ pc ∧ pc ≤ 2642 := by decide
  obtain ⟨k, _, loc, phase, hGet, _⟩ :=
    firstQueryWaitBeforeGate hp hX he (range stage).1 (range stage).2
  obtain ⟨rfl, rfl⟩ := firstQueryPollOperands hp hX hGet
  exact ⟨(g,k), _, rfl, hGet, by simp [Output.queryObject]⟩

omit hp hX in
private theorem queryReturnFloor (floor : Nat) (h : floor = 2537 ∨ floor = 2541 ∨ floor = 2542) :
    (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

omit hp hX in
private theorem queryReturnSegments (floor : Nat)
    (h : floor = 2537 ∨ floor = 2541 ∨ floor = 2542) :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Under the existing commit-order assumption, the observed second query return
completes the first query return at the same rank. -/
theorem queryReturnCommitNext {i j : EvId} {a b : TcCommit.Spec} {rank other : Fin 16}
    (hi : QueryReturn l X i 0 a rank) (hj : QueryReturn l X j 1 b other)
    (hCta : i.1 / l.block = j.1 / l.block) (hDone : other ∈ X.tcNotified j) :
    rank = other ∧ CommitNext Assumptions.all X (.async i (.tcNotify rank))
      (.async j (.tcNotify other)) := by
  obtain ⟨hg, hw, k, src, inst, hx⟩ := queryReturnActor hp hX hi
  obtain ⟨hg', hw', k', src', inst', hy⟩ := queryReturnActor hp hX hj
  have hWarp : SameWarp l i.1 j.1 := ⟨⟨hg, hg', hCta⟩, hw.trans hw'.symm⟩
  have hLane := sameWarp_eq_of_lane_eq hWarp (sameLeader hX hWarp hx hy)
  have hRank := (queryReturnRank hp hX hi).trans (queryReturnRank hp hX hj).symm
  subst other
  obtain ⟨g, index⟩ := i
  obtain ⟨g', index'⟩ := j
  change g = g' at hLane
  subst g'
  have he := queryReturnSite hp hX hi
  have he' := queryReturnSite hp hX hj
  change X.get (g,index) = some ⟨2537,.tc (.commit a)⟩ at he
  change X.get (g,index') = some ⟨2541,.tc (.commit b)⟩ at he'
  have order {floor : Nat} (h : floor = 2537 ∨ floor = 2541 ∨ floor = 2542)
      {i j : Nat} {e f : Event} (he : X.get (g,i) = some e) (hf : X.get (g,j) = some f)
      (hLo : e.pc < floor) (hHi : floor ≤ f.pc) : i < j :=
    traceOrderOfPcFloor hX (queryReturnFloor _ h) (queryReturnSegments _ h) he hf hLo hHi
  have hOrder := order (.inr (.inl rfl) : 2541 = 2537 ∨ 2541 = 2541 ∨ 2541 = 2542)
    he he' (by change 2537 < 2541; decide) (by change 2541 ≤ 2541; decide)
  have hNo : ∀ k, index < k → k < index' → ¬ ∃ s, X.Commit (g,k) s := by
    intro j hLo hHi
    rintro ⟨s, site, hGet⟩
    have audit : ∀ pc ∈ fixedCommits ++ ringCommits, pc < 2537 ∨ pc = 2537 ∨ pc = 2541 ∨
        2542 ≤ pc := by decide
    rcases audit site (List.mem_append.mpr (inCommitSites hX hGet)) with hlo | rfl | rfl | hhi
    · exact (Nat.not_lt_of_ge hLo.le (order (.inl rfl) hGet he hlo (Nat.le_refl _))).elim
    · have hEq := queryReleaseOnceInLane hp hX 0 hLo.le he hGet
      omega
    · have hEq := queryReleaseOnceInLane hp hX 1 hHi.le hGet he'
      omega
    · exact (Nat.not_lt_of_ge hHi.le
        (order (.inr (.inr rfl)) he' hGet (by change 2541 < 2542; decide) hhi)).elim
  have hMember : Assumptions.commitOrder ∈ Assumptions.all := by
    simp [Assumptions.all, Assumptions.synchronization]
  have hAssumption := hX.asm Assumptions.commitOrder hMember
  change Assumption.commitPerformedAt Assumptions.commitOrderSites X at hAssumption
  have hEarlier := hAssumption g index index' 2537 a rank he (by decide) hOrder ⟨b, hj.1⟩
    hNo hDone
  exact ⟨rfl, rfl, rfl, hOrder, hEarlier, hDone, ⟨2537, a, he, by decide⟩,
    ⟨b, hj.1⟩, hNo⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
