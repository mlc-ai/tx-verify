-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.MmaRecurringKeyPack
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitTargets
import Lemmas.Flow.CountWindow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

noncomputable section

theorem scoreCommitAtBlock {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (block : Fin 4) (hStage : block.val % 2 = stage.val)
    {g index : Nat} {spec : TcCommit.Spec}
    (hGet : X.get (g, index) = some ⟨(commitSite (qkCommitSite block)).pc, .tc (.commit spec)⟩) :
    ScoreCommit l X (g, index) (g / l.block) stage spec 0 := by
  obtain ⟨loc, hSingle⟩ := commitTargetSingle hp hX (show X.Commit (g, index) spec from ⟨_, hGet⟩)
  have hTarget : TcCommit.target spec 0 = some loc := hSingle 0
  have hSite : (commitSite (qkCommitSite block)).pc ∈
      [2208, 2270, 2274, 2418, 2519, 2537, 2541, 2642, 2646] := by fin_cases block <;> decide
  have hLocation := mmaFixedCommitExactAddress hp hX hGet hSite hTarget
  have hOffset : fixedMmaCommitOffset (commitSite (qkCommitSite block)).pc =
      80 + 8 * stage.val := by
    fin_cases block <;> fin_cases stage <;> first | decide | contradiction
  rw [hLocation, hOffset] at hTarget
  exact ⟨⟨_, hGet⟩, hTarget⟩

/-- A recurring score commit's physical target count is one plus the corresponding
recurring score-election count. The first commit of that stage supplies the offset. -/
theorem recurringScoreExactOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) =
      some ⟨(commitSite (qkCommitSite (recurringKeyBlock stage))).pc, .tc (.commit spec)⟩) :
    scoreCommitOrdinal l X (g / l.block) stage (g, index) =
      1 + ElectOrd.siteOrdinal
        (· == (electSite (commitElection (qkCommitSite (recurringKeyBlock stage)))).pc)
        X g (index - 1) := by
  classical
  let block := recurringKeyBlock stage
  let site := qkCommitSite block
  let election := (electSite (commitElection site)).pc
  let first : Fin 4 := ⟨stage.val, stage.isLt.trans (by decide)⟩
  let init := qkCommitSite first
  let slot : Fin 4 := ⟨2 * stage.val, by have := stage.isLt; omega⟩
  have hGate : probabilityScoreElection slot = election := by fin_cases stage <;> decide
  have hUpper := scoreCommitBudgetBeforeElection hp hX (g := g) (j := index)
    (cta := g / l.block) stage 0 slot (by simp [slot])
  rw [hGate] at hUpper
  apply Nat.le_antisymm hUpper
  obtain ⟨hIndex, inst, leader, hVote, hLane⟩ := scoreCommitLeader hp hX block he
  have hWarp := (scoreCommitActor hp hX
    (scoreCommitAtBlock hp hX stage block (by fin_cases stage <;> decide) he)).2.1
  have hSite : election = 2415 ∨ election = 2516 := by fin_cases stage <;> decide
  obtain ⟨opening, hOpening, inst₀, hOpen⟩ :=
    openingScoreElectionBeforeRecurring hp hX stage hVote hSite hWarp
  have hOpenPc : (if stage = 0 then 2205 else 2267) = (electSite (commitElection init)).pc := by
    fin_cases stage <;> decide
  rw [hOpenPc] at hOpen
  have hLen : index < (X.tr g).length := len_of_get he
  obtain ⟨seed, hSeed⟩ := Mma.electedCommitOccurs hp hX init hOpen hLane (by omega)
  have hSeedScore := scoreCommitAtBlock hp hX stage first (by fin_cases stage <;> decide) hSeed
  let mark := scoreCommitOn (scoreReadyObject l (g / l.block) stage)
  let vote := ElectOrd.atSites (· == election)
  let previous := (Finset.range (index - 1)).filter (fun n =>
    ((X.tr g)[n]?).any vote = true ∧ 0 ≤ ((X.tr g).take n).countP vote)
  let commits := (Finset.range index).filter (fun n =>
    ((X.tr g)[n]?).any mark = true ∧ 0 ≤ ((X.tr g).take n).countP mark)
  have hCandidate (j : Nat) (hj : j ∈ previous) :
      ∃ s : TcCommit.Spec, X.get (g, j + 1) =
        some ⟨(commitSite site).pc, .tc (.commit s)⟩ := by
    obtain ⟨hRange, hMarked, _⟩ := Finset.mem_filter.mp hj
    have hEarlier := Finset.mem_range.mp hRange
    cases hGet : (X.tr g)[j]? with
    | none => simp [hGet] at hMarked
    | some event =>
      obtain ⟨tag, kind⟩ := event
      cases kind <;> simp [hGet, vote, ElectOrd.atSites, isElectEv] at hMarked
      case elect mask inst' leader' =>
        rcases hMarked with rfl
        have he' : X.Elect (g, j) election mask inst' leader' := hGet
        have hMask := actualFullElectionMask hX he'
        subst mask
        have hg := event_thread_lt hX he
        have hSame : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
        have hLeader := sameLeader hX hSame he' hVote
        subst leader'
        exact Mma.electedCommitOccurs hp hX site he' hLane (by omega)
  let after := fun j : Nat => j + 1
  have hMapped : previous.image after ⊆ commits := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨s, hGet⟩ := hCandidate i hi
    have hScore := scoreCommitAtBlock hp hX stage block (by fin_cases stage <;> decide) hGet
    have hRank := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by dsimp [after]; omega), ?_, Nat.zero_le _⟩
    change (X.tr g)[i + 1]? = _ at hGet
    simp [after, hGet, mark, scoreCommitOn, hScore.2]
  have hSeedIn : opening + 1 ∈ commits := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_, Nat.zero_le _⟩
    change (X.tr g)[opening + 1]? = _ at hSeed
    simp [hSeed, mark, scoreCommitOn, hSeedScore.2]
  have hDisjoint : opening + 1 ∉ previous.image after := by
    intro hk
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hk
    obtain ⟨s, hGet⟩ := hCandidate i hi
    change i + 1 = opening + 1 at hEq
    rw [hEq] at hGet
    have hBad : (commitSite site).pc = (commitSite init).pc :=
      congrArg Event.pc (Option.some.inj (hGet.symm.trans hSeed))
    fin_cases stage <;> cases hBad
  have hInclude : insert (opening + 1) (previous.image after) ⊆ commits := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hLater
    · exact hSeedIn
    · exact hMapped hLater
  have hCount := Finset.card_le_card hInclude
  have hInj : Function.Injective after := by
    intro a b h
    change a + 1 = b + 1 at h
    omega
  rw [Finset.card_insert_of_notMem hDisjoint, Finset.card_image_of_injective _ hInj,
    show previous.card = ((X.tr g).take (index - 1)).countP vote from
      (card_window _ _ 0 _).trans (Nat.sub_zero _),
    show commits.card = ((X.tr g).take index).countP mark from
      (card_window _ _ 0 _).trans (Nat.sub_zero _)] at hCount
  change 1 + ((X.tr g).take (index - 1)).countP vote ≤ ((X.tr g).take index).countP mark
  omega

/-- Each recurring K release identifies both of its real score commits with
the same semantic score ordinal, one past the recurring release occurrence. -/
theorem recurringScoreOfKeyRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec}
    (release : Mma.ReleaseIssue X g index .loopKey spec) (stage : Fin 2) :
    ∃ commit s, ScoreCommit l X (g, commit) (g / l.block) stage s 0 ∧
      scoreCommitOrdinal l X (g / l.block) stage (g, commit) =
        1 + Mma.releaseOccurrence X g index .loopKey ∧
      TraceBefore X (g, commit) (g, index) := by
  obtain ⟨commit, s, hBefore, hGet, _, hRank⟩ := release.recurringScoreCommit hp hX stage
  have hBlock : (if stage = 0 then (2 : Fin 4) else 3) = recurringKeyBlock stage := by
    fin_cases stage <;> rfl
  rw [hBlock] at hGet hRank
  exact ⟨commit, s, scoreCommitAtBlock hp hX stage (recurringKeyBlock stage)
    (by fin_cases stage <;> decide) hGet, (recurringScoreExactOrdinal hp hX stage hGet).trans
      (congrArg (1 + ·) hRank), hBefore⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
