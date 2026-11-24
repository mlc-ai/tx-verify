-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
public import Kernels.TmlFa4Fwd.Proof.MmaCommit
public import Kernels.TmlFa4Fwd.Proof.MmaQkCommit
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.CommitTarget
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitTargets
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- A score issue is a real Tensor Core commit targeting the selected score object. -/
def ScoreCommit (l : Launch) (X : Execution) (issue : EvId) (cta : Nat) (stage : Fin 2)
    (spec : TcCommit.Spec) (rank : Fin 16) : Prop :=
  X.Commit issue spec ∧ TcCommit.target spec rank = some (scoreReadyObject l cta stage)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The score commit selects one of the two decoded issuances of its stage. -/
theorem scoreCommitSite (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X issue cta stage spec rank) :
    ∃ block : Fin 4, block.val % 2 = stage.val ∧
      X.get issue = some ⟨(commitSite (qkCommitSite block)).pc, .tc (.commit spec)⟩ := by
  obtain ⟨⟨pc, he⟩, hTarget⟩ := hIssue
  rcases inCommitSites hX he with hFixed | hRing
  · have hFixed' : pc ∈ [2208, 2270, 2274, 2418, 2519, 2537, 2541, 2642, 2646] := hFixed
    have hLoc := mmaFixedCommitExactAddress hp hX he hFixed' hTarget
    have hAddr : l.sharedBase + (80 + 8 * stage.val) =
        l.sharedBase + fixedMmaCommitOffset pc := congrArg Loc.addr hLoc
    have hOffset := Nat.add_left_cancel hAddr
    have audit : ∀ stage : Fin 2, ∀ pc ∈ fixedCommits,
        80 + 8 * stage.val = fixedMmaCommitOffset pc →
        ∃ block : Fin 4, block.val % 2 = stage.val ∧
          pc = (commitSite (qkCommitSite block)).pc := by decide
    obtain ⟨b, hb, rfl⟩ := audit stage pc hFixed hOffset
    exact ⟨b, hb, he⟩
  · obtain ⟨slot, hLoc⟩ := mmaRingCommitAddress hp hX he hRing hTarget
    have hAddr : l.sharedBase + (80 + 8 * stage.val) =
        l.sharedBase + (8 * slot.val + 56) := congrArg Loc.addr hLoc
    have := slot.isLt
    omega

/-- A score commit is issued by the lane chosen in its full-warp election. -/
theorem scoreCommitActor (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {e : EvId}
    {cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) :
    e.1 / l.block = cta ∧ warpIndex l e.1 = 12 ∧
      ∃ k source inst, X.Elect (e.1,k) source (2 ^ 32 - 1) inst (laneOf l e.1) := by
  obtain ⟨block, _, he⟩ := scoreCommitSite hp hX hIssue
  obtain ⟨_, _, _, hOwner⟩ := actualCommitOffset hp hX he hIssue.2
  have hCta : e.1 / l.block = cta := (congrArg Loc.cta hOwner).symm
  have hPc (block : Fin 4) :
      let pc := (commitSite (qkCommitSite block)).pc
      2145 ≤ pc ∧ pc < 2768 ∧ pc ∉ registerHintSites := by fin_cases block <;> decide
  obtain ⟨hLo, hHi, hHint⟩ := hPc block
  have hWarp : warpIndex l e.1 = 12 := by
    rcases roleBodyPcOfEvent hp hX he (by dsimp; omega) hHint with h | h
    · dsimp at h; omega
    · split_ifs at h <;> dsimp at h <;> omega
  obtain ⟨_, inst, leader, hElect, hLane⟩ := scoreCommitLeader hp hX block
    (g := e.1) (index := e.2) he
  exact ⟨hCta,hWarp,e.2-1,_,inst,hLane.symm ▸ hElect⟩

/-- All score-ready commits in a CTA come from the same physical elected MMA lane. -/
theorem scoreCommitSameIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e f : EvId} {cta : Nat} {stage other : Fin 2} {a b : TcCommit.Spec} {rank rank' : Fin 16}
    (he : ScoreCommit l X e cta stage a rank) (hf : ScoreCommit l X f cta other b rank') :
    e.1 = f.1 := by
  obtain ⟨hCta, hWarp, k, src, inst, hx⟩ := scoreCommitActor hp hX he
  obtain ⟨hCta', hWarp', k', src', inst', hy⟩ := scoreCommitActor hp hX hf
  obtain ⟨_, he'⟩ := he.1
  obtain ⟨_, hf'⟩ := hf.1
  have hw : SameWarp l e.1 f.1 :=
    ⟨⟨event_thread_lt hX he', event_thread_lt hX hf', hCta.trans hCta'.symm⟩,
      hWarp.trans hWarp'.symm⟩
  exact sameWarp_eq_of_lane_eq hw (sameLeader hX hw hx hy)

/-- The physical score target of a commit, independent of its decoded source. -/
def scoreCommitOn (object : Loc) (e : Event) : Bool :=
  match e.kind with
  | .tc (.commit spec) => decide (TcCommit.target spec 0 = some object)
  | _ => false

/-- Number of previous score commits to the same target on this issuing lane. -/
def scoreCommitOrdinal (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (e : EvId) : Nat :=
  ((X.tr e.1).take e.2).countP (scoreCommitOn (scoreReadyObject l cta stage))

/-- A score notification uses rank zero, which is the rank used to count its issue. -/
theorem scoreCommitRankZero (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {spec : TcCommit.Spec} {cta : Nat} {stage : Fin 2} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) :
    rank = 0 ∧ ScoreCommit l X e cta stage spec 0 := by
  obtain ⟨loc, hSingle⟩ := Thread.commitTargetSingle hp hX hIssue.1
  have hTarget := hIssue.2
  rw [hSingle rank] at hTarget
  split at hTarget
  · rename_i h
    have hz : rank = 0 := Fin.ext h
    exact ⟨hz, hz ▸ hIssue⟩
  · cases hTarget

/-- A local score commit ordinal names a unique physical notification. -/
theorem scoreCommitOrdinalInjective (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {a b : EvId} {cta : Nat} {stage : Fin 2} {sa sb : TcCommit.Spec} {ra rb : Fin 16}
    (ha : ScoreCommit l X a cta stage sa ra) (hb : ScoreCommit l X b cta stage sb rb)
    (hSame : scoreCommitOrdinal l X cta stage a = scoreCommitOrdinal l X cta stage b) :
    a = b ∧ ra = rb := by
  obtain ⟨rfl, ha⟩ := scoreCommitRankZero hp hX ha
  obtain ⟨rfl, hb⟩ := scoreCommitRankZero hp hX hb
  have hLane := scoreCommitSameIssuer hp hX ha hb
  obtain ⟨g, i⟩ := a
  obtain ⟨g', j⟩ := b
  change g = g' at hLane
  subst g'
  obtain ⟨⟨a, hGetA⟩, hTargetA⟩ := ha
  obtain ⟨⟨b, hGetB⟩, hTargetB⟩ := hb
  have hI := nthEv_unique hGetA (p := scoreCommitOn (scoreReadyObject l cta stage))
    (by simp [scoreCommitOn, hTargetA]) hGetB (by simp [scoreCommitOn, hTargetB]) hSame
  exact ⟨congrArg (fun k => (g,k)) hI, rfl⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
