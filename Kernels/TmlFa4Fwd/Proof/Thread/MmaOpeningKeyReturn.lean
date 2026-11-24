-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondScoreIssue
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseUse
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.TcIssueProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue Prologue
open Thread.Mma (InitialRelease)

noncomputable section

/-- The opening MMA warp elects an issuer and records the release of physical key slot zero. -/
theorem openingKeyReleaseFromWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hReached : OpeningInitialKeyReturnReached l X g shuffles votes ends) :
    ∃ issuer index, SameWarp l g issuer ∧
      InitialRelease X issuer index (commitSpec l issuer (l.sharedBase+56)) ∧
      TcCommit.target (commitSpec l issuer (l.sharedBase+56)) 0 =
        some (Thread.Mma.Observation.emptyObject l g 0) := by
  obtain ⟨cur⟩ := hReached
  let frame := [(2535,b32 l.sharedBase)]
  let afterFrame := fun lane leader =>
    ((electSite 4).pred,.pred (laneOf l (warpLane l g lane) == leader)) :: frame
  have hPred : ∀ pair ∈ frame, pair.1 ≠ (electSite 4).pred := by simp [frame,electSite]
  have hResult : ∀ pair ∈ frame, pair.1 ∉ (electSite 4).result.toList := by simp [frame,electSite]
  obtain ⟨leader,elected,_⟩ := cur.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (cur.state lane) 4) afterFrame
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection 4 Flow.code_2271
      (by decide +kernel) (by decide +kernel) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 4 (cur.checkpoint lane hl))
    (fun lane hl k => electStateFrame 4 (cur.checkpoint lane hl) k hPred hResult)
  let lane := leader.val
  let issuer := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg leader.isLt
  have hLead : (laneOf l issuer == leader.val) = true := beq_iff_eq.mpr hLane
  have hAt := elected.checkpoint lane leader.isLt
  change At (elected.state lane) 2272
    (((electSite 4).pred,.pred (laneOf l issuer == leader.val)) :: frame) at hAt
  rw [hLead] at hAt
  obtain ⟨u,hu,hU⟩ := commitGate 2 true hAt (by simp [frame,electSite,commitElection])
  have hs := hp.shared.2.1
  have ha := hp.shared.1
  let spec := commitSpec l issuer (l.sharedBase+56)
  have hn : Next kernel Assumptions.all l issuer (elected.before lane) u
      (.tc (.commit spec) (next u)) :=
    ⟨(elected.localSteps lane leader.isLt).trans (run_rtg hu),
      commitTemplate hp hWarp.1.2.1 2 (a := l.sharedBase) hU List.mem_cons_self
        (by change l.sharedBase+56 < 2^32; omega)
        (by change (l.sharedBase+56)%8=0; omega)⟩
  obtain ⟨hCommit,_,_⟩ := Step.tc_issue_of_maximal hMax hWarp.1.2.1 hn rfl
    (elected.recorded lane leader.isLt) (elected.continuation lane leader.isLt)
    (elected.positive lane leader.isLt) (elected.bounded lane leader.isLt)
    (elected.released lane leader.isLt) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
      (Execution.noNewRead_snoc rfl))
  have hCta : issuer/l.block = g/l.block := hWarp.1.2.2.symm
  refine ⟨issuer,elected.pos lane,hWarp,?_,?_⟩
  · have hSite : u.pc = 2274 := hU.1
    rw [hSite] at hCommit
    exact hCommit
  · simp [TcCommit.target,commitSpec,hCta]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Mma

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof
open Observation (emptyObject)

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
