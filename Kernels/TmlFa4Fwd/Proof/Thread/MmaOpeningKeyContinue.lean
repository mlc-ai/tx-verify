-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningKeyReturn
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue Prologue
open Thread.Mma (InitialRelease)

noncomputable section

/-- The opening key return leaves every MMA lane at the common next checkpoint. -/
theorem openingKeyReleaseAndContinueFromWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hReached : OpeningInitialKeyReturnReached l X g shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2275 (fun _ => [(2535,b32 l.sharedBase)])
      shuffles votes ends) ∧
    ∃ issuer index, SameWarp l g issuer ∧
      InitialRelease X issuer index (commitSpec l issuer (l.sharedBase+56)) ∧
      TcCommit.target (commitSpec l issuer (l.sharedBase+56)) 0 =
        some (Thread.Mma.Observation.emptyObject l g 0) := by
  obtain ⟨cur⟩ := hReached
  have hWidth : l.sharedBase+56 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+56)%8 = 0 := by have := hp.shared.1; omega
  obtain ⟨next,issuer,index,hWarp,hCommit⟩ := commitWarpFromFreshElection hp hMax hg 2 cur
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection 4 Flow.code_2271
      (by decide +kernel) (by decide +kernel) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (by simp [commitElection,electSite]) (by simp [commitElection,electSite])
    (by simp [commitElection,electSite]) List.mem_cons_self hWidth hAlign
  refine ⟨next,issuer,index,hWarp,hCommit,?_⟩
  simp [TcCommit.target,commitSpec,hWarp.1.2.2.symm]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Mma
