-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSecondScoreReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningKeyReturn
import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderEmptyFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier PTX.AsyncCopy Prologue
open Thread.Mma.Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hFrame hg hw hb hLo

/-- The initial K slot is returned by the active MMA warp after both opening QK packets. -/
theorem openingKeyReleasedOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ issuer index spec, SameWarp l g issuer ∧ Thread.Mma.InitialRelease X issuer index spec ∧
      TcCommit.target spec 0 = some (emptyObject l g 0) ∧
      ∃ r ∈ X.objects (emptyObject l g 0),
        r.id = .async (issuer,index) (.tcNotify 0) ∧ r.action = .arrive 1 0 ∧ r.fault = none := by
  obtain ⟨_,_,_,hReached,_⟩ :=
    openingSecondScoreAndKeyReturnOfMaximal hp hMax hFrame hg hw hb hLo hHi
  obtain ⟨issuer,index,hWarp,hIssue,hTarget⟩ := Mma.openingKeyReleaseFromWarp hp hMax hg hReached
  let spec := Mma.commitSpec l issuer (l.sharedBase+56)
  let loc := emptyObject l g 0
  change TcCommit.target spec 0 = some loc at hTarget
  have hCommit : X.Commit (issuer,index) spec := ⟨_,hIssue⟩
  obtain ⟨_,hNote⟩ := mmaAndCommitsDrained hp hMax hFrame
  have hArrive := hNote _ _ 0 loc hCommit hTarget
  have hAction : objectAction X X.async loc (.async (issuer,index) (.tcNotify 0)) =
      some (.arrive 1 0) := by
    obtain ⟨_,hGet⟩ := hCommit
    simp [objectAction,hGet,hTarget,hArrive]
  obtain ⟨r,hr,hId⟩ := (hMax.1.tma.2.2.1 loc).2.2 _ _ hAction
  have hMatch := ((hMax.1.tma.2.2.1 loc).2.1 r hr).1
  rw [hId,hAction] at hMatch
  exact ⟨issuer,index,spec,hWarp,hIssue,hTarget,r,hr,hId,(Option.some.inj hMatch).symm,
    Protocol.LoaderReady.emptyHistoryClean hp hMax.1 g 0 hr⟩

end PTX.Kernels.TmlFa4Fwd.Progress
