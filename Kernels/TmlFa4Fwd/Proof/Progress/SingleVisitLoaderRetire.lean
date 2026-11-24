-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningValueAcquire
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTerminalOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderDrainReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstDrainRetire
import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningKeyReturn
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTailValue
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSingleVisitLoaderRelease
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryEmptyFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderEmptyFaults
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Epilogue Thread.Loader
open Protocol.Loader (UnitRelease queryDrainReadyOfUnitRelease cacheDrainReadyOfSingleVisitBudget)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

private theorem unitReleaseOfCommit {issue : EvId} {spec : TcCommit.Spec} {loc : Loc}
    (hCommit : X.Commit issue spec) (hTarget : TcCommit.target spec 0 = some loc)
    (hClean : ∀ r ∈ X.objects loc, r.fault = none) : UnitRelease X loc := by
  have hArrive := (mmaAndCommitsDrained hp hMax hFrame).2 _ _ 0 loc hCommit hTarget
  obtain ⟨pc,he⟩ := hCommit
  have hAction : objectAction X X.async loc (.async issue (.tcNotify 0)) =
      some (.arrive 1 0) := by simp [objectAction,he,hTarget,hArrive]
  obtain ⟨_,r,hr,_,ha⟩ := MbarOneShot.Hist.record_of_action hMax.1 hAction
  exact ⟨r,List.mem_of_getElem? hr,ha,hClean r (List.mem_of_getElem? hr)⟩

set_option maxRecDepth 4096 in
private theorem terminalValueReleaseOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∃ issuer index, SameWarp l g issuer ∧ X.Commit (issuer,index)
      (Mma.commitSpec l issuer (l.sharedBase+64)) := by
  obtain ⟨_,_,_,⟨c⟩⟩ :=
    singleVisitFirstTailPvLeaderOfMaximal hp hMax hFrame hg hw hb hLo hHi hSingle
  have hc := NamedBar.cta_lt hg
  have ht₀ := singleVisitOpeningTailProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 0
  have hm₁ := singleVisitOpeningMainProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 1
  have ht₁ := singleVisitOpeningTailProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 1
  obtain ⟨_,⟨last⟩,_⟩ := Mma.terminalPvPacketsOfMaximal hp hMax hg hw c ht₀ hm₁ ht₁
  exact Mma.terminalValueReleaseOfCursor hp hMax hg last

set_option maxRecDepth 4096 in
/-- All releases needed to retire a single-visit loader are ready in a maximal execution. -/
theorem singleVisitLoaderDrainReadyOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    CacheDrainReady l X g 2 ∧ QueryDrainReady l X g 0 := by
  let mma := g/l.block*l.block+384
  have hLane : 384 < l.block := by rw [hp.block]; decide
  have hm : mma < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  change mma/l.block = g/l.block at hCta
  have hw : warpIndex l mma = 12 := by unfold warpIndex mma; rw [hLocal]
  have hLow := hCta.symm ▸ hLo
  have hHigh := hCta.symm ▸ hHi
  have hOne := hCta.symm ▸ hSingle
  obtain ⟨ki,kj,ks,hK,anchor,_,k,hKr,_,hKa,hKf⟩ :=
    openingKeyReleasedOfMaximal hp hMax hFrame hm hw hb hLow hHigh
  obtain ⟨_,_,_,⟨cur⟩⟩ :=
    openingKeyReturnedWithTripsOfMaximal hp hMax hFrame hm hw hb hLow hHigh
  have hKV : ∀ slot : Fin 3, Thread.Mma.Observation.emptyObject l mma slot =
      Thread.Mma.Observation.emptyObject l g slot := by
    intro slot
    change initObject l (mma/l.block) _ = initObject l (g/l.block) _
    rw [hCta]
  rw [hKV] at hKr
  obtain ⟨vi,vj,hV,hValue⟩ :=
    terminalValueReleaseOfMaximal hp hMax hFrame hm hw hb hLow hHigh hOne
  have hValueCta := hV.1.2.2.symm.trans hCta
  have hValueTarget : TcCommit.target (Mma.commitSpec l vi (l.sharedBase+64)) 0 =
      some (Thread.Mma.Observation.emptyObject l g 1) := by
    change TcCommit.target (Mma.commitSpec l vi (l.sharedBase+64)) 0 =
      some (initObject l (g/l.block) (TmlFa4Fwd.Loader.emptySlot 1))
    rw [TmlFa4Fwd.Loader.emptySlot_address]
    simp [Mma.commitSpec,TcCommit.target,hValueCta,Nat.add_assoc]
  have hValueRelease := unitReleaseOfCommit hp hMax hFrame hValue hValueTarget
    (fun _ => Protocol.LoaderReady.emptyHistoryClean hp hMax.1 g 1)
  have hBudget := Thread.Mma.singleVisitReadyBudget hp hMax.1 hw (hOne ▸ cur) hK
  have hAnchor : Thread.Mma.ReleaseIssue X ki kj .firstKey ks := anchor
  refine ⟨cacheDrainReadyOfSingleVisitBudget hp hMax hg hAnchor
    (hCta.symm.trans hK.1.2.2) hBudget ⟨k,hKr,hKa,hKf⟩ hValueRelease,?_⟩
  obtain ⟨hQuery,_⟩ := singleVisitOpeningTailValueOfMaximal hp hMax hFrame hm hw hb
    hLow hHigh hOne
  obtain ⟨qi,qj,hQ,hQueryCommit⟩ := hQuery 1
  have hQueryCta := hQ.1.2.2.symm.trans hCta
  have hQueryTarget : TcCommit.target (Mma.commitSpec l qi
      (l.sharedBase+16+8*(1 : Fin 2).val)) 0 = some (secondQueryEmpty l (g/l.block)) := by
    simp [Mma.commitSpec,TcCommit.target,secondQueryEmpty,queryEmptyObject,hQueryCta,Nat.add_assoc]
  exact queryDrainReadyOfUnitRelease hp hMax hg
    (unitReleaseOfCommit hp hMax hFrame hQueryCommit hQueryTarget
      (fun _ => Protocol.Query.queryEmptyHistoryClean hp hMax.1 1))

end PTX.Kernels.TmlFa4Fwd.Progress
