-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollOrder
import Kernels.TmlFa4Fwd.Proof.LoaderDrainPollUniformity
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyShuffleAlignment
import Lemmas.Flow.PollSynced

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Assumption Prologue

private theorem checkedPollGuards : kernel.pollGuardsOk = true := by
  decide +kernel

private theorem checkedPollSelection :
    kernel.code.zipIdx.all (fun (ins, site) =>
      !ins.laneCompared || Assumptions.pollAgreeSites.contains site) = true := by
  decide +kernel

private theorem pollBranchSelected {site : Nat} (hPoll : kernel.pollBranch site = true) :
    Assumptions.all.any (·.uniPoll site) = true := by
  obtain ⟨_, _, dst, neg, target, _, _, _, _, _, hc, _⟩ := PTX.pollBranch_spec hPoll
  have hMember : ((⟨some (dst, neg), .bra target true⟩ : Instr), site) ∈ kernel.code.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hc
  have h := List.all_eq_true.mp checkedPollSelection _ hMember
  rw [Assumptions.all_uniPoll]
  change false || Assumptions.pollAgreeSites.contains site = true at h
  exact h

private theorem checkedSegmentLandings :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => !kernel.pollBranch seg.stop
      | none => false) = true := by decide +kernel

private theorem localLands {l : Launch} : LocalLands kernel Assumptions.all l := by
  have segmentLands {s u : TState} {seg : SegMatch CuteSlot}
      (hSite : s.pc ∈ Assumptions.swExp2Sites)
      (hMatch : cuteExp2.matchAt kernel s.pc = some seg)
      (hSeg : Assumptions.execSwExp2 seg s = .ok u) :
      kernel.pollBranch u.pc = false := by
    have h := List.all_eq_true.mp checkedSegmentLandings _ hSite
    rw [hMatch] at h
    simpa only [(Softmax.scoreSegmentFrame hSeg).1, Bool.not_eq_true'] using h
  constructor
  · intro g s ins u hc hExec
    rcases Softmax.scoreExecLocal hExec with hFrame | ⟨_, hSite, hMatch, hSeg⟩
    · exact PTX.LocalFrame.lands hc hFrame
    · exact .inr (segmentLands hSite hMatch hSeg)
  · intro g s ins values u hc hExec
    rcases Softmax.scoreExecLocal hExec with hFrame | ⟨_, hSite, hMatch, hSeg⟩
    · exact PTX.LocalFrame.lands_sreg hc hFrame
    · exact .inr (segmentLands hSite hMatch hSeg)

private def loaderDrainWaitSites : List Nat := [1866,1877,1888]

/-- Ordinary waits agree on the initialized object. The cache ring's recurring
waits either agree or have a separating warp dependency. Its drain waits agree
on the final cursor. -/
theorem noWarpDivergenceOfPollAgreement {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y) :
    ¬ WarpDivergent l kernel Assumptions.all X := by
  apply not_warpDivergent_synced checkedPollGuards localLands
  intro g h i j site m m' parity parity' ok ok' acq acq' scope scope' hg hh hNe hWarp
    he hf hBranch hObjects
  rw [pollBranchSelected hBranch, Bool.true_eq_false, or_false] at hObjects
  have hRing := (waitObjectAgreementOrRing hp hX hWarp he hf).resolve_left hObjects
  rcases List.mem_append.mp hRing with hLoader | hMma
  · have hSplit := (by decide : ∀ pc ∈ loaderCacheRingWaitSites,
        pc ∈ loaderDrainWaitSites ∨
          ∃ r : Fin 4, pc = (TmlFa4Fwd.Loader.recurringEmptyWait r).pc) site hLoader
    rcases hSplit with hDrain | hRecurring
    · exact (hObjects (Loader.drainPollObjectsAgree hp hX hFrame hComplete hWarp he hf
        hDrain)).elim
    · exact (Loader.recurringPollObjectsAgreeOrOrdered hp hX (hFrame X hX) hWarp he hf hRecurring)
        |>.resolve_left hObjects
  · have hSite := (by decide : ∀ site ∈ mmaCacheRingWaitSites,
        1908 ≤ site ∧ site < 2768 ∧ site ∉ registerHintSites) site hMma
    have hRole := roleBodyPcOfEvent hp hX he (show 173 < site by omega) hSite.2.2
    change roleBodyPc (warpIndex l g) site at hRole
    have hMmaWarp : warpIndex l g = 12 := by
      unfold roleBodyPc at hRole
      rcases hRole with hExit | hRole
      · omega
      · split_ifs at hRole <;> omega
    have hGate := (by decide : ∀ site ∈ mmaCacheRingWaitSites, ∃ r : Fin 4,
      site = TmlFa4Fwd.Mma.readyHead r) site hMma
    exact (Mma.readyPollObjectsAgreeOrOrdered hp hX hWarp hMmaWarp he hf hGate)
      |>.resolve_left hObjects

end PTX.Kernels.TmlFa4Fwd.Thread
