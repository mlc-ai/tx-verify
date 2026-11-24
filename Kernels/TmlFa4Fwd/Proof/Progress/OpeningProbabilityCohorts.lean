-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningMainProbability
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityTail
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringProbabilityCohorts
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier PTX.Flow Prologue Thread.Scores
open Protocol.Scores (ProbabilityCohort)

private theorem firstProbabilityCreditOfIssued {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    {g j cta : Nat} (stage packet : Fin 2)
    (hIssued : ProbabilityCredit l X (g,j) cta stage packet) :
    ∃ i, ProbabilityCredit l X (g,i) cta stage packet ∧
      probabilityOrdinal l X cta stage packet (g,i) = 0 := by
  let loc := probabilityObject l cta stage packet
  obtain ⟨pc,hEvent⟩ := hIssued
  have hEx : ∃ i e, (X.tr g)[i]? = some e ∧ arrivesOn loc e = true :=
    ⟨j,_,hEvent,by simp [sourceArrive,loc]⟩
  have hPos : 0+1 ≤ (X.tr g).countP (arrivesOn loc) := by
    by_contra! hEmpty
    have hZero : (X.tr g).countP (arrivesOn loc) = 0 := by omega
    obtain ⟨i,e,he,hMark⟩ := hEx
    have hNone := (List.countP_eq_zero.mp hZero) e (List.mem_of_getElem? he)
    simp [hMark] at hNone
  exact Protocol.Scores.probabilityCreditOfExtent hp hX stage packet hPos

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {cta batch : Nat}
    (hc : cta < l.grid)
include hp hMax hFrame hc

/-- The opening softmax and correction arrivals supply the entire logical main
cohort of generation zero. -/
theorem openingMainProbabilityCohortOfMaximal (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    ProbabilityCohort l X cta stage 0 0 := by
  apply Protocol.Scores.mainProbabilityCohortOfProducers hp stage
  intro g hCta hRole
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hLane : g%l.block < l.block := Nat.mod_lt _ hBlock
  have hThread : g < l.threads := by
    have hh := NamedBar.cta_thread_lt hc hLane
    have hEq := Nat.mod_add_div g l.block
    rw [hCta,Nat.mul_comm,Nat.add_comm] at hEq
    rwa [hEq] at hh
  have hIssued : ∃ j, ProbabilityCredit l X (g,j) (g/l.block) stage 0 := by
    rcases hRole with hSoftmax | hCorrection
    · exact openingProbabilityCreditOfMaximal hp hMax hFrame hThread stage hSoftmax.2 hb
        (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)
    · exact Correction.openingJointProbabilityCreditOfMaximal hp hMax hThread
        hCorrection.1 hCorrection.2 stage
  obtain ⟨j,hCredit⟩ := hIssued
  exact firstProbabilityCreditOfIssued hp hMax.1 stage 0 (hCta ▸ hCredit)

/-- The selected opening tail arrival of each softmax warp supplies the actual
generation-zero tail cohort. -/
theorem openingTailProbabilityCohortOfMaximal (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    ProbabilityCohort l X cta stage 1 0 := by
  apply Protocol.Scores.tailProbabilityCohortOfWarps stage
  intro w
  let lane := (4*stage.val+w.val)*32
  let g := cta*l.block+lane
  have hStage := stage.isLt
  have hWarp := w.isLt
  have hLane : lane < l.block := by rw [hp.block]; dsimp only [lane]; omega
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hLane
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hLane
  change g/l.block = cta at hOwner
  change g%l.block = lane at hLocal
  have hIndex : warpIndex l g = 4*stage.val+w.val := by
    rw [warpIndex,hLocal]
    dsimp only [lane]
    omega
  have hRole : warpIndex l g/4 = stage.val := by rw [hIndex]; omega
  obtain ⟨peer,j,hSame,hCredit⟩ := openingProbabilityTailCreditOfMaximal hp hMax hFrame
    hg stage hRole hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
  obtain ⟨i,hFirst,hOrdinal⟩ := firstProbabilityCreditOfIssued hp hMax.1 stage 1
    (hOwner ▸ hCredit)
  have hSameWarp : warpIndex l g = warpIndex l peer := hSame.2
  refine ⟨(peer,i),hFirst,hOrdinal,?_⟩
  change warpIndex l peer % 4 = w.val
  rw [←hSameWarp,hIndex]
  omega

/-- Both opening stages publish both packets for generation zero in every
active CTA, independently of the number of selected KV trips. -/
theorem openingProbabilityCohortOfMaximal (stage packet : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    ProbabilityCohort l X cta stage packet 0 := by
  fin_cases packet
  · exact openingMainProbabilityCohortOfMaximal hp hMax hFrame hc stage hb hLo hHi
  · exact openingTailProbabilityCohortOfMaximal hp hMax hFrame hc stage hb hLo hHi

end PTX.Kernels.TmlFa4Fwd.Progress
