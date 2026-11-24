-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionDrain
public import Kernels.TmlFa4Fwd.Proof.Progress.OutputRoleExit
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputFreeTerminal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
include hp hMax hOutputs

/-- The two real correction cohorts publish every row of their single-visit surfaces. -/
theorem singleVisitOutputPublicationsOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∀ stage : Fin 2, ∀ row < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) row,j) stage := by
  intro stage row hRow
  let lane := Thread.Output.sourceLane l (g,0) row
  have hCta : lane/l.block = g/l.block := by
    dsimp only [lane,Thread.Output.sourceLane,Prod.fst]
    rw [hp.block]
    omega
  have hOffset : lane%l.block = 256+row := by
    dsimp only [lane,Thread.Output.sourceLane,Prod.fst]
    rw [hp.block]
    omega
  have hLane : lane < l.threads :=
    (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).1 (hCta.symm ▸ NamedBar.cta_lt hg)
  have hCorr : 8 ≤ warpIndex l lane ∧ warpIndex l lane < 12 := by
    unfold warpIndex
    omega
  fin_cases stage
  · obtain ⟨d⟩ := singleVisitCorrectionFirstOutputPublishedOfMaximal hp hMax hOutputs
      hLane hCorr hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)
    exact ⟨_,d.published.ready⟩
  · obtain ⟨d⟩ := singleVisitCorrectionSecondOutputPublishedOfMaximal hp hMax hOutputs
      hLane hCorr hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)
    exact ⟨_,d.published.ready⟩

/-- The active single-visit output warp reaches its actual lane exits. -/
theorem singleVisitOutputExitsOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    Thread.Exited X g := by
  have hCuQ := ((hOutputs X hMax.1).metadataProtected hp).1
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
  exact outputExitsOfPublishedCohorts hp hMax hg hw hCuQ hActive
    (singleVisitOutputPublicationsOfMaximal hp hMax hOutputs hg hb hLo hHi hSingle)

/-- Both staging-free objects reach their released phase in a scheduled single-visit CTA. -/
theorem singleVisitOutputFreePhaseOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∀ stage : Fin 2,
      let log := X.objects (Thread.Output.freeObject l (g/l.block) stage)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1 := by
  have hCuQ := ((hOutputs X hMax.1).metadataProtected hp).1
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
  intro stage
  apply Protocol.Output.freePhaseOneOfCredits hp hMax (NamedBar.cta_lt hg) stage
  exact outputFreeCreditsOfPublishedCohorts hp hMax hg hw hCuQ hActive
    (singleVisitOutputPublicationsOfMaximal hp hMax hOutputs hg hb hLo hHi hSingle) stage

end PTX.Kernels.TmlFa4Fwd.Progress
