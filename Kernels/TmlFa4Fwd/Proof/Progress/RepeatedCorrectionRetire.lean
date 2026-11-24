-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedCorrectionLse
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedCorrectionDrainOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalRetire
public import Kernels.TmlFa4Fwd.Proof.Progress.OutputRoleExit
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputFreeTerminal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The two real correction cohorts publish every row of both staging surfaces. -/
theorem repeatedOutputPublicationsOfRows (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) {issuer : Nat}
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer) :
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
  · obtain ⟨d⟩ := repeatedFirstStageStagingOfRows hp hMax hOutputs
      hLane hCorr hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ multiple)
      (hCta.symm ▸ rows) (cta.trans hCta.symm) issues
    obtain ⟨published⟩ := d.publishOfMaximal hp hMax hLane
    exact ⟨_,published.published.ready⟩
  · obtain ⟨d⟩ := repeatedCorrectionSecondOutputPublishedOfMaximal hp hMax hOutputs
      hLane hCorr hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ multiple)
      (hCta.symm ▸ rows) (cta.trans hCta.symm) issues
    exact ⟨_,d.published.ready⟩

theorem repeatedCorrectionArrivalsOfRows (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) {issuer : Nat}
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer) :
    ∀ lane < 32, Nonempty (Correction.TerminalCorrectionArrived l X (warpLane l g lane)) := by
  have hCuQ := ( (hOutputs X hMax.1).metadataProtected hp).1
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hTails (lane : Nat) (hl : lane < 32) :
      Nonempty (Correction.LseTailReached p l X (warpLane l g lane) batch) := by
    let thread := warpLane l g lane
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hCta : thread/l.block = g/l.block := hSame.1.2.2.symm
    have hWarp : warpIndex l g = warpIndex l thread := hSame.2
    exact repeatedCorrectionLseTailOfMaximal hp hMax hOutputs hSame.1.2.1
      (hWarp ▸ hw) hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ multiple)
      (hCta.symm ▸ rows) (cta.trans hCta.symm) issues
  let output := Thread.Output.outputLane l (g/l.block) 0
  have hCta : output/l.block = g/l.block := by
    dsimp only [output,Thread.Output.outputLane,Fin.val_zero,Nat.add_zero]
    rw [hp.block]
    omega
  have hOutput : output < l.threads :=
    (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).1 (hCta ▸ NamedBar.cta_lt hg)
  have hRole : warpIndex l output = 13 := by
    unfold warpIndex
    dsimp only [output,Thread.Output.outputLane,Fin.val_zero,Nat.add_zero]
    rw [hp.block]
    omega
  have publications := repeatedOutputPublicationsOfRows hp hMax hOutputs hOutput hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ multiple)
    (hCta.symm ▸ rows) (cta.trans hCta.symm) issues
  have active := hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
  have credits := outputFreeCreditsOfPublishedCohorts hp hMax hOutput hRole hCuQ
    (hCta.symm ▸ active) publications 1
  have free := Protocol.Output.freePhaseOneOfCredits hp hMax (NamedBar.cta_lt hOutput) 1 credits
  rw [hCta] at free
  obtain ⟨_,_,⟨warp⟩⟩ := repeatedCorrectionTerminalWarpOfPublications hp hMax hOutputs
    hg hw hb hLo hHi multiple rows.rescale
  obtain ⟨_,_,⟨down⟩⟩ := Correction.terminalFirstDownOfRescales hp hMax hg hw hb hLo hHi
    hCuQ warp hTails
  exact Correction.terminalArrivalsAfterFirstExchange hp hMax hg hb hHi down hCuQ hTails free

end PTX.Kernels.TmlFa4Fwd.Progress
