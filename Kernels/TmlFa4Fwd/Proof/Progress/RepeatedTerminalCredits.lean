-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedCorrectionSecondStage
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsCredit
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondTerminalCredit
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Correction Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem repeatedCorrectionFirstTerminalCredit (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) :
    ∃ j e, X.get (g,j) = some e ∧ Thread.correctionAction e = some (.statsCredit 0) ∧
      (Thread.correctionBefore X (g,j)).count (.statsCredit 0) =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨Y,hY,hTrace,_,⟨c⟩⟩ :=
    repeatedFirstTerminalWordsOfRows hp hMax frame hg hRole hb hLo hHi multiple rows
  have hFrameY := frame Y hY.1
  obtain ⟨-,hUsedK⟩ := hFrameY.metadataProtected hp
  have hWork : g/l.block < tilePrefix p p.batch*p.heads := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  have hWait : Thread.CorrectionWaits Y (g,c.waitIndex) .terminal 0 := by
    simpa only [hSelf] using c.waited
  obtain ⟨other,ho,hoLo,hoHi,hOrd⟩ :=
    terminalWaitOrdinalOfTrips hp hY.1 hWork hUsedK hWait
  have hSame : other = batch :=
    (tileBatch_existsUnique p hWork).unique ⟨ho,hoLo,hoHi⟩ ⟨hb,hLo,hHi⟩
  rw [hSame] at hOrd
  obtain ⟨e,he,hAction,hRank⟩ := c.creditObservationOfMaximal hp hY (hSelf.symm ▸ hg)
    (hSelf.symm ▸ hRole) (by simpa only [hSelf] using hOrd)
  have hGet : X.get (g,c.cursor.pos) = some e := by
    simpa only [Execution.get,hSelf,hTrace] using he
  have hCount : (Thread.correctionBefore Y (g,c.cursor.pos)).count (.statsCredit 0) =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    simpa only [hSelf] using hRank
  rw [Thread.correctionBefore_count,hTrace] at hCount
  exact ⟨c.cursor.pos,e,hGet,hAction,(Thread.correctionBefore_count ..).trans hCount⟩

private theorem repeatedCorrectionSecondTerminalCredit (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) {issuer : Nat}
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer) :
    ∃ j e, X.get (g,j) = some e ∧ correctionAction e = some (.statsCredit 1) ∧
      (correctionBefore X (g,j)).count (.statsCredit 1) =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  obtain ⟨staging⟩ := repeatedFirstStageStagingOfRows hp hMax hOutputs hg hw hb hLo hHi
    multiple rows cta issues
  obtain ⟨pub⟩ := staging.publishOfMaximal hp hMax hg
  obtain ⟨wait⟩ := pub.secondWaitOfMaximal hp hMax hg
  obtain ⟨Y,hY,hTrace,_,⟨ready⟩⟩ :=
    repeatedCorrectionSecondTerminalWordsOfMaximal hp hMax hOutputs hg hw hb hLo hHi
      multiple rows cta issues
  obtain ⟨w,hwGet,hwRole⟩ := wait.waited
  have hwY : CorrectionWaits Y (g,wait.first.published.cursor.pos) .terminal 1 := ⟨w,
    by simpa only [Execution.get,hTrace] using hwGet,hwRole⟩
  obtain ⟨j,e,he,hRole,hCount⟩ := ready.terminalCreditOfTrips hp hY (hOutputs Y hY.1)
    hg hw hb hLo hHi hwY
  rw [correctionBefore_count,hTrace] at hCount
  exact ⟨j,e,by simpa only [Execution.get,hTrace] using he,hRole,
    (correctionBefore_count ..).trans hCount⟩

/-- Both correction cohorts return the final generation of statistics credits. -/
theorem repeatedTerminalCreditsOfRows (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch issuer : Nat} (hCta : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch cta).1)
    (rows : TerminalRowPublications l X cta (Mma.trips p batch (assignedCoordinates p batch cta).1))
    (owner : issuer/l.block = cta) (issues : Mma.TerminalOutputIssues l X issuer) (s : Fin 2) :
    Protocol.Statistics.TerminalCorrectionCredits l X cta s
      (Mma.trips p batch (assignedCoordinates p batch cta).1) := by
  intro lane
  let g := statsCreditLane l cta lane
  have hLane : 256+lane.val < l.block := by rw [hp.block]; have := lane.isLt; omega
  have hg : g < l.threads := by
    simpa only [g,statsCreditLane,Nat.add_assoc] using NamedBar.cta_thread_lt hCta hLane
  obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  have hSame : g/l.block = cta := by
    simpa only [g,statsCreditLane,Nat.add_assoc] using hOwner
  have hLocal' : g%l.block = 256+lane.val := by
    simpa only [g,statsCreditLane,Nat.add_assoc] using hLocal
  have hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold warpIndex
    rw [hLocal']
    have := lane.isLt
    omega
  fin_cases s
  · obtain ⟨j,e,he,ha,ord⟩ := repeatedCorrectionFirstTerminalCredit hp hMax hOutputs hg hRole
      hb (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ multiple) (hSame.symm ▸ rows)
    exact ⟨j,e,he,ha,by rwa [hSame] at ord⟩
  · obtain ⟨j,e,he,ha,ord⟩ := repeatedCorrectionSecondTerminalCredit hp hMax hOutputs hg hRole
      hb (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ multiple) (hSame.symm ▸ rows)
      (owner.trans hSame.symm) issues
    exact ⟨j,e,he,ha,by rwa [hSame] at ord⟩

end PTX.Kernels.TmlFa4Fwd.Progress
