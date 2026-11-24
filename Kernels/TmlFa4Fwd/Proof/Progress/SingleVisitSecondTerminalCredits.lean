-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionOutputPublish
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondTerminalCredit
import all Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionOutputPublish

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Correction Thread

private theorem singleVisitCorrectionSecondTerminalCredit {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∃ j e, X.get (g,j) = some e ∧ correctionAction e = some (.statsCredit 1) ∧
      (correctionBefore X (g,j)).count (.statsCredit 1) = 1 := by
  obtain ⟨wait⟩ := singleVisitSecondWaitOfMaximal hp hMax hOutputs hg hw hb hLo hHi hSingle
  obtain ⟨Y,hY,hTrace,_,⟨ready⟩⟩ :=
    singleVisitCorrectionSecondTerminalWordsOfMaximal hp hMax hOutputs hg hw hb hLo hHi hSingle
  obtain ⟨w,hwGet,hwRole⟩ := wait.waited
  have hwY : CorrectionWaits Y (g,wait.first.published.cursor.pos) .terminal 1 := ⟨w,
    by simpa only [Execution.get,hTrace] using hwGet,hwRole⟩
  obtain ⟨j,e,he,hRole,hCount⟩ := ready.singleVisitCreditOfMaximal hp hY (hOutputs Y hY.1)
    hg hw hb hLo hHi hSingle hwY
  rw [correctionBefore_count,hTrace] at hCount
  exact ⟨j,e,by simpa only [Execution.get,hTrace] using he,hRole,
    (correctionBefore_count ..).trans hCount⟩

/-- Every lane of the second correction cohort returns its actual single-visit
terminal credit at generation one. -/
theorem singleVisitSecondTerminalCreditsOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hCta : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) :
    Protocol.Statistics.TerminalCorrectionCredits l X cta 1 1 := by
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
  exact singleVisitCorrectionSecondTerminalCredit hp hMax hOutputs hg hRole hb
    (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ hSingle)

end PTX.Kernels.TmlFa4Fwd.Progress
