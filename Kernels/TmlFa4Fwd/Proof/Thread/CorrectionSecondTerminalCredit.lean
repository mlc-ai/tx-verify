-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondFinalizationAcquire
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalCreditProgress
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

private theorem secondTerminalCreditEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (c : SecondTerminalWordsReady p l X g batch) :
    X.get (g,c.cursor.pos) =
      some ⟨8764,.arrive (statsCreditLoc l (g/l.block) 1) 0 1 true .cta⟩ := by
  let F := c.wordsFrame
  have hBase : (rescaleReuseReg (1-1),b32 (rescaleReuseLoc l g (1-1)).addr) ∈ F := by
    simp [F,SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      rescaleReuseReg,rescaleReuseLoc,correctionBeforeRescale,tileSetupFrame,
      correctionTileGeometryFacts,correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,
      creditFacts,entryFacts,nonzeroBarrierFacts]
  have hCount : (6498,b32 1) ∈ F := by
    simp [F,SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      finalizeLayoutFacts]
  have hFresh : ∀ pair ∈ F, pair.1 ≠ finalStatsReleaseDst 1 := by
    intro pair hm hEq
    exact (of_decide_eq_true rfl : finalStatsReleaseDst 1 ∉ F.map Prod.fst)
      (hEq ▸ List.mem_map_of_mem hm)
  exact (terminalCreditOfMaximal hp hMax hg 1 c.cursor hBase hCount hFresh).1

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch wait : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg hw hb hLo hHi

/-- The actual second terminal statistics credit returns one unit at the terminal
generation of the selected tile, after the matching terminal wait and both reads. -/
theorem SecondTerminalWordsReady.terminalCreditOfTrips
    (hWait : CorrectionWaits X (g,wait) .terminal 1) (c : SecondTerminalWordsReady p l X g batch) :
    ∃ j e, X.get (g,j) = some e ∧ correctionAction e = some (.statsCredit 1) ∧
      (correctionBefore X (g,j)).count (.statsCredit 1) =
        (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) := by
  let n := (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
  let j := c.cursor.pos
  let e : Event := ⟨8764,.arrive (statsCreditLoc l (g/l.block) 1) 0 1 true .cta⟩
  have he : X.get (g,j) = some e := secondTerminalCreditEvent hp hMax hg c
  have hAction : correctionAction e = some (.statsCredit 1) := by
    apply (correctionStatsCreditObservation 1 (show e.kind = _ from rfl)).mpr
    change (8764 : Nat) ∈ [8224,8464,8764]
    decide
  have hCuQ := (hFrame.metadataProtected hp).1
  have hUsedK := (hFrame.metadataProtected hp).2
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  obtain ⟨other,ho,hoLo,hoHi,hOrd⟩ :=
    terminalWaitOrdinalOfTrips hp hMax.1 hWork hUsedK hWait
  have hSame : other = batch :=
    (tileBatch_existsUnique p hWork).unique ⟨ho,hoLo,hoHi⟩ ⟨hb,hLo,hHi⟩
  rw [hSame] at hOrd
  obtain ⟨w,hwGet,hwAction⟩ := hWait
  have hwPc := correctionTerminalWaitSite hwAction
  have hMark : correctionStatsWaitMark 1 w = true := by
    apply (correctionStatsWaitMark_iff 1 w).mpr
    rw [hwPc]
    decide
  have hBefore : wait < j := by
    apply traceOrderOfSegmentFloor hMax.1 (floor := 8764)
      (by set_option maxRecDepth 100000 in decide +kernel)
      (by
        have hSites : Assumptions.swExp2Sites.all (fun site => decide (site < 8764)) = true := by
          decide
        intro site hlo hm _ _
        have hSmall := of_decide_eq_true (List.all_eq_true.mp hSites site hm)
        omega)
      hwGet he
    · rw [hwPc]
      decide
    · rfl
  have hCountAtWait : ((X.tr g).take wait).countP (correctionStatsWaitMark 1) = n := by
    rw [correctionBarrierOrdinal,← correctionWaitPrefixCount hp hMax.1 1
      (len_of_get hwGet) hw] at hOrd
    exact hOrd
  have hTwo : ((X.tr g).take (wait+1)).countP (correctionStatsWaitMark 1) = n+1 := by
    rw [countP_take_succ hwGet hMark,hCountAtWait]
  have hLower : n+1 ≤ ((X.tr g).take j).countP (correctionStatsWaitMark 1) := by
    have hMono := countP_take_mono (correctionStatsWaitMark 1) (X.tr g)
      (show wait+1 ≤ j by omega)
    rwa [hTwo] at hMono
  have hMarked : correctionStatsCreditMark 1 e = true :=
    (correctionStatsCreditMark_iff 1 e).mpr
      ((correctionStatsCreditObservation 1 (show e.kind = _ from rfl)).mp hAction)
  have hBal : ((X.tr g).take j).countP (correctionStatsWaitMark 1) =
      ((X.tr g).take j).countP (correctionStatsCreditMark 1)+1 :=
    correctionCreditRequiresWait hMax.1 1 he hMarked
  obtain ⟨b,hb',hLo',hHi',hUpper⟩ :=
    correctionCreditsWithinTrips hp hMax.1 hWork hUsedK 1 he hAction
  have hb'Eq : b = batch :=
    (tileBatch_existsUnique p hWork).unique ⟨hb',hLo',hHi'⟩ ⟨hb,hLo,hHi⟩
  rw [hb'Eq,correctionCreditCursor hp hMax.1 1 he] at hUpper
  refine ⟨j,e,he,hAction,?_⟩
  rw [correctionCreditCursor hp hMax.1 1 he]
  change ((X.tr g).take j).countP (correctionStatsCreditMark 1) = n
  change ((X.tr g).take j).countP (correctionStatsCreditMark 1) ≤ n at hUpper
  omega

/-- The actual second terminal statistics credit returns one unit in the single
visit's terminal generation, after the matching terminal wait and both reads. -/
theorem SecondTerminalWordsReady.singleVisitCreditOfMaximal
    (hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hWait : CorrectionWaits X (g,wait) .terminal 1) (c : SecondTerminalWordsReady p l X g batch) :
    ∃ j e, X.get (g,j) = some e ∧ correctionAction e = some (.statsCredit 1) ∧
      (correctionBefore X (g,j)).count (.statsCredit 1) = 1 := by
  simpa only [hOne] using c.terminalCreditOfTrips hp hMax hFrame hg hw hb hLo hHi hWait

end PTX.Kernels.TmlFa4Fwd.Correction
