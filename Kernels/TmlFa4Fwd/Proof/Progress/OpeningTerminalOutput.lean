-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTailPv
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainStart
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof PTX.MBarrier Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
include hp hMax hFrame hg hw hb hLo hHi hSingle

set_option maxRecDepth 4096 in
/-- On a single-visit CTA, the MMA warp consumes both probability stages, completes
both PV packets, and issues both terminal output commits in any maximal execution. -/
theorem singleVisitTerminalPvAndOutputIssuesOfMaximal :
    Mma.PvPacketIssues l X g 3 1 false ∧ Mma.TerminalOutputIssues l X g := by
  obtain ⟨_,_,_,⟨c⟩⟩ :=
    singleVisitFirstTailPvLeaderOfMaximal hp hMax hFrame hg hw hb hLo hHi hSingle
  have hc := NamedBar.cta_lt hg
  have ht₀ := singleVisitOpeningTailProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 0
  have hm₁ := singleVisitOpeningMainProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 1
  have ht₁ := singleVisitOpeningTailProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 1
  obtain ⟨_,⟨last⟩,hPv⟩ := Mma.terminalPvPacketsOfMaximal hp hMax hg hw c ht₀ hm₁ ht₁
  exact ⟨hPv,Mma.terminalOutputIssuesOfCursor hp hMax hg last⟩

set_option maxRecDepth 4096 in
/-- A single-visit MMA warp reaches its protected first drain words. -/
theorem singleVisitMmaDrainWordsOfMaximal :
    Nonempty (Mma.ActiveDrainWords p l X g) := by
  obtain ⟨_,_,_,⟨c⟩⟩ :=
    singleVisitFirstTailPvLeaderOfMaximal hp hMax hFrame hg hw hb hLo hHi hSingle
  have hc := NamedBar.cta_lt hg
  have ht₀ := singleVisitOpeningTailProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 0
  have hm₁ := singleVisitOpeningMainProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 1
  have ht₁ := singleVisitOpeningTailProbabilityPhaseOfMaximal hp hMax hFrame hc hb hLo hHi hSingle 1
  obtain ⟨_,⟨last⟩,_⟩ := Mma.terminalPvPacketsOfMaximal hp hMax hg hw c ht₀ hm₁ ht₁
  exact Mma.terminalOutputDrainWordsOfMaximal hp hMax (hFrame.metadataProtected hp).1 hg hw last

/-- The single-visit MMA warp consumes its first drain shuffle in the recorded trace. -/
theorem singleVisitMmaDrainNeighborsOfMaximal :
    Nonempty (Mma.ActiveDrainNeighbors p l X g) := by
  obtain ⟨words⟩ := singleVisitMmaDrainWordsOfMaximal hp hMax hFrame hg hw hb hLo hHi hSingle
  exact words.shuffleOfMaximal hp hMax hg

end PTX.Kernels.TmlFa4Fwd.Progress
