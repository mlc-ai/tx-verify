-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedCorrectionSecondStage
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseTailProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityHistory
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleStoreValues
import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) {issuer : Nat}
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer)
include hp hMax hOutputs hg hRole hb hLo hHi multiple rows cta issues

/-- Every repeated-visit correction lane stages and publishes both actual
output surfaces and retains the normalized row data. -/
theorem repeatedCorrectionSecondOutputPublishedOfMaximal :
    Nonempty (SecondOutputPublished p l X g batch) := by
  have hFrame := hOutputs X hMax.1
  have hCuQ := (hFrame.metadataProtected hp).1
  have hOperands := Safety.mmaOperandsOfProbabilities hp hMax.1 hFrame
    (Protocol.Scores.completedPvProbabilitiesOfExecution hp hMax.1 hOutputs)
  have hRescale := Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hMax.1 hOutputs
  have hValues := Safety.mmaCompletedValuesOfOperandsAndRescaleStores hp hMax.1 hCuQ
    hOperands hRescale
  have hStart : ∀ lane, SameWarp l g lane → ∃ Y, Y.tr = X.tr ∧
      Nonempty (SecondOutputLoadReady p l Y lane batch) := by
    intro lane hw
    have hCta := hw.1.2.2
    have hWarp : warpIndex l g = warpIndex l lane := hw.2
    obtain ⟨Y,_,ht,_,hFirst⟩ :=
      repeatedCorrectionSecondOutputLoadReadyOfMaximal hp hMax hOutputs hw.1.2.1 (hWarp ▸ hRole)
        hb (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ multiple)
        (hCta ▸ rows) (cta.trans hCta) issues
    exact ⟨Y,ht,hFirst⟩
  obtain ⟨c⟩ := secondStageStagingAfterRescale hp hMax hFrame hValues hRole
    hStart g ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact c.publishOfMaximal hp hMax hg

/-- Both published surfaces lead into the real LSE computation for the selected request. -/
theorem repeatedCorrectionLseHeadOfMaximal :
    Nonempty (LseHeadReached p l X g batch) := by
  obtain ⟨c⟩ := repeatedCorrectionSecondOutputPublishedOfMaximal hp hMax hOutputs
    hg hRole hb hLo hHi multiple rows cta issues
  exact c.lseHead hp hb hLo hHi

/-- The actual correction lane finishes both row-guarded LSE paths after its
outputs are published, including rows of zero mass. -/
theorem repeatedCorrectionLseTailOfMaximal :
    Nonempty (LseTailReached p l X g batch) := by
  obtain ⟨c⟩ := repeatedCorrectionLseHeadOfMaximal hp hMax hOutputs
    hg hRole hb hLo hHi multiple rows cta issues
  exact c.tailOfMaximal hp hMax hg hRole.2 hb hLo hHi

end PTX.Kernels.TmlFa4Fwd.Progress
