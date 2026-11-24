-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondStageStaging
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The actual lane has prepared its packed LSE address from the selected request. -/
structure LseHeadReached (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  source : SecondOutputPublished p l X g batch
  cursor : OpeningTripCursor l X g (lsePc 0)
    ((9525,b64 (p.lseLoc (p.qOffset batch) (assignedCoordinates p batch (g/l.block)).2).addr) ::
      source.staging.words.chunkFrame)

theorem SecondOutputPublished.lseHead {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (c : SecondOutputPublished p l X g batch) :
    Nonempty (LseHeadReached p l X g batch) := by
  let F := c.staging.words.chunkFrame
  let pos := assignedCoordinates p batch (g/l.block)
  let a := c.published.cursor
  have hAt : At a.ready 9057 F :=
    a.checkpoint.mono ((holds_append _ _ _).1 a.checkpoint.2.2.2.2).2
  have hOffset : (1634,b32 (p.qOffset batch)) ∈ F := by
    simp [F,SecondTerminalWordsReady.chunkFrame,SecondTerminalWordsReady.pollFrame,
      SecondTerminalWordsReady.reciprocalFrame,SecondTerminalWordsReady.wordsFrame,
      firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale]
  have hHead : (9605,b64 pos.2) ∈ F := by
    simp [F,pos,SecondTerminalWordsReady.chunkFrame,SecondTerminalWordsReady.pollFrame,
      SecondTerminalWordsReady.reciprocalFrame,SecondTerminalWordsReady.wordsFrame,
      firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale,
      tileSetupFrame,correctionActiveTileFacts]
  have hStride : (7501,b64 p.lseStride) ∈ F := by
    simp [F,SecondTerminalWordsReady.chunkFrame,SecondTerminalWordsReady.pollFrame,
      SecondTerminalWordsReady.reciprocalFrame,SecondTerminalWordsReady.wordsFrame,
      firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale,tileSetupFrame,
      correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,
      nonzeroBarrierFacts,abiFacts]
  have hBase : (7500,b64 p.lseBase) ∈ F := by
    simp [F,SecondTerminalWordsReady.chunkFrame,SecondTerminalWordsReady.pollFrame,
      SecondTerminalWordsReady.reciprocalFrame,SecondTerminalWordsReady.wordsFrame,
      firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale,tileSetupFrame,
      correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,
      nonzeroBarrierFacts,abiFacts]
  have hShape := assignedCoordinates_valid hp hLo hHi
  obtain ⟨u,hU,hLocal⟩ := correctionLseBaseRun hp (g := g) hb hShape.2
    (by omega) hAt hOffset hHead hStride hBase
    (by set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨⟨c,⟨a.pos,a.before,u,a.ending,a.positive,a.bounded,a.released,hU,
    a.recorded,a.remaining,a.localSteps.trans (run_rtg hLocal)⟩⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
