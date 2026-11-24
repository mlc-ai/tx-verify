-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstNormalizedChunk
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionNormalizedChunkProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingGeometry
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeSurface

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The full first eight-column chunk is staged, and the real lane is ready
for the local address update of the second chunk. -/
structure FirstStagedChunk (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  source : FirstNormalizedChunk p l X g batch lane
  cursor : OpeningTripCursor l X (warpLane l g lane) (finalizeSurfacePc 0 1)
    (finalizeVectorFact l (warpLane l g lane) 0 1 ::
      firstChunkFrame p l g batch lane source.source.acquired.sum source.source.acquired.maximum)
  written : ∀ half : Fin 2, ∀ k : Fin 4, Thread.Correction.StagingWrite X
    (.thread (warpLane l g lane,source.source.loadCursor.pos+2+4*half.val+k.val))
    { loc := (outputChunkLoc l (warpLane l g lane) 0 0 (rowOf l (warpLane l g lane))
        (finalizeVector 0 half).val).at (4*k.val)
      size := 4
      elem := k.val }
    (let sum := source.source.acquired.sum
     (fl (source.values (4*half.val+k.val) * (1 / (if sum = 0 then 1 else sum)))).toBytes)
  position : cursor.pos = source.source.loadCursor.pos+10

theorem FirstNormalizedChunk.stageChunkOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (hw : warpIndex l (warpLane l g lane) < 12) (c : FirstNormalizedChunk p l X g batch lane)
    (hRelease : c.source.loadCursor.pos+2 = (X.tr (warpLane l g lane)).length →
      Step.Released l X (warpLane l g lane)) :
    Nonempty (FirstStagedChunk p l X g batch lane) := by
  let thread := warpLane l g lane
  let sum := c.source.acquired.sum
  let reciprocal : ℝ := 1 / (if sum = 0 then 1 else sum)
  let F := firstChunkFrame p l g batch lane sum c.source.acquired.maximum
  let P := finalizeProductFacts 0 0 c.values reciprocal
  let facts := normalizeStoreFacts l thread 0 0
  have hOld := (holds_append _ _ _).1 c.checkpoint.2.2.2.2
  have hVec : finalizeVectorFact l thread 0 0 ∈ F := by
    simp [F,thread,firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts]
  have hDelta : (6500,b32 (finalizeVectorDelta l thread)) ∈ F := by
    simp [F,thread,firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts,finalizeDeltas]
  have hFacts : Holds c.ready.regs facts :=
    ⟨holds_mem hOld.2 hVec,holds_mem hOld.2 hDelta,trivial⟩
  have hAt : At c.ready (finalizeLoadPc 0 0+10) (P++(facts++F)) := c.checkpoint.mono
    ((holds_append _ _ _).2 ⟨hOld.1,(holds_append _ _ _).2 ⟨hFacts,hOld.2⟩⟩)
  let cur : OpeningTripCursor l X thread (finalizeLoadPc 0 0+10) (P++(facts++F)) :=
    ⟨c.source.loadCursor.pos+2,c.before,c.ready,c.source.loadCursor.ending,by omega,
      len_of_get c.wait,
      hRelease,hAt,c.returned,c.remaining,c.localSteps⟩
  have hKeep : ∀ r ∈ F.map Prod.fst,
      (∀ half, ∀ q ∈ finalizeUnpacks 0 0 half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      ((0 : Fin 16).val < 4 → r ≠ outputStoreAddrReg 0 (finalizeVector 0 1)) :=
    of_decide_eq_true rfl
  obtain ⟨hWrites,d,hPos,_⟩ :=
    normalizedChunkWritesOfMaximal hp hMax hg hw 0 0 c.values reciprocal cur hKeep
  exact ⟨⟨c,d,fun half k => Thread.Correction.StagingWrite.of_event 0
    (finalizeSubset 0) (finalizeVector 0 half) (hWrites half k),by rw [hPos]⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
