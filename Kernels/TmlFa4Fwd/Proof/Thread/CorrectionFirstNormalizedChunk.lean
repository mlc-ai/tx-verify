-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionChunkComputeProgress
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTensorSchedule

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue Epilogue

/-- The unchanged accumulator-load frame includes the packed reciprocal
and the decoded vector geometry for the staging stores. -/
noncomputable def firstChunkFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (sum : ℝ) (maximum : Option ℝ) : List (Nat × Value) :=
  let recip := fl (1 / (if sum = 0 then 1 else sum))
  (finalizeReciprocalPair 0,.pair recip recip) ::
    (finalPollPrepReg 0,finalPollPrepWord l 0) ::
    firstTerminalReciprocalFrame p l g batch lane sum maximum

/-- A recorded first chunk computed its four normalized pairs after the explicit wait. -/
structure FirstNormalizedChunk (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  source : FirstOutputLoadIssued p l X g batch lane
  values : Nat → ℝ
  before : TState
  ready : TState
  checkpoint : At ready (finalizeLoadPc 0 0+10)
    (finalizeProductFacts 0 0 values
      (1 / (if source.acquired.sum = 0 then 1 else source.acquired.sum))
      ++ firstChunkFrame p l g batch lane source.acquired.sum source.acquired.maximum)
  wait : X.get (warpLane l g lane,source.loadCursor.pos+1) =
    some ⟨finalizeLoadPc 0 0+5,.tc .waitLd⟩
  returned : Run kernel Assumptions.all l (warpLane l g lane) {}
    ((X.tr (warpLane l g lane)).take (source.loadCursor.pos+2)) (some before)
  remaining : Run kernel Assumptions.all l (warpLane l g lane) before
    ((X.tr (warpLane l g lane)).drop (source.loadCursor.pos+2)) source.loadCursor.ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) before ready

/-- The released first load returns the actual accumulator values. The lane
issues its explicit wait and combines the observed words with its reciprocal.
The new cursor keeps the same actual suffix ending. -/
theorem FirstOutputLoadIssued.normalizeOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hValues : ∀ i, CompletedValues l Assumptions.all X i) {g batch lane : Nat}
    (hg : warpLane l g lane < l.threads) (c : FirstOutputLoadIssued p l X g batch lane)
    (hRelease : c.loadCursor.pos+1 = (X.tr (warpLane l g lane)).length →
      Step.Released l X (warpLane l g lane)) :
    Nonempty (FirstNormalizedChunk p l X g batch lane) := by
  let F := firstChunkFrame p l g batch lane c.acquired.sum c.acquired.maximum
  let r := 1 / (if c.acquired.sum = 0 then 1 else c.acquired.sum)
  have hRecip : (finalizeReciprocalPair 0,.pair (fl r) (fl r)) ∈ F := .head _
  have hFresh : ∀ a ∈ F.map Prod.fst,
      a ∉ finalizeDataRegs 0 0 ∧
      (∀ q ∈ finalizePacks 0 0, q.1 ≠ a) ∧
      (∀ q ∈ finalizeMuls 0 0, q.1 ≠ a) := of_decide_eq_true rfl
  obtain ⟨d⟩ := chunkProductsOfMaximal hp hMax hCuQ hValues hg 0 0 c.loadCursor c.wordCount
    c.decoded c.issued c.returned c.continuation hRelease r hRecip hFresh
  exact ⟨⟨c,d.values,d.before,d.ready,d.checkpoint,d.wait,d.returned,d.remaining,d.localSteps⟩⟩

theorem FirstNormalizedChunk.waitOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch lane : Nat}
    (hRole : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ warpLane l g lane/l.block)
    (hHi : warpLane l g lane/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (warpLane l g lane/l.block)).1 = 1)
    (c : FirstNormalizedChunk p l X g batch lane) :
    X.TcK (warpLane l g lane,c.source.loadCursor.pos+1) 1 :=
  Thread.correctionFirstOutputWaitOrdinal hp hX hFrame hRole.1 hRole.2 hb hLo hHi hSingle c.wait

/-- Matching explicit waits release the warp's first normalized chunk for staging. -/
theorem FirstNormalizedChunk.waitReleased {p : Params} {l : Launch} {X : Execution}
    {g batch lane : Nat} (c : FirstNormalizedChunk p l X g batch lane)
    (hRank : X.TcK (warpLane l g lane,c.source.loadCursor.pos+1) 1)
    (hPeers : ∀ peer ∈ warpLanes l (warpLane l g lane), ∃ k, X.TcK (peer,k) 1) :
    c.source.loadCursor.pos+2 = (X.tr (warpLane l g lane)).length →
      Step.Released l X (warpLane l g lane) := by
  simpa only [Nat.add_assoc] using Step.releasedOfTcOrdinal c.wait rfl hRank.2 hPeers

end PTX.Kernels.TmlFa4Fwd.Correction
