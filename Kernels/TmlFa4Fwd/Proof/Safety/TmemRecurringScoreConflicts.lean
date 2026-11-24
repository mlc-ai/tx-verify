-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemInitialScoreConflicts
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityStoreScoreOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringProbabilityAcquire
import Lemmas.Tcgen05.TcMmaResultLayout
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Proof PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Protocol.Scores (ProbabilityStoreScore probabilityStoreObservesScore)

/-- The remaining probability reuse direction is from a store to a repeated QK
issue later than the store's observed score commit. -/
def ProbabilityStoreReuseOrder (l : Launch) (X : Execution) : Prop :=
  ∀ (stage : Fin 2) {mma store : EvId} {cell : Cell},
    StoreCell l X store cell → TensorStoreFootprint l store cell (.probability stage) →
    MmaAccumulatorOn X mma cell (.probability stage) →
    (seen : ProbabilityStoreScore l X store stage) → seen.commit.2 ≤ mma.2 →
    (∀ packet, ∃ wait, MmaProbabilityAcquire l X mma stage packet wait) →
    StoreDoneBefore l X store mma

/-- The actual acquire discharges all earlier score fragments, leaving only the
later QK issue's reuse of the store's probability packet. -/
theorem TensorMixedWriteOrder.ofProbabilityReuse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hReuse : ProbabilityStoreReuseOrder l X)
    (hRescale : ∀ stage, TensorMmaStoreOrder l X (.rescale stage)) :
    TensorMixedWriteOrder l X := by
  apply TensorMixedWriteOrder.ofRecurringScores hp hX _ hRescale
  intro stage mma store block frag d row col op acc mask cell
    hRepeat hStage hQk hResult hStore hFoot
  let hMma : X.MmaIssue mma d op acc mask := ⟨_,hQk.decoded⟩
  obtain ⟨seen⟩ := probabilityStoreObservesScore hp hX stage hStore hFoot
  by_cases hEarlier : mma.2 < seen.commit.2
  · have hOp := hQk.queryOperand hp hX
    have hCell : cell.cta = mma.1/l.block := by
      rcases resultCell_cta hResult with hLo | hHi
      · exact hLo.trans hOp.ctaLow
      · exact hHi.trans hOp.ctaHigh
    have hCta : SameCta l mma.1 store.1 := by
      obtain ⟨_,_,_,_,⟨_,he⟩,_,_⟩ := hStore
      exact ⟨event_thread_lt hX hQk.decoded,event_thread_lt hX he,hCell.symm.trans hFoot.cta⟩
    exact .inl (seen.doneBeforeEarlierMma hp hX hMma hCta hEarlier)
  · have hGuard (packet : Fin 2) : ∃ wait, MmaProbabilityAcquire l X mma stage packet wait :=
      hStage ▸ hQk.recurringProbabilityAcquire hp hX hRepeat packet
    have hOn : MmaAccumulatorOn X mma cell (.probability stage) :=
      ⟨block,frag,d,op,acc,mask,row,col,hStage,hQk,hResult⟩
    exact .inr (hReuse stage hStore hFoot hOn seen (Nat.le_of_not_lt hEarlier) hGuard)

end PTX.Kernels.TmlFa4Fwd.Safety
