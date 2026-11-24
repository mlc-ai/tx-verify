-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LseTerminalPeer
import all Kernels.TmlFa4Fwd.Proof.Protocol.LseTerminalPeer

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow Thread Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

/-- A known final publication in the returned correction wait's generation
identifies the paired producer without requiring that producer to have exited. -/
theorem terminalPeerOfFinalPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait pos : Nat} {stage : Fin 2} (hWait : CorrectionWaits X (g,wait) .terminal stage)
    (hPass : wait+1 < (X.tr g).length)
    (hFinal : Scores.Publishes X (terminalStatsProducer l g stage,pos) .final)
    (hOrd : observedBarrierOrdinal X (terminalStatsProducer l g stage,pos)
      (statsBarrierId l g stage) = observedBarrierOrdinal X (g,wait) (statsBarrierId l g stage)) :
    TerminalPeer l X g stage wait pos .final := by
  let producer := terminalStatsProducer l g stage
  have hId : 3+warpIndex l producer = statsBarrierId l g stage :=
    (congrArg (3+·) (terminalStatsProducerWarp hp g stage)).trans (terminalStatsBarrier l g stage)
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := Scores.publishes hp hX hFinal
  rw [hId] at hKind
  obtain ⟨round,hPeer⟩ := terminalPeerOfArrival hp hX (terminalWaitArrival hp hX hWait)
    hPass (mode := .arrive) ⟨e,he,hKind⟩ hOrd
  obtain ⟨f,hf,hNotice⟩ := hPeer.publication
  obtain ⟨f',hf',hFinalNotice⟩ := hFinal
  rw [Option.some.inj (hf.symm.trans hf'),hFinalNotice] at hNotice
  exact (Option.some.inj hNotice).symm ▸ hPeer

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
