-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsTripExtent
import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow Thread Correction Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
include hp hX hCuQ

/-- The actual paired producer, if exited, has published every required statistics generation. -/
theorem exitedCreditExtent (hUsedK : UsedKProtected p X) : ExitedCreditExtent l X := by
  intro stage credit e he hAction
  let producer := terminalStatsProducer l credit.1 stage
  have hSame : producer / l.block = credit.1 / l.block := terminalStatsCta hp credit.1 stage
  have hPair : Paired l producer credit.1 stage := by
    unfold Paired
    rw [terminalStatsProducerWarp hp]
    exact terminalStatsBarrier l credit.1 stage
  refine ⟨producer, hSame, hPair, ?_⟩
  rintro ⟨pos, stop, hGet, hExit⟩
  have hWork := statsCreditHasWork hp hX he hAction
  have hEarlier := creditOrdinalBeforeActiveExit hp hX hCuQ hUsedK he hAction
    hSame hPair hWork hGet hExit
  have hPos : pos ≤ (X.tr producer).length := (List.getElem?_eq_some_iff.mp hGet).1.le
  have hLater : (Scores.before X (producer,pos)).notices ≤
      (Scores.before X (producer,(X.tr producer).length)).notices := by
    rw [Scores.beforeNotices, Scores.beforeNotices]
    exact countP_take_mono _ _ hPos
  exact hEarlier.trans_le hLater

/-- Correction credits have actual statistics publications in their observed generation. -/
theorem creditPeers (hUsedK : UsedKProtected p X) : CreditPeers l X :=
  creditPeersOfExitedExtent hp hX (exitedCreditExtent hp hX hCuQ hUsedK)

/-- The required generation precedes any counted exit of the selected producer. -/
theorem countedExitCreditBound (hUsedK : UsedKProtected p X) :
    CountedExitCreditBound l X := by
  intro stage credit e he hAction
  obtain ⟨producer, hSame, hPair, _⟩ := exitedCreditExtent hp hX hCuQ hUsedK stage credit e
    he hAction
  refine ⟨producer, hSame, hPair, ?_⟩
  intro j k stop _ _ _ hGet hExit
  have hWork := statsCreditHasWork hp hX he hAction
  exact (creditOrdinalBeforeActiveExit hp hX hCuQ hUsedK he hAction
    hSame hPair hWork hGet hExit).le

/-- The observed producer and correction histories enforce statistics release before reuse. -/
theorem actualStatsArrivalReleaseBeforeReuse (hUsedK : UsedKProtected p X) {g i j key : Nat}
    {count nextCount : Option Nat} {mode : BarMode} (hRange : 3 ≤ key % 16 ∧ key % 16 < 11)
    (hKey : CtaBarArrivalK l X (g,i) key) (hInit : BarrierArrival X (g,i) (key % 16) count .arrive)
    (hNext : BarrierArrival X (g,j) (key % 16) nextCount mode) (hLt : i < j) :
    CtaBarDone l X (g / l.block) key :=
  releasesStatsArrivalBeforeReuse hp hX (creditPeers hp hX hCuQ hUsedK)
    hRange hKey hInit hNext hLt

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
