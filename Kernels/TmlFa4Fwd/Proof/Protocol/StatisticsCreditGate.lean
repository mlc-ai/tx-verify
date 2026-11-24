-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuseClosure
import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
public import Lemmas.Protocol.UnitHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.Thread.WaitMode
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy Thread Prologue Epilogue
open Correction (statsCreditLoc statsCreditLane terminalStatsProducer terminalStatsCta
  terminalStatsProducerWarp terminalStatsWarp terminalStatsBarrier rowOf)

private def SoftmaxConsumer (l : Launch) (cta : Nat) (stage : Fin 2) (g : Nat) : Prop :=
  g < l.threads ∧ g / l.block = cta ∧ g % l.block / 128 = stage.val

private def CreditPair (l : Launch) (cta : Nat) (stage : Fin 2) (lane : Fin 128) (g : Nat) : Prop :=
  g = terminalStatsProducer l (statsCreditLane l cta lane) stage

private theorem creditLaneCta {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (cta : Nat) (lane : Fin 128) : statsCreditLane l cta lane / l.block = cta := by
  have hLane := lane.isLt
  unfold statsCreditLane
  rw [hp.block]
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem gate (hCuQ : DrainCuQProtected p X) (cta : Nat) (stage : Fin 2) :
    MbarRing.Unit.Gate l kernel Assumptions.all X (statsCreditLoc l cta stage) 128
      (statsCreditLane l cta) 1 (SoftmaxConsumer l cta stage) (CreditPair l cta stage) where
  toObj := Correction.statsCreditObject hp hX cta stage
  cover g hg := by
    let lane : Fin 128 := ⟨g % l.block % 128, Nat.mod_lt _ (by decide)⟩
    refine ⟨lane, ?_⟩
    have hCta := creditLaneCta hp cta lane
    have hRow : rowOf l (statsCreditLane l cta lane) = lane.val := by
      have hLane := lane.isLt
      unfold rowOf statsCreditLane
      rw [hp.block]
      omega
    have hDiv := hg.2.2
    have hOwner := hg.2.1
    unfold CreditPair terminalStatsProducer
    rw [hCta, hRow]
    change g = cta * l.block + 128 * stage.val + g % l.block % 128
    have hG : g = cta * l.block + g % l.block := by
      rw [← hOwner, Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]
    have hTail : g % l.block = 128 * stage.val + g % l.block % 128 := by
      have h := Nat.mod_add_div (g % l.block) 128
      change g % l.block / 128 = stage.val at hDiv
      omega
    exact hG.trans ((congrArg (cta * l.block + ·) hTail).trans (Nat.add_assoc ..).symm)
  partner lane := ⟨_, rfl⟩
  gate {lane h i site} {scope} hPair he _ := by
    let g := statsCreditLane l cta lane
    change h = terminalStatsProducer l g stage at hPair
    subst h
    have hc := Correction.statsCreditArrivalAction hp hX stage he
    let producer := terminalStatsProducer l g stage
    have hSame : producer / l.block = g / l.block := terminalStatsCta hp g stage
    have hPaired : Paired l producer g stage := by
      unfold Paired producer
      rw [terminalStatsProducerWarp hp]
      exact terminalStatsBarrier l g stage
    have hStage : stage.val = warpIndex l producer / 4 := by
      have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
      rw [show warpIndex l producer = (terminalStatsWarp l g stage).val from
        terminalStatsProducerWarp hp g stage]
      change stage.val = (rowOf l g / 32 + 4 * stage.val) / 4
      omega
    let n := (correctionBefore X (g, i)).count (.statsCredit stage)
    have hWork := Correction.statsCreditHasWork hp hX he hc
    have hUsedK := usedKProtected hp hX
    obtain ⟨acquire, hAcquire, hCount, hPath⟩ :=
      creditDependsOnSelectedProducer hp hX he hc hSame hPaired
        (fun _ _ _ _ _ _ hGet hExit =>
          (creditOrdinalBeforeActiveExit hp hX hCuQ hUsedK he hc hSame hPaired hWork hGet hExit).le)
        (n := n) le_rfl
    obtain ⟨_, parity, acq, sc, hWait⟩ := Scores.CreditAcquired.waits hp hX hAcquire
    have hOwner : producer / l.block = cta := hSame.trans (creditLaneCta hp cta lane)
    rw [← hStage, hOwner] at hWait
    have hPoll := Correction.statsCreditPollCursor hp hX (g := producer) (j := acquire)
      stage hStage
    rw [hOwner, hCount] at hPoll
    have hCredit := Correction.statsCreditArrivalCursor hp hX stage he
    rw [creditLaneCta hp cta lane] at hCredit
    exact ⟨acquire, _, parity, acq, sc, hWait, by rw [hPoll, hCredit], hPath⟩
  acq _ he := actualPollAcquires hX he
  cta lane h hh := by
    have hCta := creditLaneCta hp cta lane
    have hGrid : cta < l.grid := hh.2.1 ▸ NamedBar.cta_lt hh.1
    have hThread : statsCreditLane l cta lane < l.threads := by
      have hLane := lane.isLt
      have hBound := Nat.mul_le_mul_right l.block (Nat.succ_le_of_lt hGrid)
      unfold Launch.threads statsCreditLane
      rw [hp.block, Nat.succ_mul] at hBound
      rw [hp.block]
      omega
    exact ⟨hThread, hh.1, hCta.trans hh.2.1.symm⟩

/-- A successful softmax statistics acquire observes every correction credit in its
completed generation. -/
theorem creditHandoff (hCuQ : DrainCuQProtected p X) (input : EvId) (stage : Fin 2)
    (hAcquire : Scores.CreditAcquired X input) (hStage : stage.val = warpIndex l input.1 / 4)
    (q : Nat) (hOrdinal : (Scores.before X input).credits = q + 1) (lane : Fin 128) :
    let cta := input.1 / l.block
    let loc := statsCreditLoc l cta stage
    ∃ index, let credit := (statsCreditLane l cta lane, index)
      (correctionBefore X credit).count (.statsCredit stage) = q ∧
        MbarRing.Syncs l X credit input loc := by
  obtain ⟨g,j⟩ := input
  obtain ⟨_, parity, acq, scope, hWait⟩ := Scores.CreditAcquired.waits hp hX hAcquire
  rw [← hStage] at hWait
  have hConsumer : SoftmaxConsumer l (g / l.block) stage g := by
    refine ⟨event_thread_lt hX hWait, rfl, ?_⟩
    change stage.val = (g % l.block / 32) / 4 at hStage
    omega
  have hCursor := Correction.statsCreditPollCursor hp hX (g := g) (j := j) stage hStage
  rw [hOrdinal] at hCursor
  have hGate := gate hp hX hCuQ (g / l.block) stage
  obtain ⟨index, hUse, hSync⟩ := hGate.handoff hX g j _ parity acq scope q hConsumer
    hWait hCursor (statsCreditLane l (g / l.block) lane) ⟨lane, rfl⟩
  obtain ⟨_, hGet, _⟩ := hSync.arrives
  have hC := Correction.statsCreditArrivalCursor hp hX stage hGet
  rw [creditLaneCta hp] at hC
  exact ⟨index, hC.symm.trans hUse, hSync⟩

/-- A completed credit generation needs a successful acquire by the consumer paired
with a lane of that generation. The final physical phase cannot overtake its polls. -/
theorem creditFinalPhaseLeSuccessfulPolls (hCuQ : DrainCuQProtected p X) {g : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hStage : warpIndex l g/4 = stage.val) {s : MBarrier.State}
    (hFinal : MBarrier.stateBefore (X.objects (statsCreditLoc l (g/l.block) stage))
      (X.objects (statsCreditLoc l (g/l.block) stage)).length = some s) :
    s.phase ≤ Flow.okPolls (statsCreditLoc l (g/l.block) stage) (X.tr g) := by
  let addr := statsCreditLoc l (g/l.block) stage
  let G := gate hp hX hCuQ (g/l.block) stage
  let n := Flow.okPolls addr (X.tr g)
  have hConsumer : SoftmaxConsumer l (g/l.block) stage g := by
    refine ⟨hg,rfl,?_⟩
    change ((g % l.block)/32)/4 = stage.val at hStage
    omega
  obtain ⟨lane,hPair⟩ := G.cover g hConsumer
  show s.phase ≤ n
  by_contra! hAdvance
  obtain ⟨i,r,j,_,hRec,_,hArrive,hId,_,hOrdinal⟩ := G.phase_all hX
    (j := (X.objects addr).length) (q := n) le_rfl hFinal hAdvance (by
      intro k _ r lane j cnt tx hGet hClean hArrive hId hPhase
      have hOrdinal := G.phase_eq hX k r lane j cnt tx hGet hClean hArrive hId
      rw [hPhase] at hOrdinal
      exact (Option.some.inj hOrdinal).symm) lane
  obtain ⟨_,_,hCredit⟩ := G.arrive_of_id hRec hArrive hId
  obtain ⟨pos,_,_,_,_,hPoll,hCount,_⟩ := G.gate hPair hCredit (by omega)
  have hGt : Flow.okPolls addr ((X.tr g).take (pos+1)) =
      Flow.okPolls addr ((X.tr g).take pos)+1 := MbarRing.Poll.okPoll_get hPoll
  have hEq : Flow.okPolls addr ((X.tr g).take pos)+1 = n+1 :=
    hCount.trans (congrArg (·+1) hOrdinal)
  have hLe := MbarRing.Poll.okPolls_mono addr (X.tr g)
    (show pos+1 ≤ (X.tr g).length from len_of_get hPoll)
  rw [List.take_length] at hLe
  change Flow.okPolls addr ((X.tr g).take (pos+1)) ≤ n at hLe
  rw [hGt,hEq] at hLe
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
