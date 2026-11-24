-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
public import Lemmas.Protocol.NamedBarArrive
public import Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow Thread Prologue

/-- The producer warp meets the correction warp on the named barrier of this stage. -/
def Paired (l : Launch) (producer consumer : Nat) (stage : Fin 2) : Prop :=
  3 + warpIndex l producer = Correction.statsBarrierId l consumer stage

private theorem producerWarp {l : Launch} {g h : Nat} {stage : Fin 2} (hs : Paired l g h stage) :
    warpIndex l g < 8 := by
  have hw := Nat.mod_lt (warpIndex l h) (by decide : 0 < 4)
  have hd := stage.isLt
  unfold Paired Correction.statsBarrierId at hs
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Both sides of the initial statistics exchange join generation zero. -/
theorem firstOrdinals {producer consumer : EvId} {stage : Fin 2}
    (hPair : Paired l producer.1 consumer.1 stage) (hPub : Scores.Publishes X producer .first)
    (hWait : CorrectionWaits X consumer .initial stage) :
    (Scores.before X producer).barrier (3 + warpIndex l producer.1) = 0 ∧
      (correctionBefore X consumer).barrier (3 + warpIndex l producer.1) = 0 := by
  let w : Fin 8 := ⟨warpIndex l producer.1, producerWarp hPair⟩
  have hSources := statsBarrierSources hp hX w
  refine ⟨Scores.firstOrdinal hp hX hPub hSources, ?_⟩
  unfold Paired at hPair
  rw [hPair]
  exact correctionInitialWaitOrdinal hp hX hWait (hPair ▸ hSources)

/-- Statistics published before a producer's notification reach the correction lane after
it returns from its rendezvous in the same generation. -/
theorem handoff {g h i j before after : Nat} {stage : Fin 2} {producerRound : Scores.Round}
    {consumerRound : CorrectionRound} (hSame : SameCta l g h) (hPair : Paired l g h stage)
    (hPub : Scores.Publishes X (g, i) producerRound)
    (hWait : CorrectionWaits X (h, j) consumerRound stage)
    (hOrdinal : (Scores.before X (g, i)).barrier (3 + warpIndex l g) =
      (correctionBefore X (h, j)).barrier (3 + warpIndex l g)) (hBefore : before < i)
    (hAfter : j < after) (hLen : after < (X.tr h).length) :
    baseCausality l X (g, before) (h, after) := by
  let w : Fin 8 := ⟨warpIndex l g, producerWarp hPair⟩
  have hSources := statsBarrierSources hp hX w
  have hShape := statsBarrierShape hp w
  obtain ⟨_, ⟨e, he, hKind, _, _⟩, _⟩ := Scores.publishes hp hX hPub
  obtain ⟨_, ⟨f, hf, hKind', _, _⟩, _⟩ := correctionWaits hp hX hWait
  unfold Paired at hPair
  rw [← hPair] at hKind'
  rw [Scores.barrierOrdinal, correctionBarrierOrdinal] at hOrdinal
  exact hSources.arrive_sync_kind_baseCausality hX hShape hSame
    ⟨e, he, hKind⟩ ⟨f, hf, hKind'⟩ hOrdinal hBefore hAfter hLen

private theorem producerGenerationKey {producer : EvId} {key : Nat} {round : Scores.Round}
    (hw : warpIndex l producer.1 < 8) (hPub : Scores.Publishes X producer round)
    (hKey : CtaBarArrivalK l X producer key) :
    key = 3 + warpIndex l producer.1 +
      16 * (Scores.before X producer).barrier (3 + warpIndex l producer.1) := by
  let warp : Fin 8 := ⟨warpIndex l producer.1, hw⟩
  obtain ⟨_, ⟨f, hf, hKind, _, _⟩, _⟩ := Scores.publishes hp hX hPub
  have hActual := (statsBarrierSources hp hX warp).arrival_kind_key hX
    (statsBarrierShape hp warp) ⟨f, hf, hKind⟩ hKey
  rw [Scores.barrierOrdinal]
  exact hActual

/-- A received correction credit with the matching role cursor proves that the producer's
recorded statistics arrival has released its generation. -/
theorem releasedByCorrectionCredit {producer credit : EvId} {key : Nat} {stage : Fin 2}
    {round : Scores.Round} (hSame : producer.1 / l.block = credit.1 / l.block)
    (hPair : Paired l producer.1 credit.1 stage) (hPub : Scores.Publishes X producer round)
    (hKey : CtaBarArrivalK l X producer key) {e : Event} (he : X.get credit = some e)
    (hc : correctionAction e = some (.statsCredit stage))
    (hOrd : (Scores.before X producer).barrier (3 + warpIndex l producer.1) =
      (correctionBefore X credit).count (.statsCredit stage)) :
    CtaBarDone l X (producer.1 / l.block) key := by
  have hActual := producerGenerationKey hp hX (producerWarp hPair) hPub hKey
  unfold Paired at hPair
  rw [hSame, hActual, hOrd, hPair]
  exact Correction.observedCorrectionCreditReleases hp hX stage he hc

omit hp hX in
/-- The clean arrivals in this history prefix come from correction uses below `limit`. -/
def CreditFrontier (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (cursor limit : Nat) : Prop :=
  ∀ k < cursor, ∀ r i,
    (X.objects (Correction.statsCreditLoc l cta stage))[k]? = some r → r.fault = none →
    r.action = .arrive 1 0 → r.id = .thread i →
    (correctionBefore X i).count (.statsCredit stage) < limit

omit hp hX in
private theorem warpOfCreditLane {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (cta w : Nat) (hw : w < 4) :
    let lane : Fin 128 := ⟨32*w, by omega⟩
    warpIndex l (Correction.statsCreditLane l cta lane) = 8 + w := by
  simp only [warpIndex, Correction.statsCreditLane, hp.block]
  omega

/-- A complete group of reusable statistics credits releases each covered named generation. -/
theorem releasedByCreditFrontier {producer : EvId} {key cursor limit : Nat} {stage : Fin 2}
    {round : Scores.Round} (hPub : Scores.Publishes X producer round)
    (hKey : CtaBarArrivalK l X producer key) (hStage : stage.val = warpIndex l producer.1 / 4)
    (hGeneration : (Scores.before X producer).barrier (3 + warpIndex l producer.1) < limit)
    (hUnits : 128 * limit ≤ MBarrier.unitsBefore
      (X.objects (Correction.statsCreditLoc l (producer.1 / l.block) stage)) cursor)
    (hFrontier : CreditFrontier l X (producer.1 / l.block) stage cursor limit) :
    CtaBarDone l X (producer.1 / l.block) key := by
  let cta := producer.1 / l.block
  let w := warpIndex l producer.1 % 4
  have hw : w < 4 := Nat.mod_lt _ (by decide)
  let lane : Fin 128 := ⟨32*w, by omega⟩
  let g := Correction.statsCreditLane l cta lane
  have hWarp : warpIndex l g = 8 + w := warpOfCreditLane hp cta w hw
  have hPair : Paired l producer.1 g stage := by
    unfold Paired Correction.statsBarrierId
    rw [hWarp, hStage]
    unfold w
    omega
  obtain ⟨_, _, r, hr, _, ha, hId⟩ := Correction.statsCreditCoverage hp hX stage hUnits
    (fun k hk r i _ hr hClean ha hId _ _ => hFrontier k hk r i hr hClean ha hId) lane hGeneration
  cases Correction.statsCreditHistorySource hp hX stage (List.mem_of_getElem? hr) with
  | init hi => rw [ha] at hi; cases hi
  | poll hi => rw [ha] at hi; cases hi
  | credit hid he _ hAction hOwner _ _ _ =>
    obtain rfl := AsyncCopy.Ref.thread.inj (hid.symm.trans hId)
    have hOrdinal := (nthEv_spec_of_get he).2
    have hCount := Correction.correctionCreditCursor hp hX stage he
    exact releasedByCorrectionCredit hp hX hOwner.symm hPair hPub hKey he hAction
      (hOrdinal.symm.trans hCount.symm)

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
