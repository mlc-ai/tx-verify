-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpOrdinalPoll
public import Kernels.TmlFa4Fwd.Proof.Progress.RecurringCacheAcquire
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringProbabilityCohorts
public import Kernels.TmlFa4Fwd.Proof.MmaReadySegments
import Kernels.TmlFa4Fwd.Proof.Thread.Mma

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem cacheReadyObject (l : Launch) (g use : Nat) :
    Thread.Loader.readyObject l g (readyStage use) =
      ⟨.shared,g/l.block,readyAddr l use⟩ := by
  simp only [Thread.Loader.readyObject,Loader.readySlot_address,readyAddr,Nat.add_assoc]

private theorem sameWarpAtMma {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g lane : Nat} (hg : g < l.threads) (hRole : warpIndex l g = 12) (hl : lane < 32) :
    warpLane l g lane < l.threads ∧ warpIndex l (warpLane l g lane) = 12 ∧
      (warpLane l g lane)/l.block = g/l.block := by
  have hw : SameWarp l g (warpLane l g lane) := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  exact ⟨hw.1.2.1,hw.2.symm.trans hRole,hw.1.2.2.symm⟩

/-- Delivered cache copies unblock exactly the generation of the addressed K/V
slot if it is still pending, including when other slots are further ahead. -/
theorem mmaWarpCachePollOfDelivered {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use shuffles votes : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    (site : Fin 14) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (waitSite site).pc F shuffles votes ends)
    (hOperands : ∀ lane < 32, (∀ pair ∈ F lane, pair.1 ≠ (waitSite site).result) ∧
      ((waitSite site).base,b32 (readyAddr l use)) ∈ F lane ∧
      ((waitSite site).phase,b32 (readyWord use)) ∈ F lane)
    (hOrdinal : ∀ lane < 32, okPolls ⟨.shared,g/l.block,readyAddr l use⟩
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = use/3)
    (hDelivered : Protocol.LoaderReady.DeliveredCohort l X g (readyStage use) (use/3)) :
    WarpOrdinalPollAdvance l X g site (readyAddr l use) (readyWord use)
      shuffles votes F ends cur := by
  have hSlot := (readyStage use).isLt
  have hBase := hp.shared.2.1
  have hDiv := hp.shared.1
  have hWidth : readyAddr l use < 2^32 := by unfold readyAddr; omega
  have hAlign : readyAddr l use%8 = 0 := by unfold readyAddr; omega
  apply mmaWarpOrdinalPollReturnedOfMaximal hp hMax hg site hWidth hAlign (readyWord_lt use)
    cur hOperands hOrdinal
  intro lane hl hTotal
  let peer := warpLane l g lane
  have ⟨ht,hw,hCta⟩ := sameWarpAtMma hp hg hWarp hl
  change peer/l.block = g/l.block at hCta
  have hRank : (Thread.Mma.atPrefix l X peer (X.tr peer).length).kvAcquires
      (readyStage use) = use/3 := by
    rw [Thread.Mma.atPrefix,Thread.Mma.kvAcquireCount]
    change okPolls (Thread.Loader.readyObject l peer (readyStage use))
      ((X.tr peer).take (X.tr peer).length) = _
    rw [cacheReadyObject,List.take_length]
    exact hCta ▸ hTotal
  have hPub : Protocol.LoaderReady.DeliveredCohort l X peer (readyStage use) (use/3) := by
    unfold Protocol.LoaderReady.DeliveredCohort at hDelivered ⊢
    simpa only [cacheReadyObject, hCta] using hDelivered
  have h := Protocol.LoaderReady.readyPhaseOfUnconsumedCohort hp hMax.1 ht hw hPub hRank
  dsimp only [peer] at hCta
  simpa only [cacheReadyObject,hCta,readyWord,MbarRing.Index.round,Nat.mod_mod] using h

/-- The softmax/correction cohort unblocks its own P object at exactly the
specified visit, unless this lane's corresponding acquire is already recorded. -/
theorem mmaWarpProbabilityPollOfCohort {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X)
    {g gen shuffles votes : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12)
    (site : Fin 14) (stage packet : Fin 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (waitSite site).pc F shuffles votes ends)
    (hOperands : ∀ lane < 32, (∀ pair ∈ F lane, pair.1 ≠ (waitSite site).result) ∧
      ((waitSite site).base,b32 (l.sharedBase+(96+8*stage.val+16*packet.val))) ∈ F lane ∧
      ((waitSite site).phase,b32 (gen%2)) ∈ F lane)
    (hOrdinal : ∀ lane < 32, okPolls (Thread.Scores.probabilityObject l (g/l.block) stage packet)
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = gen)
    (hCohort : Protocol.Scores.ProbabilityCohort l X (g/l.block) stage packet gen) :
    WarpOrdinalPollAdvance l X g site (l.sharedBase+(96+8*stage.val+16*packet.val)) (gen%2)
      shuffles votes F ends cur := by
  let addr := l.sharedBase+(96+8*stage.val+16*packet.val)
  have hStage := stage.isLt
  have hPacket := packet.isLt
  have hBase := hp.shared.2.1
  have hDiv := hp.shared.1
  have hWidth : addr < 2^32 := by dsimp [addr]; omega
  have hAlign : addr%8 = 0 := by dsimp [addr]; omega
  apply mmaWarpOrdinalPollReturnedOfMaximal hp hMax hg site hWidth hAlign (Nat.mod_lt _ (by decide))
    cur hOperands hOrdinal
  intro lane hl hTotal
  have ⟨ht,hw,hCta⟩ := sameWarpAtMma hp hg hWarp hl
  have h := Protocol.Scores.probabilityReadyOfUnconsumedCohort hp hMax.1 hGuard ht hw stage packet
    (by rw [hCta]; exact hCohort)
    (by rw [hCta]; exact hTotal)
  simpa only [Thread.Scores.probabilityObject,hCta,addr] using h

end
end PTX.Kernels.TmlFa4Fwd.Mma
