-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRepeatedJoinCounts
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedAffineProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.AffineWarpRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedAffineOrdinals
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction Thread.Scores

/-- The outcome of one repeated biased visit at its probability join. -/
structure BiasedVisitJoin (p : Params) (l : Launch) (X Y : Execution) (g : Nat) (warp : Fin 8)
    (visit start nextBlock counter bars elects : Nat) (old : Option ℝ) (oldSum : ℝ)
    (bias : Nat → Option ℝ) (dot : Nat → ℝ) where
  candidate : Option ℝ
  leader : Fin 32
  join : RepeatedProbabilityJoinCursor l Y g .biased warp
    (fun i => repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits)
      (-((chosenReference (abiFloat p.scaleLog2Bits) old candidate).map
        (abiFloat p.scaleLog2Bits * ·)).getD 0)
      (affineScore (abiFloat p.invScaleBits) (dot i) (bias i))))
    oldSum (maskedRescale (old.map (abiFloat p.scaleLog2Bits * ·))
      ((chosenReference (abiFloat p.scaleLog2Bits) old candidate).map
        (abiFloat p.scaleLog2Bits * ·))) (visit%2)
  bound : ∀ v : EReal, scoreReal candidate ≤ v ↔
    scoreReal old ≤ v ∧ ∀ i < 128,
      scoreReal (affineScore (abiFloat p.invScaleBits) (dot i) (bias i)) ≤ v
  stored : StatisticsStore X (g,start) (rescaleStore true) (statsAcc l g warp 0)
    (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes
  published : Scores.Publishes X (g,start+1) .biased
  mainCredit : Scores.ProbabilityCredit l Y (g,start+2+5) (g/l.block) (stageOf warp) 0
  tailCredit : laneOf l g = leader.val →
    Scores.ProbabilityCredit l Y (g,start+2+10) (g/l.block) (stageOf warp) 1
  maximum : join.values 7256 = scoreValue (chosenReference (abiFloat p.scaleLog2Bits) old candidate)
  biasPhase : join.values 7250 = b32 (visit%2)
  scorePhase : join.values 7253 = b32 (visit%2)
  counterWord : join.values 7248 = b32 counter
  blockWord : join.values 7249 = b32 nextBlock
  counts : SoftmaxCounts Y g join.cursor.pos (11*visit+11) (bars+1) (elects+1) (visit+1)
    (visit+1) (visit+1)
  elected : ∃ inst, Y.Elect (g,start+2+9) (probabilityWaitPc Repeated.biased.round true+2)
    (2^32-1) inst leader.val
  mainBefore : start+2+5 < join.cursor.pos
  tailBefore : laneOf l g = leader.val → start+2+10 < join.cursor.pos

/-- A warp at its biased FMA body with the packed scores, unpacked Bias and loop registers of
the visit publishes its statistics and probabilities and reaches the correction join. -/
theorem warpBiasedJoinOfBodies {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) {lead : Nat} (warp : Fin 8)
    (hLead : warpIndex l lead = warp.val) (visit bars elects : Nat)
    (nextBlock floor counter : Nat → Nat) (old : Nat → Option ℝ) (oldSum : Nat → ℝ)
    (bias : Nat → Nat → Option ℝ) (dot : Nat → Nat → ℝ)
    {F : ∀ g, SameWarp l lead g → List (Nat × Value)}
    (body : ∀ g (hw : SameWarp l lead g), OpeningTripCursor l X g (biasBodyStart true) (F g hw))
    (hScale : ∀ g (hw : SameWarp l lead g), readERealPair l g (body g hw).ready (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hUnpacked : ∀ g (hw : SameWarp l lead g) (i : Fin 16), BiasUnpacked true i
      (body g hw).ready (fun k =>
        biasLoadWord (bias g (8*i.val+2*k)) (bias g (8*i.val+2*k+1))))
    (hDots : ∀ g (hw : SameWarp l lead g), ∀ pair < 64,
      readERealPair l g (body g hw).ready (.reg (7367+pair)) =
        some (.ok ((dot g (2*pair) : EReal),(dot g (2*pair+1) : EReal))))
    (hPrior : ∀ g (hw : SameWarp l lead g), Holds (body g hw).ready.regs
      (biasedAffineInputFrame p l warp (old g) (oldSum g) (nextBlock g) (floor g) (visit%2)
        (b32 (visit%2)) (b32 (visit%2)) (b32 (counter g))))
    (hCounts : ∀ g (hw : SameWarp l lead g),
      SoftmaxCounts X g (body g hw).pos (11*visit+4) bars elects visit (visit+1) (visit+1)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      ∀ g (hw : SameWarp l lead g), Nonempty (BiasedVisitJoin p l X Y g warp visit
        (body g hw).pos (nextBlock g) (counter g) bars elects (old g) (oldSum g) (bias g)
        (dot g)) := by
  classical
  have hLeadWarp : warpIndex l lead < 8 := hLead ▸ warp.isLt
  have hWarpOf (g : Nat) (hw : SameWarp l lead g) : warp.val = warpIndex l g := by
    rw [← hLead]; exact hw.2
  have prepare (g : Nat) (hw : SameWarp l lead g) :=
    biasedAffineReachedOfInputsOfMaximal hp hMax hw.1.2.1 warp (hWarpOf g hw) (body g hw)
      (bias g) (dot g) (old g) (oldSum g) (nextBlock g) (floor g) (visit%2)
      (Nat.mod_lt _ (by decide)) (b32 (visit%2)) (b32 (visit%2)) (b32 (counter g))
      (hScale g hw) (hUnpacked g hw) (hDots g hw) (hPrior g hw)
  choose chosen deferred hBound hStore hNotice hPos hEnd hFrame hOperands hCont using prepare
  have hPub (g : Nat) (hw : SameWarp l lead g) :
      Scores.Publishes X (g,(deferred g hw).pos-1) .biased ∧
        (Scores.before X (g,(deferred g hw).pos-1)).notices = visit := by
    rw [hPos g hw,show ∀ n : Nat, n+2-1 = n+1 by omega]
    refine ⟨hNotice g hw,(statisticsNoticeRankAfterStore .biased (hStore g hw)).trans ?_⟩
    rw [Scores.beforeNotices]
    exact (hCounts g hw).2.2.2.1
  obtain ⟨Y,hY,hTrace,hObjects,hResume⟩ :=
    resumeAffineWarpWithObjects hp hMax hFootprint hLeadWarp .biased visit deferred hPub
  choose affine hAffinePos hAffineReady hAffineEnding using hResume
  let scores g i := affineScore (abiFloat p.invScaleBits) (dot g i) (bias g i)
  let candidate g := if hw : SameWarp l lead g then chosen g hw else none
  let reference g := (chosenReference (abiFloat p.scaleLog2Bits) (old g) (candidate g)).map
    (abiFloat p.scaleLog2Bits * ·)
  let alpha g := maskedRescale ((old g).map (abiFloat p.scaleLog2Bits * ·)) (reference g)
  have hInputs (g : Nat) (hw : SameWarp l lead g) :
      RepeatedProbabilityShiftFrame p l .biased g (stageOf warp) (affine g hw).ready
        (scores g) ((reference g).getD 0) := by
    simpa only [hAffineReady g hw,scores,candidate,reference,dite_eq_left hw]
      using Classical.choice (hFrame g hw)
  have hArithmetic (g : Nat) (hw : SameWarp l lead g) :
      RepeatedTailOperands l .biased (stageOf warp) (affine g hw).ready warp (oldSum g)
        (alpha g) (visit%2) := by
    simpa only [hAffineReady g hw,alpha,candidate,reference,dite_eq_left hw]
      using Classical.choice (hOperands g hw)
  have hStats g (hw : SameWarp l lead g) :=
    repeatedStatisticsKeepOrdinals .biased (hStore g hw) (hNotice g hw)
  have hAffineCounts (g : Nat) (hw : SameWarp l lead g) :
      SoftmaxCounts Y g (affine g hw).pos (11*visit+4) bars elects (visit+1) (visit+1)
        (visit+1) := by
    apply SoftmaxCounts.ofTrace hTrace
    rw [hAffinePos g hw,hPos g hw]
    obtain ⟨tc,wb,el⟩ := hStats g hw
    obtain ⟨nEv,hnGet,hnNotice⟩ := hNotice g hw
    have hCreditSilent : Scores.creditAcquired nEv = false := by
      rcases nEv with ⟨pc,kind⟩
      cases kind <;> simp_all [Scores.notice,Scores.creditAcquired]
    have hScoreSilent : scoreAcquired nEv = false := by
      rcases nEv with ⟨pc,kind⟩
      cases kind <;> simp_all [Scores.notice,scoreAcquired]
    have two : (body g hw).pos+2 = (body g hw).pos+1+1 := by omega
    refine ⟨tc.trans (hCounts g hw).1,wb.trans (hCounts g hw).2.1,el.trans (hCounts g hw).2.2.1,
      ?_,?_,?_⟩ <;> rw [two]
    · rw [countP_take_succ (p := Scores.publishesStats) hnGet
        (by simp [Scores.publishesStats,hnNotice]),
        countP_take_succ_false (hStore g hw) rfl,(hCounts g hw).2.2.2.1]
    · rw [countP_take_succ_false hnGet hCreditSilent,
        countP_take_succ_false (hStore g hw) rfl,(hCounts g hw).2.2.2.2.1]
    · rw [countP_take_succ_false hnGet hScoreSilent,
        countP_take_succ_false (hStore g hw) rfl,(hCounts g hw).2.2.2.2.2]
  have joins := warpRepeatedProbabilityJoinWithCountsOfMaximal hp hY .biased (stageOf warp)
    (11*visit+4) bars elects scores (fun g => (reference g).getD 0) (fun _ => warp) oldSum alpha
    (fun _ => visit%2) affine hInputs hArithmetic (fun g hw => (hAffineCounts g hw).1)
    (fun g hw => (hAffineCounts g hw).2.1) (fun g hw => (hAffineCounts g hw).2.2.1)
    (fun _ => visit+1) (fun _ => visit+1) (fun _ => visit+1)
    (fun g hw => (hAffineCounts g hw).2.2.2.1) (fun g hw => (hAffineCounts g hw).2.2.2.2.1)
    (fun g hw => (hAffineCounts g hw).2.2.2.2.2)
  refine ⟨Y,hY,hTrace,hObjects,?_⟩
  intro g hw
  obtain ⟨leader,j,_,hMain,hTail,_,hValues,hJoinCounts,hElected,hJoinLe,hJoinLt⟩ :=
    joins g hw
  have hc : candidate g = chosen g hw := dite_eq_left hw
  have hStart : (affine g hw).pos = (body g hw).pos+2 := (hAffinePos g hw).trans (hPos g hw)
  rw [hStart] at hElected hJoinLe hJoinLt
  have value (n : Nat) (hn : n ∈ Repeated.biased.continuationRegs) {v : Value}
      (h : (deferred g hw).ready.regs n = some v) : j.values n = v := by
    have e := hValues n hn
    rw [hAffineReady g hw,h] at e
    exact (Option.some.inj e).symm
  obtain ⟨c7256,c7250,c7253,c7248,c7249⟩ := hCont g hw
  rw [hStart] at hMain hTail
  refine ⟨⟨candidate g,leader,j,?_,?_,hNotice g hw,hMain,hTail,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [hc]; exact hBound g hw
  · rw [hc]; exact hStore g hw
  · exact (value 7256 (by decide) c7256).trans (by rw [hc])
  · exact value 7250 (by decide) c7250
  · exact value 7253 (by decide) c7253
  · exact value 7248 (by decide) c7248
  · exact value 7249 (by decide) c7249
  · exact hJoinCounts
  · exact hElected
  · rw [ite_eq_left rfl] at hJoinLe; omega
  · intro hLead
    have h := hJoinLt hLead
    rw [ite_eq_left rfl] at h
    omega

end PTX.Kernels.TmlFa4Fwd.Softmax
