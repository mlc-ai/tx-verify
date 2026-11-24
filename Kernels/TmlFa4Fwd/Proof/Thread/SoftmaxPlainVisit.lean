-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedStageVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.PlainWarpAffineProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreProgress
import all Lemmas.Flow.RecordedCheckpointPath
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePollRanks
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.Safety.TmemWordSizes
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
import Lemmas.Flow.CountTake
import Lemmas.Flow.SplitJoin
import Lemmas.Flow.Widen
import Lemmas.Flow.Regs

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction Thread.Scores

/-- The registers kept from the plain loop head to the score loads. -/
noncomputable def plainHeadKept (p : Params) (warp : Fin 8) (visit counter : Nat)
    (maximum : Option ℝ) (sum : ℝ) : List (Nat × Value) :=
  [(5127,b32 (3+warp.val)),(1230,fl (-abiFloat p.scaleLog2Bits)),(7133,b32 p.scaleLog2Bits),
    (8692,joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)),(7254,b32 counter),
    (7255,scoreValue maximum),(7256,scoreValue maximum),(7257,fl sum),(7258,b32 (visit%2))]

/-- The registers live at the head of the plain loop (pc 6661) in every visit. -/
noncomputable def plainHeadFacts (p : Params) (l : Launch) (warp : Fin 8) (visit counter : Nat)
    (maximum : Option ℝ) (sum : ℝ) : List (Nat × Value) :=
  (1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 (visit%2))::
    plainHeadKept p warp visit counter maximum sum

/-- The kept registers carried through the score acquire, including the ABI words. -/
noncomputable def plainReturnedKept (p : Params) (l : Launch) (warp : Fin 8) (visit counter : Nat)
    (maximum : Option ℝ) (sum : ℝ) : List (Nat × Value) :=
  (1062,b32 warp.val)::(2535,b32 l.sharedBase)::plainHeadKept p warp visit counter maximum sum

/-- A lane at the head of the plain loop at a lane pc (the head or the plain exit). -/
structure PlainLoopAt (p : Params) (l : Launch) (X : Execution) (g : Nat) (warp : Fin 8)
    (pc visit counter tc bars elects : Nat) (maximum : Option ℝ) (sum : ℝ) where
  valid : DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g pc (plainHeadFacts p l warp visit counter maximum sum)
  scores : okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf warp))
    ((X.tr g).take cursor.pos) = visit
  counts : SoftmaxCounts X g cursor.pos tc bars elects visit (visit+1) visit

private theorem plainKeptStable (p : Params) (l : Launch) (warp : Fin 8) (visit counter : Nat)
    (maximum : Option ℝ) (sum : ℝ) :
    ∀ x ∈ plainReturnedKept p l warp visit counter maximum sum,
      x.1 ∉ unbiasedSetupWrites ∧ x.1 ≠ 9821 := by
  intro x hx
  simp only [plainReturnedKept,plainHeadKept,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by dsimp only; decide,by dsimp only; decide⟩

/-- A plain head lane whose score is ready (when pending) returns from the score acquire. -/
structure PlainScoreReturned (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (visit counter tc bars elects : Nat) (maximum : Option ℝ) (sum : ℝ) where
  head : PlainLoopAt p l X g warp 6661 visit counter tc bars elects maximum sum
  returned : RepeatedScoreCursor l X g .unbiased (stageOf warp) (visit%2)
    (plainReadyFacts l g warp (visit%2) (plainReturnedKept p l warp visit counter maximum sum))
  after : head.cursor.pos ≤ returned.index
  ending : returned.cursor.ending = head.cursor.ending
  counts : SoftmaxCounts X g returned.cursor.pos tc bars elects visit (visit+1) (visit+1)

theorem PlainLoopAt.scoreReturnedOfPending {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g visit counter tc bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    (hg : g < l.threads) {warp : Fin 8} (hw : warp.val = warpIndex l g)
    (c : PlainLoopAt p l X g warp 6661 visit counter tc bars elects maximum sum)
    (hReady : let loc := Scores.scoreReadyObject l (g/l.block) (stageOf warp)
      okPolls loc (X.tr g) = visit → OpeningPollReady X loc (visit%2)) :
    Nonempty (PlainScoreReturned p l X g warp visit counter tc bars elects maximum sum) := by
  have hStable := plainKeptStable p l warp visit counter maximum sum
  have regs := c.cursor.checkpoint.2.2.2.2
  let c' : OpeningTripCursor l X g 6661 ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::
      (7253,b32 (visit%2))::plainReturnedKept p l warp visit counter maximum sum) :=
    ⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
      c.cursor.bounded,c.cursor.released,
      c.cursor.checkpoint.mono ⟨regs.1,regs.2.1,regs.2.2.1,regs.1,regs.2.1,regs.2.2.2⟩,
      c.cursor.recorded,c.cursor.remaining,c.cursor.localSteps⟩
  obtain ⟨u,hOrder,hEnd,trace⟩ := plainScoreReturnOfPending hp hMax hg warp (visit%2)
    (Nat.mod_lt _ (by decide)) _ (fun x hx => (hStable x hx).1) (fun x hx => (hStable x hx).2)
    c' (fun h => hReady (h.trans c.scores))
  let loc := Scores.scoreReadyObject l (g/l.block) (stageOf warp)
  let poll (ok : Bool) := Event.mk (waitSite (qkWaitSite .unbiased)).pc
    (.wait loc (visit%2) ok true .cta)
  let window := List.replicate (u.index-c.cursor.pos) (poll false) ++ [poll true]
  have size : c.cursor.pos+window.length = u.cursor.pos := by
    have := u.position
    simp [window]
    change c.cursor.pos ≤ u.index at hOrder
    omega
  have cut : (X.tr g).drop c.cursor.pos = window ++ (X.tr g).drop u.cursor.pos := by
    simpa [window,poll,loc] using trace
  have step : okPolls loc ((X.tr g).take u.cursor.pos) =
      okPolls loc ((X.tr g).take c.cursor.pos)+1 := by
    rw [← size,List.take_add,cut,List.take_append_length]
    simp [okPolls,window,poll,List.countP_append,List.countP_replicate,okPoll,sourceWaitSuccess]
  have polls := step.trans (congrArg (·+1) c.scores)
  have keep {mark : Event → Bool} (hm : ∀ ok, mark (poll ok) = false) :=
    repeatedScorePollKeepsCount hOrder u.position trace hm
  have hStage : (stageOf warp).val = warpIndex l g/4 := by rw [← hw]; rfl
  refine ⟨⟨c,u,hOrder,hEnd,(keep (fun _ => rfl)).trans c.counts.1,
    (keep (fun _ => rfl)).trans c.counts.2.1,(keep (fun _ => rfl)).trans c.counts.2.2.1,
    (keep (fun _ => rfl)).trans c.counts.2.2.2.1,
    (keep (fun ok => by cases ok <;> rfl)).trans c.counts.2.2.2.2.1,?_⟩⟩
  rw [← scorePollCursor hp hMax.1 (stageOf warp) hStage]
  exact polls

/-- The ABI scale of the plain exponent, packed on both halves. -/
theorem plainScalePair {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat}
    {s : TState}
    (h : s.regs 8692 = some (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits))) :
    readERealPair l g s (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))) := by
  obtain ⟨q,_,hDecode,_,_,_⟩ := hp.scales
  have bits := (hp.values (12,p.scaleLog2Bits) (by simp [Params.scalarWords])).1
  have val := valFloat_b32 (by omega) hDecode
  have halves : splitValue 64 (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)) =
      (b32 p.scaleLog2Bits,b32 p.scaleLog2Bits) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact bits)
  rw [show abiFloat p.scaleLog2Bits = (q : ℝ) by simp [abiFloat,hDecode]]
  exact readERealPair_reg h (by rw [halves]; exact val) (by rw [halves]; exact val)

/-- The outcome of one repeated plain visit at its probability join. -/
structure PlainVisitJoin (p : Params) (l : Launch) (X Y : Execution) (g : Nat) (warp : Fin 8)
    (visit start counter tc bars elects : Nat) (old : Option ℝ) (oldSum : ℝ) where
  scores : Nat → Option ℝ
  candidate : Option ℝ
  leader : Fin 32
  join : RepeatedProbabilityJoinCursor l Y g .unbiased warp
    (fun i => repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits)
      (-((chosenReference (abiFloat p.scaleLog2Bits) old candidate).map
        (abiFloat p.scaleLog2Bits * ·)).getD 0) (scores i)))
    oldSum (maskedRescale (old.map (abiFloat p.scaleLog2Bits * ·))
      ((chosenReference (abiFloat p.scaleLog2Bits) old candidate).map
        (abiFloat p.scaleLog2Bits * ·))) (visit%2)
  bound : ∀ v : EReal, scoreReal candidate ≤ v ↔
    scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (scores i) ≤ v
  stored : StatisticsStore X (g,start+8) (rescaleStore false) (statsAcc l g warp 1)
    (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes
  published : Scores.Publishes X (g,start+9) .plain
  mainCredit : Scores.ProbabilityCredit l Y (g,start+14) (g/l.block) (stageOf warp) 0
  tailCredit : laneOf l g = leader.val →
    Scores.ProbabilityCredit l Y (g,start+19) (g/l.block) (stageOf warp) 1
  maximum : join.values 7256 = scoreValue (chosenReference (abiFloat p.scaleLog2Bits) old candidate)
  scorePhase : join.values 7253 = b32 (visit%2)
  counterWord : join.values 7254 = b32 counter
  counts : SoftmaxCounts Y g join.cursor.pos (tc+14) (bars+1) (elects+1) (visit+1)
    (visit+1) (visit+1)
  elected : ∃ inst, Y.Elect (g,start+18) (probabilityWaitPc Repeated.unbiased.round true+2)
    (2^32-1) inst leader.val
  mainBefore : start+14 < join.cursor.pos
  tailBefore : laneOf l g = leader.val → start+19 < join.cursor.pos

private theorem creditNotTc (e : Event) (h : Scores.creditAcquired e = true) :
    isTcColl e = false := by
  rcases e with ⟨pc,kind⟩
  cases kind <;> simp_all [Scores.creditAcquired,isTcColl]

private theorem creditNotNotice (e : Event) (h : Scores.publishesStats e = true) :
    Scores.creditAcquired e = false := by
  rcases e with ⟨pc,kind⟩
  cases kind <;> simp_all [Scores.creditAcquired,Scores.publishesStats,Scores.notice]

private theorem scoreNotTc (e : Event) (h : scoreAcquired e = true) : isTcColl e = false := by
  rcases e with ⟨pc,kind⟩
  cases kind <;> simp_all [scoreAcquired,isTcColl]

private theorem scoreNotNotice (e : Event) (h : Scores.publishesStats e = true) :
    scoreAcquired e = false := by
  rcases e with ⟨pc,kind⟩
  cases kind <;> simp_all [scoreAcquired,Scores.publishesStats,Scores.notice]

/-- A warp whose plain scores returned publishes its statistics and probabilities and reaches
the correction join. -/
theorem warpPlainJoinOfReturned {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) {lead : Nat} (warp : Fin 8)
    (hLead : warpIndex l lead = warp.val) (visit tc bars elects : Nat)
    (counter : Nat → Nat) (old : Nat → Option ℝ) (oldSum : Nat → ℝ)
    (rows : ∀ g, SameWarp l lead g → PlainScoreReturned p l X g warp visit (counter g) tc bars
      elects (old g) (oldSum g)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      ∀ g (hw : SameWarp l lead g), Nonempty (PlainVisitJoin p l X Y g warp visit
        (rows g hw).returned.cursor.pos (counter g) tc bars elects (old g) (oldSum g)) := by
  classical
  have hLeadWarp : warpIndex l lead < 8 := hLead ▸ warp.isLt
  have hWarpOf (g : Nat) (hw : SameWarp l lead g) : warp.val = warpIndex l g := by
    rw [← hLead]; exact hw.2
  let input g hw := (rows g hw).returned.cursor
  have mem (g : Nat) (hw : SameWarp l lead g) {x : Nat × Value}
      (hx : x ∈ plainReadyFacts l g warp (visit%2)
        (plainReturnedKept p l warp visit (counter g) (old g) (oldSum g))) :
      (input g hw).ready.regs x.1 = some x.2 := holds_mem (input g hw).checkpoint.2.2.2.2 hx
  obtain ⟨Y,hY,hTrace,hObjects,ready⟩ := warpPlainAffineFromScoreWithObjectsOfMaximal hp hMax
    hFootprint (Progress.syncGuarded hp hMax.1 (hFootprint.metadataProtected hp).1)
    (Mma.actualMmaLayoutInjective hMax.1) hLeadWarp warp tc bars elects visit old oldSum
    (fun _ => visit%2) (fun _ => b32 (visit%2)) (fun g => b32 (counter g)) input hWarpOf
    (fun g hw q => by
      simp only [plainReadyFacts,plainReadySetup,List.mem_append]
      exact .inr (.inl (.inr (.inr (List.mem_ofFn.mpr ⟨q,rfl⟩)))))
    (fun g hw => (rows g hw).counts.1) (fun g hw => (rows g hw).counts.2.1)
    (fun g hw => (rows g hw).counts.2.2.1)
    (fun g hw => by rw [Scores.beforeNotices]; exact (rows g hw).counts.2.2.2.1)
    (fun g hw q k hk v last => by
      obtain ⟨_,source,_⟩ := last
      exact Safety.tensorWroteWordBytes hp hMax.1 source)
    (fun g hw => by
      apply frameOfFacts
      intro pair hPair
      apply mem g hw
      simp only [plainAffineInputFrame,List.mem_cons,List.not_mem_nil,or_false] at hPair
      rw [hWarpOf g hw] at hPair
      rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
        simp [plainReadyFacts,plainReadySetup,unbiasedAddressRows,plainReturnedKept,
          plainHeadKept,scoreColumn,stageOf,hWarpOf g hw])
    (fun _ _ => Nat.mod_lt _ (by decide))
    (fun g hw => plainScalePair hp (mem g hw
      (x := (8692,joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)))
      (by simp [plainReturnedKept,plainHeadKept,plainReadyFacts])))
    (fun g hw q => mem g hw
      (x := (probabilityReg .unbiased q,b32 (probabilityAddress l g (stageOf warp) q))) (by
      fin_cases q <;> simp [plainReadyFacts,plainReadySetup,unbiasedProbabilityFacts,
        probabilityReg]))
  choose physical chosen affine hAt hEnding hTc hBars hElects hStore hNotice hFrame hOperands
    hCont hNotices hOthers hBound using ready
  let scores g i := if hw : SameWarp l lead g then some (physical g hw i) else none
  let candidate g := if hw : SameWarp l lead g then chosen g hw else none
  let reference g := (chosenReference (abiFloat p.scaleLog2Bits) (old g) (candidate g)).map
    (abiFloat p.scaleLog2Bits * ·)
  let alpha g := maskedRescale ((old g).map (abiFloat p.scaleLog2Bits * ·)) (reference g)
  have hInputs (g : Nat) (hw : SameWarp l lead g) :
      RepeatedProbabilityShiftFrame p l .unbiased g (stageOf warp) (affine g hw).ready
        (scores g) ((reference g).getD 0) := by
    simpa only [scores,candidate,reference,dite_eq_left hw] using Classical.choice (hFrame g hw)
  have hArithmetic (g : Nat) (hw : SameWarp l lead g) :
      RepeatedTailOperands l .unbiased (stageOf warp) (affine g hw).ready warp (oldSum g)
        (alpha g) (visit%2) := by
    simpa only [alpha,candidate,reference,dite_eq_left hw] using Classical.choice (hOperands g hw)
  have hCred (g : Nat) (hw : SameWarp l lead g) :
      ((Y.tr g).take (affine g hw).pos).countP Scores.creditAcquired = visit+1 :=
    (hOthers g hw _ creditNotTc creditNotNotice (fun _ _ _ => rfl)).trans
      (rows g hw).counts.2.2.2.2.1
  have hScr (g : Nat) (hw : SameWarp l lead g) :
      ((Y.tr g).take (affine g hw).pos).countP scoreAcquired = visit+1 :=
    (hOthers g hw _ scoreNotTc scoreNotNotice (fun _ _ _ => rfl)).trans
      (rows g hw).counts.2.2.2.2.2
  have joins := warpRepeatedProbabilityJoinWithCountsOfMaximal hp hY .unbiased (stageOf warp)
    (tc+8) bars elects scores (fun g => (reference g).getD 0) (fun _ => warp) oldSum alpha
    (fun _ => visit%2) affine hInputs hArithmetic hTc hBars hElects (fun _ => visit+1)
    (fun _ => visit+1) (fun _ => visit+1)
    (fun g hw => (hNotices g hw).trans (congrArg (·+1) (rows g hw).counts.2.2.2.1)) hCred hScr
  refine ⟨Y,hY,hTrace,hObjects,?_⟩
  intro g hw
  obtain ⟨leader,j,_,hMain,hTail,_,hValues,hJoinCounts,hElected,hJoinLe,hJoinLt⟩ :=
    joins g hw
  have hc : candidate g = chosen g hw := dite_eq_left hw
  have value (n : Nat) (hn : n ∈ Repeated.unbiased.continuationRegs) {v : Value}
      (h : (affine g hw).ready.regs n = some v) : j.values n = v :=
    (Option.some.inj ((hValues n hn).symm.trans h))
  obtain ⟨c7256,c7253,c7254⟩ := hCont g hw
  have hStart : (affine g hw).pos = (input g hw).pos+10 := hAt g hw
  rw [hStart] at hMain hTail hElected hJoinLe hJoinLt
  have hsc : scores g = fun i => some (physical g hw i) := by
    funext i; simp only [scores,dite_eq_left hw]
  refine ⟨⟨scores g,candidate g,leader,j,?_,?_,hNotice g hw,hMain,hTail,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [hc,hsc]; exact hBound g hw
  · rw [hc]; exact hStore g hw
  · exact (value 7256 (by decide) c7256).trans (by rw [hc])
  · exact value 7253 (by decide) c7253
  · exact value 7254 (by decide) c7254
  · exact hJoinCounts
  · exact hElected
  · rw [ite_eq_right (by decide)] at hJoinLe
    have : (affine g hw).pos = (rows g hw).returned.cursor.pos+10 := hAt g hw
    omega
  · intro hLead
    have h := hJoinLt hLead
    rw [ite_eq_right (by decide)] at h
    have : (affine g hw).pos = (rows g hw).returned.cursor.pos+10 := hAt g hw
    omega

private theorem plainPhaseBit (v : Nat) : (decide (v%2 = 1)).toNat = v%2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

private theorem plainNextPhaseBit (v : Nat) : (!decide (v%2 = 1)).toNat = (v+1)%2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

/-- After the correction credit a plain visit updates its denominator and takes the loop
back edge to the next plain head, or to the terminal statistics when the counter wraps. -/
theorem PlainVisitJoin.nextOfPending {p : Params} {l : Launch} {m : Mem0}
    {X₀ X Y : Execution} (hp : Pre p l m) (hMax₀ : Maximal l kernel Assumptions.all m X₀)
    (hMax : Maximal l kernel Assumptions.all m Y) (hTrace : Y.tr = X₀.tr)
    {g : Nat} (hg : g < l.threads) {warp : Fin 8} (hw : warp.val = warpIndex l g)
    {visit counter tc bars elects start : Nat} {old : Option ℝ} {oldSum : ℝ}
    (head : PlainLoopAt p l X₀ g warp 6661 visit counter tc bars elects old oldSum)
    (J : PlainVisitJoin p l X Y g warp visit start counter tc bars elects old oldSum)
    (hOrder : head.cursor.pos < J.join.cursor.pos) (hCounter : counter < 2^32)
    (hReady : (Y.tr g).countP Scores.creditAcquired = visit+1 →
      OpeningPollReady Y (waitLoc l g (stageOf warp) Repeated.unbiased.correctionSite)
        (visit%2)) :
    let scale := abiFloat p.scaleLog2Bits
    let chosen := chosenReference scale old J.candidate
    let ref := chosen.map (scale * ·)
    let mass := oldSum*maskedRescale (old.map (scale * ·)) ref +
      ∑ i ∈ Finset.range 128, repeatedExpWeight (affineScore scale (-ref.getD 0) (J.scores i))
    let next := (counter+1)%2^32
    Nonempty (PlainLoopAt p l X₀ g warp
      (if next ≠ 0 then 6661 else (scoreLoopSite .plain).increment+4) (visit+1)
      next (tc+14) (bars+1) (elects+1) chosen mass) := by
  intro scale chosen ref mass next
  obtain ⟨index,u,he,hUPos,hUEnd,hU7258,hUCont,hLe,window⟩ :=
    J.join.denominatorOfPending hp hMax hg (visit+1) J.counts.2.2.2.2.1 hReady
  have cont (n : Nat) (hn : n ∈ Repeated.unbiased.continuationRegs) {v : Value}
      (h : J.join.values n = v) : u.ready.regs n = some v :=
    (hUCont n hn).trans (congrArg some h)
  let phase := decide (visit%2 = 1)
  have hPhaseNat : phase.toNat = visit%2 := plainPhaseBit visit
  obtain ⟨after,hAPos,hAEnd,_,hARes⟩ :=
    repeatedLoopOfDenominatorCursor .unbiased chosen mass counter hCounter phase phase phase u
      (cont 7256 (by decide) J.maximum) (cont 7254 (by decide) J.counterWord)
      (by rw [hPhaseNat]; exact hU7258) nofun
      (by rw [hPhaseNat]; exact cont 7253 (by decide) J.scorePhase)
  have hJoinLe : J.join.cursor.pos ≤ index := hLe
  have hLt : head.cursor.pos < u.pos := by omega
  have hUBound : u.pos ≤ (X₀.tr g).length := by rw [← hTrace]; exact u.bounded
  have hURec : Run kernel Assumptions.all l g {} ((X₀.tr g).take u.pos) (some u.before) := by
    rw [← hTrace]; exact u.recorded
  have hPath := traceBetweenLaterIndex hLt hUBound head.cursor.recorded head.cursor.localSteps
    hURec u.localSteps
  have hHeadPc : head.cursor.ready.pc = 6661 := head.cursor.checkpoint.1
  have hKeep := scoreTraceKeepsResidents .plain hPath (by rw [hHeadPc]; decide)
    (by rw [u.checkpoint.1]; decide) (by rw [head.cursor.checkpoint.2.1]; decide)
  have headRegs := head.cursor.checkpoint.2.2.2.2
  have resident (r : Nat) (hr : r ∈ loopResident .plain) {v : Value}
      (h : head.cursor.ready.regs r = some v) : after.ready.regs r = some v :=
    ((hARes r hr).trans (hKeep r hr)).trans h
  have hd (r : Nat) {v : Value} (h : (r,v) ∈ plainHeadFacts p l warp visit counter old oldSum) :
      head.cursor.ready.regs r = some v := holds_mem headRegs h
  have aRegs := after.checkpoint.2.2.2.2
  have aReg (r : Nat) {v : Value} (h : (r,v) ∈ [(7254,b32 next),(7255,scoreValue chosen),
      (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat),
      (7253,b32 (!phase).toNat)]) : after.ready.regs r = some v := holds_mem aRegs h
  have hNext : (!phase).toNat = (visit+1)%2 := plainNextPhaseBit visit
  have hFrame : Holds after.ready.regs
      (plainHeadFacts p l warp (visit+1) next chosen mass) := by
    apply frameOfFacts
    intro pair hPair
    simp only [plainHeadFacts,plainHeadKept,List.mem_cons,List.not_mem_nil,or_false] at hPair
    rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact resident 1062 (by decide) (hd _ (by simp [plainHeadFacts]))
    · exact resident 2535 (by decide) (hd _ (by simp [plainHeadFacts]))
    · rw [← hNext]; exact aReg 7253 (by simp)
    · exact resident 5127 (by decide) (hd _ (by simp [plainHeadFacts,plainHeadKept]))
    · exact resident 1230 (by decide) (hd _ (by simp [plainHeadFacts,plainHeadKept]))
    · exact resident 7133 (by decide) (hd _ (by simp [plainHeadFacts,plainHeadKept]))
    · exact resident 8692 (by decide) (hd _ (by simp [plainHeadFacts,plainHeadKept]))
    · exact aReg 7254 (by simp)
    · exact aReg 7255 (by simp)
    · exact aReg 7256 (by simp)
    · exact aReg 7257 (by simp)
    · rw [← hNext]; exact aReg 7258 (by simp)
  let credit (ok : Bool) := Event.mk (waitSite Repeated.unbiased.correctionSite).pc
    (.wait (waitLoc l g (stageOf warp) Repeated.unbiased.correctionSite) (visit%2) ok true .cta)
  have keep {mark : Event → Bool} (hm : ∀ ok, mark (credit ok) = false) :=
    repeatedScorePollKeepsCount hLe hUPos window hm
  let pollWindow := List.replicate (index-J.join.cursor.pos) (credit false) ++ [credit true]
  have size : J.join.cursor.pos+pollWindow.length = u.pos := by
    simp [pollWindow]
    omega
  have cut : (Y.tr g).drop J.join.cursor.pos = pollWindow ++ (Y.tr g).drop u.pos := by
    simpa [pollWindow,credit] using window
  have creditStep : ((Y.tr g).take u.pos).countP Scores.creditAcquired =
      ((Y.tr g).take J.join.cursor.pos).countP Scores.creditAcquired+1 := by
    rw [← size,List.take_add,cut,List.take_append_length]
    simp [pollWindow,credit,List.countP_append,List.countP_replicate,Scores.creditAcquired]
    decide
  have c := J.counts
  have countsY : SoftmaxCounts Y g u.pos (tc+14) (bars+1) (elects+1) (visit+1)
      (visit+1+1) (visit+1) :=
    ⟨(keep (fun _ => rfl)).trans c.1,(keep (fun _ => rfl)).trans c.2.1,
      (keep (fun _ => rfl)).trans c.2.2.1,(keep (fun _ => rfl)).trans c.2.2.2.1,
      creditStep.trans (congrArg (·+1) c.2.2.2.2.1),
      (keep (fun ok => by cases ok <;> rfl)).trans c.2.2.2.2.2⟩
  have countsX := SoftmaxCounts.ofTrace hTrace.symm countsY
  have heX : X₀.get (g,index) = Y.get (g,index) := by
    simp only [Execution.get,hTrace]
  let cur : OpeningTripCursor l X₀ g
      (if next ≠ 0 then 6661 else (scoreLoopSite .plain).increment+4)
      (plainHeadFacts p l warp (visit+1) next chosen mass) :=
    ⟨after.pos,after.before,after.ready,after.ending,after.positive,
      by rw [← hTrace]; exact after.bounded,
      fun h => Prologue.releasedIfLast (heX.trans he) (by simp [Kind.resume])
        (by rw [← hUPos,← hAPos,h]),
      ⟨after.checkpoint.1,after.checkpoint.2.1,after.checkpoint.2.2.1,after.checkpoint.2.2.2.1,
        hFrame⟩,
      by rw [← hTrace]; exact after.recorded,by rw [← hTrace]; exact after.remaining,
      after.localSteps⟩
  have hStage : (stageOf warp).val = warpIndex l g/4 := by rw [← hw]; rfl
  have hCurPos : cur.pos = u.pos := hAPos
  refine ⟨⟨repeatedDenominatorValid head.valid _ J.bound,cur,?_,?_⟩⟩
  · rw [scorePollCursor hp hMax₀.1 (stageOf warp) hStage,hCurPos]
    exact countsX.2.2.2.2.2
  · rw [hCurPos]
    exact countsX

end PTX.Kernels.TmlFa4Fwd.Softmax
