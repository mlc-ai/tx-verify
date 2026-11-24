-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskMaximum
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals
public import Kernels.TmlFa4Fwd.Proof.SoftmaxReference
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasRendezvousProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMaskCursor
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityOrdinal
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningAffineLaunchScores
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstRound
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxNamedBarrierIds
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasAffineNumerics
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords


@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

/-- Once the first causal mask is evaluated, the local maximum and reference lead to the
actual opening statistics publication even if the recorded suffix initially stops there. -/
private theorem openingStatisticsFromMask {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} {t u : TState} {ending : Option TState}
    (hg : g < l.threads) (hPos : 0 < j) (hBound : j ≤ (X.tr g).length)
    (ht : At u 4329 [(5127,b32 (3+warp.val))])
    (scores : Nat → Option ℝ) (hScores : ∀ group : Fin 4, firstMaskOutputs u group scores)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hRelease : j = (X.tr g).length → ∃ Y, Maximal l kernel Assumptions.all m Y ∧
      Y.tr = X.tr ∧ Step.Released l Y g) :
    ∃ v, X.get (g,j) = some ⟨statsPc (some .first),.bar (3+warp.val) (some 64) .arrive⟩ ∧
      At v (statsPc (some .first)+1)
        [(3685,finiteRefValue (scoreMax scores (List.range 128))),
          (7256,scoreValue (scoreMax scores (List.range 128))),(5127,b32 (3+warp.val))] ∧
      (∀ group : Fin 4, firstMaskOutputs v group scores) ∧
      (∀ r ∉ rWrites (firstMaxItems.map MaxItem.item) ++ [3685,622], v.regs r = u.regs r) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) ending := by
  obtain ⟨s,hs,hMaxLocal,hMasked,hFrame⟩ := firstMaskedMaxLocal scores (ht.mono trivial) hScores
  obtain ⟨v,hv,hRefLocal,hRefFrame⟩ :=
    finiteReferenceLocal (g := g) .first _ (hs.mono trivial) hs.2.2.2.2.1
  have hBar : v.regs 5127 = some (b32 (3+warp.val)) :=
    (hRefFrame _ (by decide)).trans ((hFrame _ (by decide +kernel)).trans ht.2.2.2.2.1)
  have hAt : At v (statsPc (some .first)) [(5127,b32 (3+warp.val))] := hv.mono ⟨hBar,trivial⟩
  obtain ⟨he,hPrefix,hSuffix⟩ := statsArrivalOfMaximal hp (some .first) warp
    hg hPos hBound hAt hPast ((hLocal.trans hMaxLocal).trans hRefLocal) hRun hRelease
  refine ⟨next v,he,hv.next.mono ⟨hv.2.2.2.2.1,hv.2.2.2.2.2.1,hBar,trivial⟩,
    ?_,?_,hPrefix,hSuffix⟩
  · intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo,hHi⟩ := hMasked group pair hPair
    have hNotLo : (firstMaskPairRegs group pair).low ∉ [3685,622] := by
      simp only [firstMaskPairRegs,maskScratch,List.mem_cons,List.not_mem_nil,or_false,not_or]
      omega
    have hNotHi : (firstMaskPairRegs group pair).high ∉ [3685,622] := by
      simp only [firstMaskPairRegs,maskScratch,List.mem_cons,List.not_mem_nil,or_false,not_or]
      split <;> omega
    exact ⟨(hRefFrame _ hNotLo).trans hLo,(hRefFrame _ hNotHi).trans hHi⟩
  · intro r hr
    exact (hRefFrame r (fun h => hr (List.mem_append_right _ h))).trans
      (hFrame r (fun h => hr (List.mem_append_left _ h)))

/-- Initial statistics publication with the frame for the first P computation. -/
structure OpeningStatisticsCursor (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  index : Nat
  state : TState
  ending : Option TState
  scores : Nat → Option ℝ
  published : Thread.Scores.Publishes X (g,index) .first
  tensorCount : ((X.tr g).take (index+1)).countP isTcColl = 4
  ready : At state (statsPc (some .first)+1)
    [(3685,finiteRefValue (scoreMax scores (List.range 128))),(7132,b32 p.scaleLog2Bits)]
  masked : ∀ group : Fin 4, firstMaskOutputs state group scores
  shared : state.regs 3217 = some (b32 (l.sharedBase+8*stage.val))
  addresses : ∀ q : Fin 4, state.regs (probabilityReg .first q) =
    some (b32 (probabilityAddress l g stage q))
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some state)
  continuation : Run kernel Assumptions.all l g state ((X.tr g).drop (index+1)) ending

/-- The post-Bias FMA operands and a released cursor lead to an actual first statistics event. -/
theorem OpeningBiasArrivalLane.statisticsWithScoresAndRegistersOfMaximal {p : Params} {l :
  Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch wait : Nat} {stage : Fin 2} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (arrival : OpeningBiasArrivalLane p l X g batch stage wait)
    (hRelease : wait+67 < (X.tr g).length ∨
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g) :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    ∃ c : OpeningStatisticsCursor p l X g stage,
      Holds c.state.regs (firstLoopGeometry blocks cap past) ∧
      c.state.regs 7256 = some (scoreValue (scoreMax c.scores (List.range 128))) ∧
      (row < p.qLength batch → ∀ col : Fin 128,
        c.scores col.val = maskedLogit p batch coords.2 row (visitKey blocks 0 col.val)) ∧
      Holds c.state.regs [(1062,b32 (Prologue.warpIndex l g)),(2535,b32 l.sharedBase),
        (5127,b32 (3+Prologue.warpIndex l g))] := by
  obtain ⟨fma⟩ := arrival.firstFmaOfMaximal hp hg hRelease
  obtain ⟨lane⟩ := fma.affineOfPrefix hp hMax.1 hFrame hb hLo hHi
  let entry := lane.entry
  let warp := entry.arrival.loaded.opening.warp
  let tile := Epilogue.assignedCoordinates p batch (g/l.block) |>.1
  let blocks := Mma.trips p batch tile
  let base := 2*tile+stage.val
  let raw := firstBiasLogit (abiFloat p.invScaleBits)
    (firstBiasRegisterValue (openingBiasColumns p l g batch stage)) (firstQkRegisterValue lane.dot)
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  obtain ⟨u,hu,hAddresses,hRaw,hScale,hBar,hReach,hCarry⟩ := lane.maskCursorWithFrame hp
  have hStage : stageOf warp = stage := entry.arrival.loaded.opening.selectedStage
  have hFields {x : Nat × Value}
      (hm : x ∈ openingScoreReturnedFacts p l g batch tile warp) :
      entry.arrival.loaded.cursor.ready.regs x.1 = some x.2 :=
    holds_mem entry.arrival.loaded.cursor.checkpoint.2.2.2.2 hm
  have hPast : past+256 = p.kLength batch-p.qLength batch+256*(tile+1) := by
    dsimp [past]
    omega
  have hLoop : Holds u.regs (firstLoopGeometry blocks cap past) := by
    refine ⟨?_,?_,?_,hu.2.2.2.2.1,trivial⟩
    · exact (hCarry _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1225,b32 (past+256))) (by
          simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,hPast]))
    · exact (hCarry _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1226,b32 blocks)) (by
          simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,blocks]))
    · exact (hCarry _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1228,b32 cap)) (by
          simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,cap,blocks,
            hStage]))
  have hTile := (Epilogue.assignedCoordinates_valid hp hLo hHi).1
  have hBlock := (Mma.trips_bounds hp hb hTile).2.1
  have hBlocks : 128*(blocks-1) ≤ p.kLength batch := by
    change blocks ≤ (p.kLength batch+127)/128 at hBlock
    omega
  have hTid : g%l.block < 2^32 := by
    rw [hp.block]
    have := Nat.mod_lt g (by decide : 0 < 512)
    omega
  have hRow : 128*base+(g%l.block)%128 < p.qLength batch+256 := by
    have hStage := stage.isLt
    have hLane := Nat.mod_lt (g%l.block) (by decide : 0 < 128)
    dsimp only [base]
    omega
  obtain ⟨v,hv,hMask,hScores,hKeep⟩ := firstCausalMaskLocal (g := g)
    p batch (g%l.block) base blocks raw hTid (hp.lengths batch hb).2.1 (hp.lengths batch hb).2.2
    hRow hBlocks hu hRaw
  have hKeepControl (r : Nat) (hr : r ∈ [1062,2535,5127,7132,3217,3223,3224,3225,3226,1225,1226,
    1228,1229]) :
      v.regs r = u.regs r := by
    have hSetup : List.all [1062,2535,5127,7132,3217,3223,3224,3225,3226,1225,1226,1228,1229]
        (fun reg => !firstMaskSetupWrites.contains reg) = true := by decide +kernel
    refine hKeep r (by simpa using List.all_eq_true.mp hSetup r hr) (fun group => ?_)
    have hGroup := group.isLt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    unfold firstMaskGroupWrites maskScratch maskPred
    omega
  have hvBar : v.regs 5127 = some (b32 (3+warp.val)) :=
    (hKeepControl 5127 (by simp)).trans hBar
  have hPos : 0 < entry.pos := by rw [entry.position]; split <;> omega
  have hBound : entry.pos ≤ (X.tr g).length := by
    rw [entry.position]
    split
    · rename_i hLeader
      exact len_of_get (entry.releasedBias hLeader)
    · exact len_of_get entry.arrival.arrival
  have hReturn (hEnd : entry.pos = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
    by_cases hLeader : laneOf l g = 0
    · have hLength : wait+67+1 = (X.tr g).length := by
        simpa only [entry.position,ite_eq_left hLeader] using hEnd
      exact ⟨X,hMax,rfl,Prologue.releasedIfLast (entry.releasedBias hLeader)
        (by intro h; cases h) hLength⟩
    · rw [entry.position,ite_eq_right hLeader] at hEnd
      rcases hRelease with hBefore | hReady
      · omega
      · exact hReady
  obtain ⟨after,he,hAfter,hMasked,hFrameAfter,hPast,hSuffix⟩ :=
    openingStatisticsFromMask hp warp hg hPos hBound
      (hv.mono ⟨hvBar,trivial⟩) _ hScores entry.recorded (hReach.trans hMask)
      entry.continuation hReturn
  have hControl (r : Nat) (hr : r ∈ [1062,2535,5127,7132,3217,3223,3224,3225,3226,1225,1226,1228,
    1229]) :
      after.regs r = u.regs r := by
    have hAudit : List.all [1062,2535,5127,7132,3217,3223,3224,3225,3226,1225,1226,1228,1229]
      (fun reg =>
        !((rWrites (firstMaxItems.map MaxItem.item)) ++ [3685,622]).contains reg) =
        true := by decide +kernel
    exact (hFrameAfter r (by simpa using List.all_eq_true.mp hAudit r hr)).trans (hKeepControl r hr)
  have hCount : ((X.tr g).take (entry.pos+1)).countP isTcColl = 4 :=
    (countP_take_succ_false he (p := isTcColl) rfl).trans entry.tensorCount
  refine ⟨⟨entry.pos,after,_,_,⟨_,he,rfl⟩,hCount,
    hAfter.mono ⟨hAfter.2.2.2.2.1,(hControl 7132 (by simp)).trans hScale,trivial⟩,
    hMasked,?_,?_,hPast,hSuffix⟩,?_,hAfter.2.2.2.2.2.1,?_,?_⟩
  · exact (hControl 3217 (by simp)).trans
      (holds_mem hAddresses (by simp [firstAddressFacts]))
  · intro q
    have hReg : probabilityReg .first q ∈
        [1062,2535,5127,7132,3217,3223,3224,3225,3226,1225,1226,1228,1229] :=
      by
      fin_cases q <;> decide
    exact (hControl _ hReg).trans
      (holds_mem hAddresses (by fin_cases q <;> simp [firstAddressFacts,probabilityReg]))
  · change Holds after.regs (firstLoopGeometry blocks cap past)
    obtain ⟨h1,h2,h3,h4,_⟩ := hLoop
    exact ⟨(hControl 1225 (by simp)).trans h1,(hControl 1226 (by simp)).trans h2,
      (hControl 1228 (by simp)).trans h3,(hControl 1229 (by simp)).trans h4,trivial⟩
  · intro hRow col
    exact lane.maskedLogitOfLaunch hp hMax.1 hFrame hb hLo hHi col hRow
  · have hId := actualSoftmaxStatsBarrierId hp hMax.1
      (show statsPc (some .first) ∈ softmaxStatsSites by decide) he
    have hWarp : warp.val = Prologue.warpIndex l g := by omega
    have hSetup : Holds u.regs (tailFrame l warp) := by
      refine ⟨?_,?_,trivial⟩
      · exact (hCarry 1062 (by decide) (by decide +kernel) (by decide)).trans
          (hFields (x := (1062,b32 warp.val)) (by simp [openingScoreReturnedFacts,
            singleVisitGeometryCarry,biasFenceFacts,biasKeep]))
      · exact (hCarry 2535 (by decide) (by decide +kernel) (by decide)).trans
          (hFields (x := (2535,b32 l.sharedBase)) (by simp [openingScoreReturnedFacts,
            singleVisitGeometryCarry,biasFenceFacts,biasKeep]))
    rw [← hWarp]
    exact ⟨(hControl 1062 (by decide)).trans hSetup.1,
      (hControl 2535 (by decide)).trans hSetup.2.1,hAfter.2.2.2.2.2.2.1,trivial⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch wait : Nat} {stage : Fin 2} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (arrival : OpeningBiasArrivalLane p l X g batch stage wait)
    (hRelease : wait+67 < (X.tr g).length ∨
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g)
include hp hMax hFrame hg hb hLo hHi arrival hRelease

theorem OpeningBiasArrivalLane.statisticsWithScoresOfMaximal :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    ∃ c : OpeningStatisticsCursor p l X g stage,
      Holds c.state.regs (firstLoopGeometry blocks cap past) ∧
      c.state.regs 7256 = some (scoreValue (scoreMax c.scores (List.range 128))) ∧
      (row < p.qLength batch → ∀ col : Fin 128,
        c.scores col.val = maskedLogit p batch coords.2 row (visitKey blocks 0 col.val)) := by
  obtain ⟨c,hGeometry,hMaximum,hLogits,_⟩ :=
    arrival.statisticsWithScoresAndRegistersOfMaximal hp hMax hFrame hg hb hLo hHi hRelease
  exact ⟨c,hGeometry,hMaximum,hLogits⟩

theorem OpeningBiasArrivalLane.statisticsOfMaximal :
    Nonempty (OpeningStatisticsCursor p l X g stage) := by
  obtain ⟨c,_,_,_⟩ := arrival.statisticsWithScoresOfMaximal hp hMax hFrame hg hb hLo hHi hRelease
  exact ⟨c⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
