-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainLoadLogits
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainRound
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainPublicationOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Numeric PTX.Assumption PTX.TcMma
open Prologue Epilogue Thread Thread.Scores

noncomputable section

/-- The persistent inputs of the ordinary repeated loop. Its tensor addresses and
lane-selection words are computed anew by its decoded entry sequence. -/
def plainIterationInputs (p : Params) (warp : Fin 8) (old : Option ℝ) (mass : ℝ)
    (phase : Bool) (word : Nat) : List (Nat × Value) :=
  [(7255,scoreValue old),(7257,fl mass),(7258,b32 phase.toNat),(5127,b32 (3+warp.val)),
    (1230,fl (-abiFloat p.scaleLog2Bits)),(7133,b32 p.scaleLog2Bits),
    (8692,joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)),(7254,b32 word)]

private def plainSavedRegisters : List Nat :=
  [1062,2535,7253,7255,7257,7258,5127,1230,7133,8692,7254,
    5187,5176,5177,5183,5185,5181,5184]

private def plainScoreKeeps (q : Fin 4) (n : Nat) : Bool :=
  decide (n < repeatedScoreWordBase .unbiased q ∨
    repeatedScoreWordBase .unbiased q+32 ≤ n) &&
  (List.finRange 16).all (fun k => n != repeatedScorePairReg .unbiased q k.val)

private theorem plainScoreKeepProof (q : Fin 4) {n : Nat} (hn : n ∈ plainSavedRegisters) :
    (n < repeatedScoreWordBase .unbiased q ∨ repeatedScoreWordBase .unbiased q+32 ≤ n) ∧
    ∀ k : Fin 16, n ≠ repeatedScorePairReg .unbiased q k.val := by
  have hAudit : plainSavedRegisters.all (plainScoreKeeps q) = true := by
    fin_cases q <;> decide +kernel
  have h := List.all_eq_true.mp hAudit n hn
  simp only [plainScoreKeeps,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1,fun k => by
    simpa only [bne_iff_ne] using List.all_eq_true.mp h.2 k (List.mem_finRange _)⟩

private theorem plainScaleAt {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (hScale : t.regs 8692 = some (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits))) :
    readERealPair l g t (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))) := by
  let word := b32 p.scaleLog2Bits
  have hb : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits)
    (by simp [Params.scalarWords])).1
  obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
  have hVal : valFloat .f32 word = .ok (abiFloat p.scaleLog2Bits) := by
    simpa only [word,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  have hSplit : splitValue 64 (joinValue word word) = (word,word) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hb)
  exact readERealPair_reg hScale (by rw [hSplit]; exact hVal) (by rw [hSplit]; exact hVal)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) (warp : Fin 8) {g j last pc batch : Nat} {t : TState}
    (hWarp : warp.val = warpIndex l g) (old : Option ℝ) (oldMass : ℝ) (phase scorePhase : Bool)
    (word : Nat) (hWord : word < 2^32)
    (ht : At t 6661 ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::
      (7253,b32 scorePhase.toNat)::plainIterationInputs p warp old oldMass phase word))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hX hFrame hCuQ warp hWarp old oldMass phase scorePhase word hWord ht hRun hExit hb hLo

/-- One actual plain round starts at its loop head, reads the matching launch logits,
publishes its FP32 correction and BF16 probabilities, and produces the next live state. -/
theorem plainRoundFromHeadOfFootprintWithPath (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let tile := (assignedCoordinates p batch (g/l.block)).1
      256*tile+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch) :
    ∃ failed candidate u endPos barInst,
      let loadPos := j+failed+1
      let storePos := loadPos+8
      let stage := stageOf warp
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let trips := Mma.trips p batch co.1
      let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,loadPos)
      let scale := abiFloat p.scaleLog2Bits
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      let weights := fun col =>
        shiftedWeight p batch co.2 row (visitKey trips visit col) (ref.getD 0)
      let events := Repeated.probabilityEvents .unbiased l g stage weights
      let mass := oldMass*maskedRescale (old.map (scale * ·)) ref +
        (2 : ℝ)^(-ref.getD 0)*maskedBlockSum (p.keyCount batch row) trips visit
          (weight p batch co.2 row)
      visit = probabilityOrdinal l X (g/l.block) stage 0 (g,j) ∧
      (∀ v : EReal, scoreReal candidate ≤ v ↔ scoreReal old ≤ v ∧
        ∀ i < 128, scoreReal (maskedLogit p batch co.2 row (visitKey trips visit i)) ≤ v) ∧
      X.get (g,storePos) = some ⟨6890,.wr (statsAcc l g warp 1)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,storePos+1) = some ⟨6891,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      (∀ k : Fin events.length, X.get (g,storePos+2+k.val) = events[k.val]?) ∧
      X.get (g,storePos+2+events.length+1) =
        some ⟨probabilityWaitPc .unbiased true+1,.warpBar (2^32-1) barInst⟩ ∧
      X.get (g,loadPos+14) = some ⟨(signalSite Repeated.unbiased.earlySignal).pc,
        .arrive (signalLoc l g stage Repeated.unbiased.earlySignal) 0 1 true .cta⟩ ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,loadPos+14) = visit ∧
      (∀ q : Fin 4, okPolls (scoreReadyObject l (g/l.block) stage)
        ((X.tr g).take (storePos+2+Repeated.unbiased.probabilityStoreOffset q)) = visit+1) ∧
      storePos+2+events.length < endPos ∧
      let site := scoreLoopSite .plain
      let nextWord := (word+1)%2^32
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg .plain,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
          tailPhaseWords true (!scorePhase) .plain) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      ((X.tr g).take endPos).countP earlyProbabilityMark =
        ((X.tr g).take (j+failed+1+8)).countP earlyProbabilityMark + 1 ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,storePos) = visit := by
  let facts := (1062,b32 warp.val)::(2535,b32 l.sharedBase)::
    plainIterationInputs p warp old oldMass phase word
  have hStart : At t 6661 ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::
      (7253,b32 scorePhase.toNat)::facts) := ht.mono
    ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2⟩
  have hSource : ∀ x ∈ facts, x.1 ∉ unbiasedSetupWrites := by
    intro x hx
    simp only [facts,plainIterationInputs,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only <;> decide +kernel
  have hFresh : ∀ x ∈ facts, x.1 ≠ 9821 := by
    intro x hx
    simp only [facts,plainIterationInputs,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only <;> decide
  have hPhaseRange : scorePhase.toNat < 2 := by cases scorePhase <;> decide
  obtain ⟨s,failed,hPollTrace,hs,hAddrs,hTail,hPollPath⟩ :=
    plainScorePathFromHead hp warp hPhaseRange facts hSource hFresh hStart hRun
  obtain ⟨a,ha,hNext,hWaits,hLoads,hFrameA,hLoadPath,hPacked⟩ :=
    plainPackedLogitsFromLoadsOfFootprint
    hp hX hFrame hCuQ warp hWarp (hs.mono trivial) hAddrs hTail hExit
      hb hLo hHi hRow
  have hCarry (n : Nat) (hn : n ∈ plainSavedRegisters) :
      a.regs n = s.regs n := hFrameA n (fun q => plainScoreKeepProof q hn)
  let stage := stageOf warp
  have hHeld : Holds s.regs (plainReadySetup l g warp ++ facts) := hs.2.2.2.2.2.2.2
  obtain ⟨hSetup,hInputs⟩ := (holds_append ..).mp hHeld
  have hFacts : Holds s.regs (unbiasedAddressRows l g warp) ∧
      Holds s.regs (unbiasedProbabilityFacts l g stage ++ roundScoreFacts l g stage .unbiased) :=
    (holds_append s.regs (unbiasedAddressRows l g warp) _).mp hSetup
  obtain ⟨hWarpS,hBaseS,hOld,hMass,hPhase,hBar,hNeg,hAbi,hScaleReg,hWordReg,_⟩ := hInputs
  have hPrior : Holds a.regs
      [(7255,scoreValue old),(7257,fl oldMass),(7258,b32 phase.toNat),
        (1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
        (5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
        (1230,fl (-abiFloat p.scaleLog2Bits)),(7133,b32 p.scaleLog2Bits),
        (5187,b32 (l.sharedBase+8*(stageOf warp).val))] :=
    ⟨(hCarry _ (by decide)).trans hOld,(hCarry _ (by decide)).trans hMass,
      (hCarry _ (by decide)).trans hPhase,(hCarry _ (by decide)).trans hWarpS,
      (hCarry _ (by decide)).trans hBaseS,(hCarry _ (by decide)).trans hBar,
      (hCarry _ (by decide)).trans hFacts.1.2.2.1,(hCarry _ (by decide)).trans hFacts.1.2.1,
      (hCarry _ (by decide)).trans hNeg,(hCarry _ (by decide)).trans hAbi,
      (hCarry _ (by decide)).trans hs.2.2.2.2.2.1,trivial⟩
  have hPaired := plainScaleAt (g := g) hp ((hCarry _ (by decide)).trans hScaleReg)
  have hP (q : Fin 4) : a.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g stage q)) := by
    have hMem : (probabilityReg .unbiased q,b32 (probabilityAddress l g stage q)) ∈
        unbiasedProbabilityFacts l g stage := by
      fin_cases q <;> simp [unbiasedProbabilityFacts,probabilityReg]
    have hProb := ((holds_append s.regs (unbiasedProbabilityFacts l g stage) _).mp hFacts.2).1
    exact (hCarry _ (by fin_cases q <;> decide)).trans (holds_mem hProb hMem)
  have hControl : Holds a.regs [(7253,b32 scorePhase.toNat),(7254,b32 word)] :=
    ⟨(hCarry _ (by decide)).trans hs.2.2.2.2.2.2.1,(hCarry _ (by decide)).trans hWordReg,
      trivial⟩
  have hResult := plainRoundFromLogitsWithPath hp warp hWarp old oldMass phase scorePhase
    ha hPacked hPrior hPaired hP word hWord hControl hNext
  obtain ⟨candidate,u,endPos,barInst,hCandidate,hStore,hNotice,hEvents,hBarTail,hBound,hU,hEnd,
    hNumeric,hEarly⟩ :=
    hResult
  have hCredit := Repeated.probabilityCreditOfRound .unbiased (stageOf warp) hEvents
  let loadPos := j+failed+1
  let co := assignedCoordinates p batch (g/l.block)
  let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,loadPos)
  let weights := fun col => shiftedWeight p batch co.2
    (256*co.1+128*stage.val+(g%l.block)%128)
    (visitKey (Mma.trips p batch co.1) visit col)
    (((chosenReference (abiFloat p.scaleLog2Bits) old candidate).map
      (abiFloat p.scaleLog2Bits * ·)).getD 0)
  have hProbability : ∀ k : Fin (Repeated.probabilityEvents .unbiased l g stage weights).length,
      X.get (g,loadPos+10+k.val) =
        (Repeated.probabilityEvents .unbiased l g stage weights)[k.val]? := by
    intro k
    exact hEvents k
  obtain ⟨hOrdinal,hPolls,hStatisticsCount⟩ :=
    plainPublicationCountsWithStatistics stage weights hLoads hWaits hStore
    hNotice hProbability
  obtain ⟨inputs,hFirst⟩ := hLoads 0
  have hFirstLoad : X.get (g,loadPos) =
      some ⟨scorePc .unbiased 0,.tc (.ld (scoreAddress l g stage 0) inputs .s32x32b)⟩ :=
    hFirst
  have hStage : warpIndex l g/4 = stage.val := by rw [← hWarp]; rfl
  have hScoreCount := scoreLoadExactCursor hp hX stage (hWarp ▸ warp.isLt) hStage
    .unbiased 0 hFirstLoad
  have hVisit : visit = probabilityOrdinal l X (g/l.block) stage 0 (g,j) := by
    let object := probabilityObject l (g/l.block) stage 0
    have hTake : (X.tr g).take loadPos =
        (X.tr g).take j ++ ((X.tr g).drop j).take (failed+1) := by
      rw [show loadPos = j+(failed+1) from Nat.add_assoc ..,List.take_add]
    change arrivals object ((X.tr g).take loadPos) = arrivals object ((X.tr g).take j)
    rw [hTake,arrivals,List.countP_append,hPollTrace]
    rw [← List.singleton_append,← List.append_assoc,List.take_append_of_le_length (by simp)]
    simp [arrivals,arrivesOn]
    intro e he
    have hMember := List.mem_of_mem_take he
    simp only [List.mem_append,List.mem_replicate,List.mem_singleton] at hMember
    rcases hMember with ⟨_,rfl⟩ | rfl <;> rfl
  refine ⟨failed,candidate,u,endPos,barInst,hVisit,hCandidate,hStore,hNotice,hEvents,hBarTail,
    ?_,hOrdinal,(fun q => (hPolls q).trans hScoreCount),hBound,hU,hEnd,?_,?_,hStatisticsCount⟩
  · exact hCredit
  · have hPrefix := hPollPath.append hLoadPath
    have hEq : j+failed+1 = j+(failed+1) := by omega
    rw [hEq,← List.drop_drop,← List.take_add] at hPrefix
    have hMid : j+failed+1+8 = j+(failed+1+8) := by omega
    rw [hMid,← List.drop_drop] at hNumeric
    have hPath := hPrefix.append hNumeric
    rw [← List.take_add,show failed+1+8+(endPos-(j+(failed+1+8))) = endPos-j by omega] at hPath
    exact hPath
  · exact hEarly

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X)
include hp hX hFrame hCuQ

end
end PTX.Kernels.TmlFa4Fwd.Softmax
