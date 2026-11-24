-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityPrepare
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityMainCredit
import all Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityPrepare
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedExponent
import Lemmas.Step.WarpLanes
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

private theorem PackedRoundContinuation.issue
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {mode : Repeated} {stage : Fin 2} {weights : Nat → ℝ}
    {q : Fin 4} (pack : PackedRoundContinuation l X g mode stage weights q)
    (hWaitPeers : delayedProbability mode.round q = true →
      pack.cursor.pos+1 = (X.tr g).length →
      ∀ peer ∈ warpLanes l g, ∃ k, X.TcK (peer,k)
        (((X.tr g).take pack.cursor.pos).countP isTcColl)) :
    let pos := if delayedProbability mode.round q then pack.cursor.pos+1 else pack.cursor.pos
    (delayedProbability mode.round q = true →
      X.get (g,pack.cursor.pos) = some ⟨probabilityPc mode.round q,.tc .waitLd⟩) ∧
    X.get (g,pos) = some (repeatedStoreEvent l g stage mode.round q weights) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next pack.cursor.ready)) ∧
    Run kernel Assumptions.all l g (next pack.cursor.ready) ((X.tr g).drop (pos+1))
      pack.cursor.ending := by
  cases mode with
  | biased =>
    obtain ⟨hLen,hWords,hAddr⟩ :=
      biasedStoreWords stage pack.mixed q pack.holds pack.table (pack.addresses q)
    exact repeatedProbabilityIssueOfMaximal hp hMax hg .biased stage q pack.cursor _
      weights hLen (biasedStoreCode q) hWords hAddr hWaitPeers
  | unbiased =>
    obtain ⟨hLen,hWords,hAddr⟩ :=
      unbiasedStoreWords stage q pack.holds pack.table (pack.addresses q)
    exact repeatedProbabilityIssueOfMaximal hp hMax hg .unbiased stage q pack.cursor _
      weights hLen (unbiasedStoreCode q) hWords hAddr hWaitPeers

private def storeContinuationPc (mode : Repeated) (q : Fin 3) : Nat :=
  match mode with
  | .biased => biasedStoreRunStart q
  | .unbiased => unbiasedStoreRunStart q

private def storeContinuationTable (mode : Repeated) (q : Fin 3)
    (regs : ExponentRegs) : ExponentRegs :=
  if q.val = 2 then
    match mode with
    | .biased => biasedClearSignal regs
    | .unbiased => unbiasedClearSignal regs
  else regs

section
variable {l : Launch} {X : Execution} {g : Nat} {mode : Repeated}

private theorem PackedRoundContinuation.advance {stage : Fin 2} {weights : Nat → ℝ} (q : Fin 3)
    (pack : PackedRoundContinuation l X g mode stage weights (Fin.castSucc q))
    (c : OpeningTripCursor l X g (storeContinuationPc mode q) [])
    (hSource : ExponentHolds pack.arguments weights
      (storeContinuationTable mode q pack.registerTable) c.ready) :
    ∃ s : PackedRoundContinuation l X g mode stage weights q.succ,
      s.cursor.pos = c.pos ∧ s.cursor.ending = c.ending ∧ s.origin = pack.origin := by
  cases mode with
  | biased =>
    let start := biasedStoreRunStart q
    let regs := pack.registerTable
    have hCheck := biasedAllStoreChecks pack.mixed q.succ
    cases hOut : biasedStoreInputs pack.mixed q.succ with
    | none => rw [hOut,Option.any_none] at hCheck; cases hCheck
    | some outRegs =>
      have hRun : nextBiasedRegs q regs = some outRegs := by
        have hTable : biasedStoreInputs pack.mixed q.castSucc = some regs := pack.table
        rw [biasedStoreInputs_succ,hTable,Option.bind_some] at hOut
        exact hOut
      obtain ⟨u,hu,hU,hRegs⟩ := exponentRun_sound (l := l) (g := g) pack.eval
        biasedCode biasedCode_sound 8 _ _ _ _ hRun c.checkpoint hSource
      have hPub := (observedBiasedRegs pack.mixed _ hOut hRegs).2
      have hBefore := (observedBiasedRegs pack.mixed _ pack.table pack.holds).2
      have hPublication : Holds u.regs (firstPublicationFacts l stage .biased) :=
        ⟨(hPub _ (by decide)).trans ((hBefore _ (by decide)).symm.trans pack.publication.1),
          (hPub _ (by decide)).trans ((hBefore _ (by decide)).symm.trans pack.publication.2.1),
          trivial⟩
      exact ⟨⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hU,
        c.recorded,c.remaining,c.localSteps.trans hu⟩,pack.arguments,outRegs,pack.mixed,
        pack.eval,hRegs,hOut,pack.addresses,
        hPublication,pack.origin,pack.originalFrame,pack.continuationFrame⟩,rfl,rfl,rfl⟩
  | unbiased =>
    let start := unbiasedStoreRunStart q
    let regs := pack.registerTable
    have hCheck := unbiasedAllStoreChecks q.succ
    cases hOut : unbiasedStoreInputs q.succ with
    | none => rw [hOut,Option.any_none] at hCheck; cases hCheck
    | some outRegs =>
      have hRun : nextUnbiasedRegs q regs = some outRegs := by
        have hTable : unbiasedStoreInputs q.castSucc = some regs := pack.table
        rw [unbiasedStoreInputs_succ,hTable,Option.bind_some] at hOut
        exact hOut
      obtain ⟨u,hu,hU,hRegs⟩ := exponentRun_sound (l := l) (g := g) pack.eval
        unbiasedCode unbiasedCode_sound 8 _ _ _ _ hRun c.checkpoint hSource
      have hPub := (observedUnbiasedRegs _ hOut hRegs).2
      have hBefore := (observedUnbiasedRegs _ pack.table pack.holds).2
      have hPublication : Holds u.regs (firstPublicationFacts l stage .unbiased) :=
        ⟨(hPub _ (by decide)).trans ((hBefore _ (by decide)).symm.trans pack.publication.1),
          trivial⟩
      exact ⟨⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hU,
        c.recorded,c.remaining,c.localSteps.trans hu⟩,pack.arguments,outRegs,pack.mixed,
        pack.eval,hRegs,hOut,pack.addresses,
        hPublication,pack.origin,pack.originalFrame,pack.continuationFrame⟩,rfl,rfl,rfl⟩

private theorem PackedRoundContinuation.nextMain {stage : Fin 2} {weights : Nat → ℝ} (q : Fin 3)
    (hq : q.val < 2) (pack : PackedRoundContinuation l X g mode stage weights (Fin.castSucc q))
    {j : Nat} (hPos : 0 < j) (hBound : j ≤ (X.tr g).length)
    (hRelease : j = (X.tr g).length → Step.Released l X g)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some (next pack.cursor.ready)))
    (hTail : Run kernel Assumptions.all l g (next pack.cursor.ready) ((X.tr g).drop j)
      pack.cursor.ending) :
    ∃ s : PackedRoundContinuation l X g mode stage weights q.succ,
      s.cursor.pos = j ∧ s.cursor.ending = pack.cursor.ending ∧ s.origin = pack.origin := by
  have hPc : probabilityPc mode.round (Fin.castSucc q)+1 = storeContinuationPc mode q := by
    cases mode <;> fin_cases q <;> first | rfl | contradiction
  let c : OpeningTripCursor l X g (storeContinuationPc mode q) [] :=
    ⟨j,next pack.cursor.ready,next pack.cursor.ready,pack.cursor.ending,
      hPos,hBound,hRelease,hPc ▸ pack.cursor.checkpoint.next,hPast,hTail,.refl⟩
  apply pack.advance q c
  unfold storeContinuationTable
  rw [ite_eq_right (show q.val ≠ 2 by omega)]
  exact pack.holds

private theorem PackedRoundContinuation.afterCredit {stage : Fin 2} {weights : Nat → ℝ}
    (pack : PackedRoundContinuation l X g mode stage weights 2)
    (c : OpeningTripCursor l X g ((signalSite (firstPublication mode.round)).pc+1) [])
    (hKeeps : ∀ r ∉ mainProbabilityCreditWrites mode.round,
      c.ready.regs r = pack.cursor.ready.regs r) :
    ∃ tail : PackedRoundContinuation l X g mode stage weights 3,
      tail.cursor.pos = c.pos ∧ tail.cursor.ending = c.ending ∧ tail.origin = pack.origin := by
  cases mode with
  | biased =>
    apply pack.advance (2 : Fin 3) c
    intro r value hr
    change (if r ∈ biasedSignalWrites then none else pack.registerTable r) = some value at hr
    split at hr
    · cases hr
    · rename_i hReg
      exact (hKeeps r hReg).trans (pack.holds r value hr)
  | unbiased =>
    apply pack.advance (2 : Fin 3) c
    intro r value hr
    change (Function.update (Function.update pack.registerTable 5781 none) 8850 none) r =
      some value at hr
    have hOne : r ≠ 5781 := by
      intro h
      subst r
      simp at hr
    have hTwo : r ≠ 8850 := by
      intro h
      subst r
      simp at hr
    have hn : r ∉ mainProbabilityCreditWrites .unbiased := by
      simpa only [mainProbabilityCreditWrites,List.mem_cons,List.not_mem_nil,or_false,not_or]
        using And.intro hTwo hOne
    simp only [Function.update_of_ne hOne,Function.update_of_ne hTwo] at hr
    exact (hKeeps r hn).trans (pack.holds r value hr)
end

private theorem warpIssueMainQuarter
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {lead : Nat}
    {mode : Repeated} {stage : Fin 2} (ordinal : Nat) (q : Fin 4)
    (weights : Nat → Nat → ℝ)
    (input : ∀ g, SameWarp l lead g → PackedRoundContinuation l X g mode stage (weights g) q)
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).cursor.pos).countP isTcColl = ordinal) :
    ∀ g (hw : SameWarp l lead g),
      let v := input g hw
      let delay := if delayedProbability mode.round q then 1 else 0
      let pos := v.cursor.pos+delay
      let pc := probabilityPc mode.round q+1
      ∃ c : OpeningTripCursor l X g pc [],
        X.get (g,pos) = some (repeatedStoreEvent l g stage mode.round q (weights g)) ∧
        c.pos = pos+1 ∧ c.before = next v.cursor.ready ∧ c.ready = c.before ∧
        c.ending = v.cursor.ending ∧
        ((X.tr g).take c.pos).countP isTcColl = ordinal+delay+1 := by
  let delay := if delayedProbability mode.round q then 1 else 0
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have pending (g : Nat) (hw : SameWarp l lead g)
      (hDelay : delayedProbability mode.round q = true) :
      X.get (g,(input g hw).cursor.pos) = some ⟨probabilityPc mode.round q,.tc .waitLd⟩ := by
    cases mode
    · exact (repeatedProbabilityLoadWaitOfMaximal hp hMax hw.1.2.1 .biased q
        (input g hw).cursor _ (biasedStoreCode q) hDelay).1
    · exact (repeatedProbabilityLoadWaitOfMaximal hp hMax hw.1.2.1 .unbiased q
        (input g hw).cursor _ (unbiasedStoreCode q) hDelay).1
  have record (g : Nat) (hw : SameWarp l lead g) :
      let c := (input g hw).cursor
      let pos := c.pos+delay
      X.get (g,pos) = some (repeatedStoreEvent l g stage mode.round q (weights g)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next c.ready)) ∧
      Run kernel Assumptions.all l g (next c.ready) ((X.tr g).drop (pos+1)) c.ending ∧
      ((X.tr g).take pos).countP isTcColl = ordinal+delay := by
    let c := (input g hw).cursor
    have hPeers (hDel : delayedProbability mode.round q = true)
        (peer : Nat) (hm : peer ∈ warpLanes l g) :
        ∃ k, X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl) := by
      obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hm
      have hLaneBound := (List.mem_range.mp hLane).trans_le (Nat.min_le_left ..)
      have hSame := (Step.sameWarp_lane hBlock hw.1.2.1 hLaneBound).1
      let hPeer := Step.sameWarp_trans hw hSame
      let w := input (warpLane l g lane) hPeer
      exact ⟨w.cursor.pos,⟨⟨_,pending _ hPeer hDel,rfl⟩,
        (hRank _ hPeer).trans (hRank g hw).symm⟩⟩
    have hIssue := (input g hw).issue hp hMax hw.1.2.1 (fun hDel _ => hPeers hDel)
    have hIndex : (if delayedProbability mode.round q then c.pos+1 else c.pos) =
        c.pos+delay := by unfold delay; split <;> rfl
    change X.get (g,c.pos+delay) = _ ∧ _ ∧ _ ∧
      ((X.tr g).take (c.pos+delay)).countP isTcColl = ordinal+delay
    refine ⟨?_,?_,?_,?_⟩
    · exact hIndex ▸ hIssue.2.1
    · exact hIndex ▸ hIssue.2.2.1
    · exact hIndex ▸ hIssue.2.2.2
    · have hHere : ((X.tr g).take c.pos).countP isTcColl = ordinal := hRank g hw
      unfold delay
      split
      · rename_i hd
        rw [countP_take_succ (p := isTcColl) (pending g hw hd) rfl,hHere]
      · exact hHere
  intro g hw
  let v := input g hw
  let c := v.cursor
  let pos := c.pos+delay
  obtain ⟨he,hPrefix,hSuffix,hOrdinal⟩ := record g hw
  have hReady (peer : Nat) (hm : peer ∈ warpLanes l g) :
      ∃ k, X.TcK (peer,k) (ordinal+delay) := by
    obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hm
    have hLaneBound := (List.mem_range.mp hLane).trans_le (Nat.min_le_left ..)
    have hSame := (Step.sameWarp_lane hBlock hw.1.2.1 hLaneBound).1
    let hPeer := Step.sameWarp_trans hw hSame
    let w := input (warpLane l g lane) hPeer
    obtain ⟨hStore,_,_,hCount⟩ := record (warpLane l g lane) hPeer
    exact ⟨w.cursor.pos+delay,⟨⟨_,hStore,rfl⟩,hCount⟩⟩
  have hRelease (hEnd : pos+1 = (X.tr g).length) : Step.Released l X g :=
    probabilityCollectiveReleased he (.inr (.inr ⟨_,_,_,rfl⟩)) hOrdinal hReady hEnd
  exact ⟨⟨pos+1,next c.ready,next c.ready,c.ending,by omega,len_of_get he,hRelease,
    c.checkpoint.next,hPrefix,hSuffix,.refl⟩,he,rfl,rfl,rfl,rfl,
    (countP_take_succ (p := isTcColl) he rfl).trans (congrArg (·+1) hOrdinal)⟩

private theorem warpNextMainQuarter
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {lead : Nat}
    {mode : Repeated} {stage : Fin 2} (ordinal : Nat) (q : Fin 3) (hq : q.val < 2)
    (weights : Nat → Nat → ℝ)
    (input : ∀ g, SameWarp l lead g →
      PackedRoundContinuation l X g mode stage (weights g) (Fin.castSucc q))
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).cursor.pos).countP isTcColl = ordinal) :
    ∀ g (hw : SameWarp l lead g),
      let current := input g hw
      let delay := if delayedProbability mode.round (Fin.castSucc q) then 1 else 0
      let pos := current.cursor.pos+delay
      ∃ c : PackedRoundContinuation l X g mode stage (weights g) q.succ,
        X.get (g,pos) =
          some (repeatedStoreEvent l g stage mode.round (Fin.castSucc q) (weights g)) ∧
        c.cursor.pos = pos+1 ∧ c.cursor.ending = current.cursor.ending ∧
        ((X.tr g).take c.cursor.pos).countP isTcColl = ordinal+delay+1 ∧
        c.origin = current.origin := by
  intro g hw
  obtain ⟨after,he,hPos,hBefore,_,hEnding,hOrdinal⟩ :=
    warpIssueMainQuarter hp hMax ordinal q.castSucc weights input hRank g hw
  have hRecorded := after.recorded
  have hRemaining := after.remaining
  rw [hBefore] at hRecorded hRemaining
  rw [hEnding] at hRemaining
  have hPositive := after.positive
  have hBound := after.bounded
  have hReleased := after.released
  obtain ⟨next,hNext,hEnd,hOrigin⟩ := (input g hw).nextMain q hq hPositive hBound hReleased
    hRecorded hRemaining
  exact ⟨next,he,hNext.trans hPos,hEnd,hNext.symm ▸ hOrdinal,hOrigin⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {lead : Nat} (mode : Repeated) (stage : Fin 2)
    (ordinal : Nat) (scores : Nat → Nat → Option ℝ) (reference : Nat → ℝ)
    {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g mode.affineStart (F g))
    (hFrame : ∀ g (hw : SameWarp l lead g),
      RepeatedProbabilityShiftFrame p l mode g stage (input g hw).ready (scores g) (reference g))
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP isTcColl = ordinal)
include hp hMax mode stage ordinal scores reference input hFrame hRank

private theorem warpRepeatedMainPacketWithTail :
    ∀ g (hw : SameWarp l lead g),
      let start := (input g hw).pos
      let delay := if mode = .biased then 1 else 0
      let weights := fun i =>
        repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-(reference g)) (scores g i))
      let site := signalSite (firstPublication mode.round)
      ∃ cursor : OpeningTripCursor l X g (site.pc+1) [],
        (∀ q : Fin 3, X.get (g,start+delay+q.val) =
          some (repeatedStoreEvent l g stage mode.round (Fin.castSucc q) weights)) ∧
        Thread.Scores.ProbabilityCredit l X (g,start+delay+4) (g/l.block) stage 0 ∧
        cursor.pos = start+delay+5 ∧ cursor.ending = (input g hw).ending ∧
        ((X.tr g).take cursor.pos).countP isTcColl = ordinal+delay+4 ∧
        ∃ tail : PackedRoundContinuation l X g mode stage weights 3,
          tail.cursor.pos = cursor.pos ∧ tail.cursor.ending = cursor.ending ∧
          tail.origin = (input g hw).ready ∧
          (mode = .biased → X.get (g,start) = some ⟨probabilityPc mode.round 0,.tc .waitLd⟩) ∧
          X.get (g,start+delay+3) = some ⟨probabilityWaitPc mode.round false,.tc .waitSt⟩ := by
  classical
  let delay := if mode = .biased then 1 else 0
  let weights g i :=
    repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-(reference g)) (scores g i))
  have hDelay0 : (if delayedProbability mode.round (Fin.castSucc (0 : Fin 3))
      then 1 else 0 : Nat) = delay := by
    cases mode <;> rfl
  have hDelay1 : (if delayedProbability mode.round (Fin.castSucc (1 : Fin 3))
      then 1 else 0 : Nat) = 0 := by cases mode <;> rfl
  have hDelay2 : (if delayedProbability mode.round 2 then 1 else 0 : Nat) = 0 := by
    cases mode <;> rfl
  have hPrepare (g : Nat) (hw : SameWarp l lead g) :
      ∃ v : PackedRoundContinuation l X g mode stage (weights g) 0,
        v.cursor.pos = (input g hw).pos ∧
        v.cursor.ending = (input g hw).ending ∧
          v.origin = (input g hw).ready := by
    obtain ⟨ready,v,hReady,hPos,hEnd,hOrigin⟩ :=
      prepareWithContinuation hp (input g hw) (hFrame g hw)
    exact ⟨v,(congrArg OpeningTripCursor.pos hReady).symm.trans hPos,
      (congrArg OpeningTripCursor.ending hReady).symm.trans hEnd,hOrigin⟩
  choose q0 q0Pos q0Ending hOrigin0 using hPrepare
  have hRank0 (g : Nat) (hw : SameWarp l lead g) :
      ((X.tr g).take (q0 g hw).cursor.pos).countP isTcColl = ordinal := by
    rw [q0Pos g hw]
    exact hRank g hw
  have hOne := warpNextMainQuarter hp hMax ordinal (0 : Fin 3) (by decide) weights q0 hRank0
  choose q1 hStore0 q1Pos q1Ending hRank1 hOrigin1 using hOne
  have hRank1' (g : Nat) (hw : SameWarp l lead g) :
      ((X.tr g).take (q1 g hw).cursor.pos).countP isTcColl = ordinal+delay+1 := by
    simpa only [hDelay0] using hRank1 g hw
  have hTwo := warpNextMainQuarter hp hMax (ordinal+delay+1) (1 : Fin 3) (by decide)
    weights q1 hRank1'
  choose q2 hStore1 q2Pos q2Ending hRank2 hOrigin2 using hTwo
  have hRank2' (g : Nat) (hw : SameWarp l lead g) :
      ((X.tr g).take (q2 g hw).cursor.pos).countP isTcColl = ordinal+delay+2 := by
    simpa only [hDelay1,Nat.add_zero,Nat.add_assoc] using hRank2 g hw
  have hThree := warpIssueMainQuarter hp hMax (ordinal+delay+2) (2 : Fin 4) weights q2 hRank2'
  choose after hStore2 hAfterPos hBefore hReady hAfterEnd hAfterRank using hThree
  have hWaitPC : probabilityPc mode.round 2+1 = probabilityWaitPc mode.round false := by
    cases mode <;> rfl
  let wait (g : Nat) (hw : SameWarp l lead g) :
      OpeningTripCursor l X g (probabilityWaitPc mode.round false)
        (firstPublicationFacts l stage mode.round) :=
    let c := after g hw
    have hAt : At c.ready (probabilityWaitPc mode.round false) [] := by
      rw [← hWaitPC]
      exact c.checkpoint
    ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,
      hAt.mono (by
        rw [hReady g hw,hBefore g hw]
        exact (q2 g hw).publication),
      c.recorded,c.remaining,c.localSteps⟩
  have hWaitRank (g : Nat) (hw : SameWarp l lead g) :
      ((X.tr g).take (wait g hw).pos).countP isTcColl = ordinal+delay+3 := by
    simpa only [wait,hDelay2,Nat.add_zero,Nat.add_assoc] using hAfterRank g hw
  intro g hw
  obtain ⟨endCursor,hWaitEvent,hCredit,hEndPos,hEndEnding,hEndRank,hKeeps⟩ :=
    warpMainProbabilityCreditOfMaximalKeeping hp hMax mode.round stage (ordinal+delay+3)
      wait hWaitRank g hw
  have hStart0 := q0Pos g hw
  have hStart1 : (q1 g hw).cursor.pos = (input g hw).pos+delay+1 := by
    simpa only [hDelay0,hStart0] using q1Pos g hw
  have hStart2 : (q2 g hw).cursor.pos = (input g hw).pos+delay+2 := by
    simpa only [hDelay1,Nat.add_zero,Nat.add_assoc,hStart1] using q2Pos g hw
  have hWaitPos : (wait g hw).pos = (input g hw).pos+delay+3 := by
    simpa only [wait,hDelay2,Nat.add_zero,Nat.add_assoc,hStart2] using hAfterPos g hw
  have hWaitEnd : (wait g hw).ending = (input g hw).ending :=
    (hAfterEnd g hw).trans
      ((q2Ending g hw).trans ((q1Ending g hw).trans (q0Ending g hw)))

  have hKeepTail (r : Nat) (hr : r ∉ mainProbabilityCreditWrites mode.round) :
      endCursor.ready.regs r = (q2 g hw).cursor.ready.regs r := by
    rw [hKeeps r hr]
    change (after g hw).ready.regs r = _
    rw [hReady g hw,hBefore g hw]
    rfl
  obtain ⟨tail,hTailPos,hTailEnd,hOrigin⟩ := (q2 g hw).afterCredit endCursor hKeepTail
  have hTailOrigin : tail.origin = (input g hw).ready :=
    hOrigin.trans ((hOrigin2 g hw).trans ((hOrigin1 g hw).trans (hOrigin0 g hw)))
  refine ⟨endCursor,?_,?_,?_,hEndEnding.trans hWaitEnd,?_,tail,hTailPos,hTailEnd,hTailOrigin,?_,?_⟩
  · intro q
    change X.get (g,(input g hw).pos+delay+q.val) =
      some (repeatedStoreEvent l g stage mode.round q.castSucc (weights g))
    fin_cases q
    · change X.get (g,(input g hw).pos+delay) =
        some (repeatedStoreEvent l g stage mode.round (Fin.castSucc (0 : Fin 3)) (weights g))
      simpa only [hDelay0,hStart0] using hStore0 g hw
    · change X.get (g,(input g hw).pos+delay+1) =
        some (repeatedStoreEvent l g stage mode.round (Fin.castSucc (1 : Fin 3)) (weights g))
      simpa only [hDelay1,hStart1,Nat.add_zero] using hStore1 g hw
    · change X.get (g,(input g hw).pos+delay+2) =
        some (repeatedStoreEvent l g stage mode.round 2 (weights g))
      simpa only [hDelay2,hStart2,Nat.add_zero] using hStore2 g hw
  · simpa only [hWaitPos,Nat.add_assoc] using hCredit
  · simpa only [hWaitPos,Nat.add_assoc] using hEndPos
  · simpa only [Nat.add_assoc] using hEndRank
  · intro hBias
    have hd : delayedProbability mode.round (0 : Fin 4) = true := by rw [hBias]; rfl
    let pack := q0 g hw
    have hs : X.get (g,pack.cursor.pos) = some ⟨probabilityPc mode.round 0,.tc .waitLd⟩ := by
      cases mode
      · exact (repeatedProbabilityLoadWaitOfMaximal hp hMax hw.1.2.1 .biased 0 pack.cursor _
          (biasedStoreCode 0) hd).1
      · cases hBias
    simpa only [pack,q0Pos g hw] using hs
  · simpa only [hWaitPos] using hWaitEvent

theorem warpRepeatedProbabilityTraceWithFrameOfMaximal :
    ∀ g (hw : SameWarp l lead g),
      let start := (input g hw).pos
      let delay := if mode = .biased then 1 else 0
      let weights := fun i =>
        repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-(reference g)) (scores g i))
      ∃ cursor : OpeningTripCursor l X g (probabilityWaitPc mode.round true+1) [],
        (∀ q : Fin 4, X.get (g,start+mode.probabilityStoreOffset q) =
          some (repeatedStoreEvent l g stage mode.round q weights)) ∧
        Thread.Scores.ProbabilityCredit l X (g,start+delay+4) (g/l.block) stage 0 ∧
        X.get (g,start+delay+6) = some ⟨probabilityWaitPc mode.round true,.tc .waitSt⟩ ∧
        cursor.pos = start+delay+7 ∧ cursor.ending = (input g hw).ending ∧
        RepeatedWeights mode cursor.ready weights ∧
        ((X.tr g).take cursor.pos).countP isTcColl = ordinal+delay+6 ∧
        (mode = .biased → X.get (g,start) = some ⟨probabilityPc mode.round 0,.tc .waitLd⟩) ∧
        X.get (g,start+delay+3) = some ⟨probabilityWaitPc mode.round false,.tc .waitSt⟩ ∧
        ∀ n ∈ repeatedProbabilityRetained mode,
          cursor.ready.regs n = (input g hw).ready.regs n := by
  classical
  let delay := if mode = .biased then 1 else 0
  let weights g i :=
    repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-(reference g)) (scores g i))
  have main := warpRepeatedMainPacketWithTail hp hMax mode stage ordinal scores reference
    input hFrame hRank
  have prepare (g : Nat) (hw : SameWarp l lead g) :
      ∃ q3 : PackedRoundContinuation l X g mode stage (weights g) 3,
        (∀ q : Fin 3, X.get (g,(input g hw).pos+delay+q.val) =
          some (repeatedStoreEvent l g stage mode.round (Fin.castSucc q) (weights g))) ∧
        Thread.Scores.ProbabilityCredit l X (g,(input g hw).pos+delay+4) (g/l.block) stage 0 ∧
        q3.cursor.pos = (input g hw).pos+delay+5 ∧ q3.cursor.ending = (input g hw).ending ∧
        ((X.tr g).take q3.cursor.pos).countP isTcColl = ordinal+delay+4 ∧
        (mode = .biased → X.get (g,(input g hw).pos) =
          some ⟨probabilityPc mode.round 0,.tc .waitLd⟩) ∧
        X.get (g,(input g hw).pos+delay+3) =
          some ⟨probabilityWaitPc mode.round false,.tc .waitSt⟩ ∧
        q3.origin = (input g hw).ready := by
    obtain ⟨u,hStores,hCredit,hPos,hEnd,hCount,q3,hQ3,hQEnd,hOrigin,hDelayEvent,hMainWait⟩ :=
      main g hw
    exact ⟨q3,hStores,hCredit,hQ3.trans hPos,hQEnd.trans hEnd,hQ3.symm ▸ hCount,
      hDelayEvent,hMainWait,hOrigin⟩
  choose q3 hMain hCredit hQ3 hQEnd hQRank hDelayEvent hMainWait hQOrigin using prepare
  have hDelay3 : (if delayedProbability mode.round (3 : Fin 4) then 1 else 0 : Nat) = 0 := by
    cases mode <;> rfl
  have hPc : probabilityPc mode.round 3+1 = probabilityWaitPc mode.round true := by
    cases mode <;> rfl
  have hBeforeWait := warpIssueMainQuarter hp hMax (ordinal+delay+4) (3 : Fin 4) weights q3 hQRank
  choose after hStore3 hAfterPos hAfterBefore hAfterReady hAfterEnd hAfterRank using hBeforeWait
  let wait (g : Nat) (hw : SameWarp l lead g) :
      OpeningTripCursor l X g (probabilityWaitPc mode.round true) [] :=
    let c := after g hw
    have hAt : At c.ready (probabilityWaitPc mode.round true) [] := by
      rw [← hPc]
      exact c.checkpoint
    ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,hAt,c.recorded,c.remaining,
      c.localSteps⟩
  have hWaitPos g (hw : SameWarp l lead g) : (wait g hw).pos = (input g hw).pos+delay+6 := by
    simpa only [wait,hDelay3,Nat.add_zero,Nat.add_assoc,hQ3 g hw] using hAfterPos g hw
  have hWaitRank g (hw : SameWarp l lead g) :
      ((X.tr g).take (wait g hw).pos).countP isTcColl = ordinal+delay+5 := by
    simpa only [wait,hDelay3,Nat.add_zero,Nat.add_assoc] using hAfterRank g hw
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  intro g hw
  let w := wait g hw
  obtain ⟨he,hPast,hTail⟩ := probabilityStoreWaitOfMaximal hp hMax hw.1.2.1 mode.round true w
  have hRelease (hEnd : w.pos+1 = (X.tr g).length) : Step.Released l X g := by
    apply probabilityCollectiveReleased he (.inr (.inl rfl)) (hWaitRank g hw) _ hEnd
    intro peer hm
    obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hm
    have hLaneBound := (List.mem_range.mp hLane).trans_le (Nat.min_le_left ..)
    have hSame := (Step.sameWarp_lane hBlock hw.1.2.1 hLaneBound).1
    let hPeer := Step.sameWarp_trans hw hSame
    let v := wait (warpLane l g lane) hPeer
    have hOther := (probabilityStoreWaitOfMaximal hp hMax hPeer.1.2.1 mode.round true v).1
    exact ⟨v.pos,⟨⟨_,hOther,rfl⟩,hWaitRank _ hPeer⟩⟩
  let u := next w.ready
  let result : OpeningTripCursor l X g (probabilityWaitPc mode.round true+1) [] :=
    ⟨w.pos+1,u,u,w.ending,Nat.succ_pos _,len_of_get he,hRelease,
      w.checkpoint.next,hPast,hTail,.refl⟩
  have hLast : X.get (g,(input g hw).pos+delay+5) =
      some (repeatedStoreEvent l g stage mode.round 3 (weights g)) := by
    simpa only [hDelay3,Nat.add_zero,hQ3 g hw] using hStore3 g hw
  have hOffset (q : Fin 4) :
      mode.probabilityStoreOffset q = delay + (if q.val = 3 then 5 else q.val) := by
    cases mode <;> fin_cases q <;> decide
  have hWeights : RepeatedWeights mode (q3 g hw).cursor.ready (weights g) := by
    let pack := q3 g hw
    cases mode with
    | biased => exact (observedBiasedRegs pack.mixed 3 pack.table pack.holds).1
    | unbiased => exact (observedUnbiasedRegs 3 pack.table pack.holds).1
  have hSameRegs : result.ready.regs = (q3 g hw).cursor.ready.regs := by
    change (after g hw).ready.regs = _
    rw [hAfterReady g hw,hAfterBefore g hw]
    rfl
  refine ⟨result,?_,hCredit g hw,?_,?_,(hAfterEnd g hw).trans (hQEnd g hw),?_,?_,
    hDelayEvent g hw,hMainWait g hw,?_⟩
  · intro q
    rw [hOffset]
    by_cases hq : q.val = 3
    · have h : q = 3 := Fin.ext hq
      subst q
      change X.get (g,(input g hw).pos+(delay+5)) =
        some (repeatedStoreEvent l g stage mode.round 3 (weights g))
      simpa only [Nat.add_assoc] using hLast
    · rw [ite_eq_right hq,← Nat.add_assoc]
      have hq' : q.val < 3 := by have := q.isLt; omega
      exact hMain g hw ⟨q.val,hq'⟩
  · simpa only [w,hWaitPos g hw] using he
  · change (wait g hw).pos+1 = _
    rw [hWaitPos g hw]
  · exact ⟨fun r hr => (congrFun hSameRegs r).trans (hWeights.1 r hr),
      fun r hr => (congrFun hSameRegs r).trans (hWeights.2 r hr)⟩
  · exact (countP_take_succ (p := isTcColl) he rfl).trans
      (congrArg (·+1) (hWaitRank g hw))

  · intro n hn
    let pack := q3 g hw
    rw [hSameRegs,← hQOrigin g hw]
    change pack.cursor.ready.regs n = pack.origin.regs n
    cases mode with
    | biased =>
      rcases List.mem_append.mp hn with hOrig | hSave
      · exact ((observedBiasedRegs pack.mixed 3 pack.table pack.holds).2 n hOrig).trans
          (pack.originalFrame n hOrig)
      · have hValue := biasedStoreKeepsContinuation pack.mixed pack.table hSave
        exact (pack.holds _ _ hValue).trans (pack.continuationFrame n hSave)
    | unbiased =>
      rcases List.mem_append.mp hn with hOrig | hSave
      · exact ((observedUnbiasedRegs 3 pack.table pack.holds).2 n hOrig).trans
          (pack.originalFrame n hOrig)
      · have hValue := unbiasedStoreKeepsContinuation pack.table hSave
        exact (pack.holds _ _ hValue).trans (pack.continuationFrame n hSave)

end PTX.Kernels.TmlFa4Fwd.Softmax
