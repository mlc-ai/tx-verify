-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondTerminalProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingPollProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalCreditProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

noncomputable def SecondTerminalWordsReady.wordsFrame {p : Params} {l : Launch}
    {X : Execution} {g batch : Nat} (c : SecondTerminalWordsReady p l X g batch) :
    List (Nat × Value) :=
  (statsReg 1 .maximum,Softmax.scoreValue c.maximum) :: (statsReg 1 .sum,fl c.sum) ::
    firstChunkFrame p l g batch (laneOf l g) c.firstSum c.firstMaximum

noncomputable def SecondTerminalWordsReady.reciprocal {p : Params} {l : Launch}
    {X : Execution} {g batch : Nat} (c : SecondTerminalWordsReady p l X g batch) : ℝ :=
  1 / (if c.sum = 0 then 1 else c.sum)

noncomputable def SecondTerminalWordsReady.reciprocalFrame {p : Params} {l : Launch}
    {X : Execution} {g batch : Nat} (c : SecondTerminalWordsReady p l X g batch) :
    List (Nat × Value) :=
  (reciprocalReg 1,fl c.reciprocal) :: (reciprocalPred 1,.pred (decide (c.sum ≠ 0))) ::
    c.wordsFrame

noncomputable def SecondTerminalWordsReady.pollFrame {p : Params} {l : Launch}
    {X : Execution} {g batch : Nat} (c : SecondTerminalWordsReady p l X g batch) :
    List (Nat × Value) :=
  (finalPollPrepReg 1,finalPollPrepWord l 1) :: c.reciprocalFrame

noncomputable def SecondTerminalWordsReady.chunkFrame {p : Params} {l : Launch}
    {X : Execution} {g batch : Nat} (c : SecondTerminalWordsReady p l X g batch) :
    List (Nat × Value) :=
  (finalizeReciprocalPair 1,.pair (fl c.reciprocal) (fl c.reciprocal)) :: c.pollFrame

/-- The second output has its ready, free slot and reciprocal while all first
output statistics remain available for the final LSE computation. -/
structure SecondOutputLoadReady (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  words : SecondTerminalWordsReady p l X g batch
  freeIndex : Nat
  freeWait : X.get (g,freeIndex) =
    some ⟨finalizePollPc 1 true,.wait (finalizePollLoc l g 1 true) 1 true true .cta⟩
  cursor : OpeningTripCursor l X g (finalizeLoadPc 1 0) words.chunkFrame
  position : cursor.pos = freeIndex+1

theorem SecondTerminalWordsReady.acquireSecondOutputOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (c : SecondTerminalWordsReady p l X g batch)
    (hDone :
      let log := X.objects (Thread.outputCompletionObject l (g/l.block) 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    Nonempty (SecondOutputLoadReady p l X g batch) := by
  let A := c.wordsFrame
  have hKey {F : List (Nat × Value)} {r : Nat} (h : r ∉ F.map Prod.fst) :
      ∀ pair ∈ F, pair.1 ≠ r :=
    fun pair hm he => h (he ▸ List.mem_map_of_mem hm)
  have hReuse : (rescaleReuseReg (1-1),b32 (rescaleReuseLoc l g (1-1)).addr) ∈ A := by
    simp [A,SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      rescaleReuseReg,rescaleReuseLoc,correctionBeforeRescale,tileSetupFrame,
      correctionTileGeometryFacts,
      correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,
      entryFacts,nonzeroBarrierFacts]
  have hCount : (6498,b32 1) ∈ A := by
    simp [A,SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      finalizeLayoutFacts]
  obtain ⟨_,afterCredit,_⟩ := terminalCreditOfMaximal hp hMax hg 1 c.cursor hReuse hCount
    (hKey (of_decide_eq_true rfl))
  have hKeep : ∀ pair ∈ A, pair.1 ∉ [reciprocalPred 1,reciprocalInput 1,reciprocalReg 1] := by
    intro pair hm
    exact (of_decide_eq_true rfl :
      ∀ r ∈ A.map Prod.fst, r ∉ [reciprocalPred 1,reciprocalInput 1,reciprocalReg 1]) _
      (List.mem_map_of_mem hm)
  obtain ⟨u,hU,hLocal⟩ := finalReciprocalWithPredicateLocal (l := l) (g := g) 1
    afterCredit.checkpoint afterCredit.checkpoint.2.2.2.2.2.1
    (show valFloat .f32 (fl c.sum) = .ok c.sum from rfl) hKeep
  have hAt : At u (reciprocalPc 1+3) c.reciprocalFrame := hU
  have hShared : u.regs 2535 = some (b32 l.sharedBase) := by
    apply holds_mem hAt.2.2.2.2
    simp [SecondTerminalWordsReady.reciprocalFrame,SecondTerminalWordsReady.wordsFrame,
      firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale,tileSetupFrame,
      correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,
      entryFacts,nonzeroBarrierFacts]
  obtain ⟨v,hPrep,hV⟩ := finalPollPrep hp 1 (g := g) hAt hShared (hKey (of_decide_eq_true rfl))
  let F := c.pollFrame
  let poll : OpeningTripCursor l X g (finalizePollPc 1 false) F :=
    ⟨afterCredit.pos,afterCredit.before,v,afterCredit.ending,afterCredit.positive,
      afterCredit.bounded,afterCredit.released,hV,afterCredit.recorded,afterCredit.remaining,
      afterCredit.localSteps.trans (hLocal.trans hPrep)⟩
  have hBase : (finalizePollBase 1 false,b32 (finalizePollLoc l g 1 false).addr) ∈ F := by
    exact .head _
  have hPhase : (finalizePollPhase false,b32 false.toNat) ∈ F := by
    simp [F,SecondTerminalWordsReady.pollFrame,SecondTerminalWordsReady.reciprocalFrame,
      SecondTerminalWordsReady.wordsFrame,firstChunkFrame,finalPollPrepReg,finalPollPrepWord,
      finalizePollPhase]
  obtain ⟨_,_,after,_⟩ := finalizePollOfMaximal hp hMax hg 1 false poll
    (hKey (of_decide_eq_true rfl)) hBase hPhase (fun _ _ _ => by
      obtain ⟨s,hs,hOne⟩ := hDone
      exact ⟨s,hs,by rw [hOne]; decide⟩)
  have hFreeBase : (finalizePollBase 1 true,b32 (finalizePollLoc l g 1 true).addr) ∈ F := by
    simp [F,SecondTerminalWordsReady.pollFrame,SecondTerminalWordsReady.reciprocalFrame,
      SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      finalizePollBase,finalizePollLoc,correctionBeforeRescale,tileSetupFrame,
      correctionTileGeometryFacts]
  have hFreePhase : (6498,b32 1) ∈ F := List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hCount))
  obtain ⟨j,hWait,free,hPos⟩ := stagingWaitOfMaximal hp hMax hg hw 1 after
    (hKey (of_decide_eq_true rfl)) hFreeBase hFreePhase
  have hRecip : free.ready.regs (reciprocalReg 1) = some (fl c.reciprocal) :=
    holds_mem free.checkpoint.2.2.2.2 (.tail _ (.head _))
  obtain ⟨w,hW,hWLocal⟩ := packFinalReciprocalLocal (l := l) (g := g) 1 c.reciprocal
    free.checkpoint hRecip (hKey (of_decide_eq_true rfl))
  exact ⟨⟨c,j,hWait,⟨free.pos,free.before,w,free.ending,free.positive,free.bounded,
    free.released,hW,free.recorded,free.remaining,free.localSteps.trans hWLocal⟩,hPos⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
