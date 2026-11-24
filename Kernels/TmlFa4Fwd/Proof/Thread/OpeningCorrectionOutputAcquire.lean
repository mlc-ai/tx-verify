-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalCreditProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFinalPollProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalPollEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue

noncomputable def firstTerminalReciprocalFrame (p : Params) (l : Launch) (g batch lane : Nat)
    (sum : ℝ) (maximum : Option ℝ) : List (Nat × Value) :=
  (reciprocalReg 0,fl (1 / (if sum = 0 then 1 else sum))) ::
    (reciprocalPred 0,.pred (decide (sum ≠ 0))) ::
    (6513,Softmax.scoreValue maximum) :: (6512,fl sum) ::
    finalizeLayoutFacts l (warpLane l g lane) ++
    (7134,b32 p.scaleLog2Bits) :: correctionBeforeRescale p l g batch lane

/-- A first terminal correction lane that has acquired the accumulator output
and is now at its separate shared staging availability test. -/
structure FirstOutputAcquired (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  sum : ℝ
  maximum : Option ℝ
  valid : Softmax.DenominatorValid sum maximum
  cursor : OpeningTripCursor l X (warpLane l g lane) (finalizePollPc 0 true)
    ((finalPollPrepReg 0,finalPollPrepWord l 0) ::
      firstTerminalReciprocalFrame p l g batch lane sum maximum)

/-- Returning the statistics credit enables normalization setup. The recorded
MMA completion phase forces the actual accumulator acquire. -/
theorem FirstTerminalWordsReady.acquireFirstOutputOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (c : FirstTerminalWordsReady p l X g batch lane)
    (hDone :
      let log := X.objects (Thread.outputCompletionObject l (warpLane l g lane/l.block) 0)
      ∃ state, MBarrier.stateBefore log log.length = some state ∧ state.phase = 1) :
    Nonempty (FirstOutputAcquired p l X g batch lane) := by
  let thread := warpLane l g lane
  let T := [(6513,Softmax.scoreValue c.maximum),(6512,fl c.sum)] ++
    finalizeLayoutFacts l thread ++
    (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane
  obtain ⟨_,afterCredit,_⟩ := c.creditOfMaximal hp hMax hg
  have hRecip : At afterCredit.ready (reciprocalPc 0) T := afterCredit.checkpoint
  have hKeep : ∀ rv ∈ T, rv.1 ∉ [reciprocalPred 0,reciprocalInput 0,reciprocalReg 0] := by
    intro rv hm hn
    have hR := List.mem_map_of_mem (f := Prod.fst) hm
    exact (of_decide_eq_true rfl : ∀ r ∈ T.map Prod.fst,
      r ∉ [reciprocalPred 0,reciprocalInput 0,reciprocalReg 0]) _ hR hn
  obtain ⟨u,hu,hLocal⟩ := finalReciprocalWithPredicateLocal (l := l) (g := thread) 0
    hRecip hRecip.2.2.2.2.2.1 (show valFloat .f32 (fl c.sum) = .ok c.sum from rfl) hKeep
  let A := firstTerminalReciprocalFrame p l g batch lane c.sum c.maximum
  have hAt : At u (reciprocalPc 0+3) A := hu
  have hShared : u.regs 2535 = some (b32 l.sharedBase) :=
    holds_mem hAt.2.2.2.2 (by
      simp [A,firstTerminalReciprocalFrame,correctionBeforeRescale,tileSetupFrame,
        correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,entryFacts,
        nonzeroBarrierFacts])
  have hFresh : ∀ pair ∈ A, pair.1 ≠ finalPollPrepReg 0 := by
    intro pair hm he
    have hR := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hR
    exact (of_decide_eq_true rfl : finalPollPrepReg 0 ∉ A.map Prod.fst) hR
  obtain ⟨v,hPrep,hV⟩ := finalPollPrep hp 0 (g := thread) hAt hShared hFresh
  let F := (finalPollPrepReg 0,finalPollPrepWord l 0)::A
  let poll : OpeningTripCursor l X thread (finalizePollPc 0 false) F :=
    ⟨afterCredit.pos,afterCredit.before,v,afterCredit.ending,afterCredit.positive,
      afterCredit.bounded,afterCredit.released,hV,afterCredit.recorded,afterCredit.remaining,
      afterCredit.localSteps.trans (hLocal.trans hPrep)⟩
  have hPred : ∀ pair ∈ F, pair.1 ≠ finalizePollPred 0 false := by
    intro pair hm he
    have hR := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hR
    exact (of_decide_eq_true rfl : finalizePollPred 0 false ∉ F.map Prod.fst) hR
  have hBase : (finalizePollBase 0 false,b32 (finalizePollLoc l thread 0 false).addr) ∈ F := by
    simp [F,A,firstTerminalReciprocalFrame,finalizePollBase,finalizePollLoc,correctionBeforeRescale,
      tileSetupFrame,correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,
      entryFacts,nonzeroBarrierFacts]
  have hPhase : (finalizePollPhase false,b32 false.toNat) ∈ F := .head _
  obtain ⟨_,_,after,_⟩ := finalizePollOfMaximal hp hMax hg 0 false poll hPred hBase hPhase
    (fun _ _ _ => by
      obtain ⟨state,hState,hPhase⟩ := hDone
      exact ⟨state,hState,by rw [hPhase]; decide⟩)
  exact ⟨⟨c.sum,c.maximum,c.valid,after⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
