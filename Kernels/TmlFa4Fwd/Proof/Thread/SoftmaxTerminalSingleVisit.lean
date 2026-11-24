-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainRetained
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorProgress
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveGroupProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Correction

/-- Startup scheduler coordinates survive to the terminal row in the actual lane trace. -/
theorem geometryAtTerminalOfRecordedSource {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g : Nat} {F : List (Nat × Value)}
    (source : OpeningTripCursor l X g 3212 (RowDrainRole.softmax.frame p l g))
    (target : OpeningTripCursor l X g 7605 F) :
    Holds target.ready.regs (RowDrainRole.softmax.frame p l g) := by
  let span : RowDrainSpan := ⟨3212,7606,7606⟩
  apply span.recordedKeep hp (by decide) (by decide) (by decide) rfl _ _ _ _ _ _ source target
  · exact fun pc h => of_decide_eq_true (List.all_eq_true.mp
      (show Assumptions.swExp2Sites.all (fun n => decide (n < 7605)) = true by decide) pc h)
  · exact fun pc h => of_decide_eq_true (List.all_eq_true.mp
      (show Assumptions.swExp2Sites.all (fun n => decide (n < 7606)) = true by decide) pc h)
  · simp only [RowDrainRole.frame,List.map_cons,List.map_nil]
    set_option maxRecDepth 100000 in decide +kernel
  · apply span.segmentKeeps_of_audit
    simp only [RowDrainRole.frame,List.map_cons,List.map_nil]
    set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel

/-- The actual opening denominator's one-visit branch enters terminal statistics with
parity one and the unchanged scheduler coordinates. -/
theorem OpeningDenominatorCursor.terminalRowOfSingleVisit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g cap past : Nat} (hw : warpIndex l g < 8)
    (hCap : 0 < cap) (hCapSigned : cap < 2^31) (hPast : past+256 < 2^31)
    (source : OpeningTripCursor l X g 3212 (RowDrainRole.softmax.frame p l g))
    (c : OpeningDenominatorCursor p l X g 1 cap past) :
    ∃ row : OpeningTripCursor l X g 7605
      (terminalRowFrame p l g ⟨warpIndex l g,hw⟩ 1 (fl c.sum) (scoreValue c.maximum)),
      row.pos = c.cursor.pos := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  have hBiased : firstBiasedRepeats 1 cap = 0 := by unfold firstBiasedRepeats; omega
  have hPlain : firstPlainSplit 1 cap = 0 := by unfold firstPlainSplit; omega
  obtain ⟨t,hLocal,ht,hAbi⟩ := c.enterLoops hp (by decide) (by decide) hCap hCapSigned hPast
  have hTerminal : At t 7605 ((1491,b32 0)::firstLoopChoiceFacts 1 0 past c.maximum c.sum) := by
    simpa only [hBiased,hPlain,ite_true] using ht
  let target : OpeningTripCursor l X g 7605
      ((1491,b32 0)::firstLoopChoiceFacts 1 0 past c.maximum c.sum) :=
    ⟨c.cursor.pos,c.cursor.before,t,c.cursor.ending,c.cursor.positive,c.cursor.bounded,
      c.cursor.released,hTerminal,c.cursor.recorded,c.cursor.remaining,
      c.cursor.localSteps.trans hLocal⟩
  have hGeom := geometryAtTerminalOfRecordedSource hp source target
  have hReg (r : Nat) (v : Value)
      (h : (r,v) ∈ (1491,b32 0)::firstLoopChoiceFacts 1 0 past c.maximum c.sum) :
      t.regs r = some v := holds_mem hTerminal.2.2.2.2 h
  have hFacts : Holds t.regs (terminalRowFrame p l g warp 1 (fl c.sum) (scoreValue c.maximum)) := by
    apply (holds_append ..).mpr
    refine ⟨⟨hReg _ _ ?_,hReg _ _ ?_,hAbi.2.2.1,trivial⟩,?_⟩
    · simp [firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]
    · simp [firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]
    · exact ⟨hReg _ _ (by simp [firstLoopChoiceFacts,loopChoiceFacts]),
        hAbi.1,hAbi.2.1,hGeom⟩
  exact ⟨⟨target.pos,target.before,t,target.ending,target.positive,target.bounded,
    target.released,hTerminal.mono hFacts,target.recorded,target.remaining,target.localSteps⟩,rfl⟩

/-- The actual first rescan boundary retains its matching post-publication checkpoint. -/
structure TerminalDrainLane (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (parity : Nat) where
  start : OpeningTripCursor l X g 7617 (terminalRetained l warp parity)
  first : OpeningTripCursor l X g 7622
    ((7259,b32 (terminalFirstWord p l g))::RowDrainRole.softmax.roots p l g)

/-- The terminal publication yields both the original ABI and the first rescan shuffle. -/
theorem terminalDrainLaneOfRow {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g parity : Nat} (hg : g < l.threads)
    (warp : Fin 8) (hw : warp.val = warpIndex l g) {sum maximum : Value}
    (hSum : sum.bytes = 4) (hMaxWord : maximum.bytes = 4)
    (c : OpeningTripCursor l X g 7605 (terminalRowFrame p l g warp parity sum maximum))
    (hSync : c.pos+3 = (X.tr g).length →
      CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g)
        (((X.tr g).take (c.pos+2)).countP (Execution.isBarId (3+warpIndex l g)))) :
    Scores.Publishes X (g,c.pos+2) .final ∧ Nonempty (TerminalDrainLane p l X g warp parity) := by
  obtain ⟨_,_,bar,hBar⟩ := terminalPublicationCursorOfRow hp hMax hg warp hw hSum hMaxWord c
  have hReady : bar.pos+1 = (X.tr g).length →
      CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g)
        (((X.tr g).take bar.pos).countP (Execution.isBarId (3+warpIndex l g))) := by
    rwa [hBar]
  obtain ⟨hPub,drain,_⟩ := terminalDrainStartOfPublication hp hMax hg warp hw bar hReady
  have hFrame := (holds_append ..).mp drain.checkpoint.2.2.2.2
  let c0 : OpeningTripCursor l X g 7617 (terminalRetained l warp parity) :=
    ⟨drain.pos,drain.before,drain.ready,drain.ending,drain.positive,drain.bounded,
      drain.released,drain.checkpoint.mono hFrame.2,drain.recorded,drain.remaining,drain.localSteps⟩
  let c1 : OpeningTripCursor l X g 7617 (RowDrainRole.softmax.guarded p l g) :=
    ⟨drain.pos,drain.before,drain.ready,drain.ending,drain.positive,drain.bounded,
      drain.released,drain.checkpoint.mono hFrame.1,drain.recorded,drain.remaining,drain.localSteps⟩
  obtain ⟨next⟩ := terminalDrainFirstShuffleOfMaximal hp hMax hCuQ hg c1
  exact ⟨hBar ▸ hPub,⟨⟨c0,next⟩⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
