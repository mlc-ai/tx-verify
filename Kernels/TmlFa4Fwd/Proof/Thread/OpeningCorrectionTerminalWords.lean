-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionTerminal
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalReadProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Thread.Correction

/-- The first correction terminal cursor holds the paired producer's actual row statistics. -/
structure FirstTerminalWordsReady (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  waitIndex : Nat
  sum : ℝ
  maximum : Option ℝ
  valid : Softmax.DenominatorValid sum maximum
  waited : Thread.CorrectionWaits X (warpLane l g lane,waitIndex) .terminal 0
  sumRead : X.get (warpLane l g lane,waitIndex+1) = some ⟨statsPc 0 .sum,
    .rd {loc := statsLoc l (warpLane l g lane) 0 .sum,size := 4} ((fl sum).toBytes.map some)⟩
  maximumRead : X.get (warpLane l g lane,waitIndex+2) = some ⟨statsPc 0 .maximum,
    .rd {loc := statsLoc l (warpLane l g lane) 0 .maximum,size := 4}
      ((scoreValue maximum).toBytes.map some)⟩
  cursor : OpeningTripCursor l X (warpLane l g lane) 8468
    ((6513,scoreValue maximum)::(6512,fl sum)::
      finalizeLayoutFacts l (warpLane l g lane) ++
      (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane)
  position : cursor.pos = waitIndex+3

/-- A released first terminal wait reaches both actual loads and the next credit
with the matched producer's row statistics. -/
theorem FirstTerminalStatisticsCursor.readPublishedOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (c : FirstTerminalStatisticsCursor p l X g batch lane)
    (hRelease : c.index+1 = (X.tr (warpLane l g lane)).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Y.MemWrites = X.MemWrites ∧ Step.Released l Y (warpLane l g lane))
    (hMatched : ∀ Y, Maximal l kernel Assumptions.all m Y → Y.tr = X.tr →
      Y.MemWrites = X.MemWrites → c.index+1 < (Y.tr (warpLane l g lane)).length →
      ∃ pub sum max,
        TerminalPublishedWords l Y (warpLane l g lane) 0 pub (fl sum) (scoreValue max) ∧
        TerminalGeneration l Y (warpLane l g lane) 0 (pub-2) c.index ∧
        Softmax.DenominatorValid sum max) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Nonempty (FirstTerminalWordsReady p l Y g batch lane) := by
  let thread := warpLane l g lane
  let F := finalizeLayoutFacts l thread ++
    (7134,b32 p.scaleLog2Bits)::correctionBeforeRescale p l g batch lane
  obtain ⟨Y,hY,hTrace,hWriters,cur,hPos⟩ := c.resumeAtCursorOfMaximal hMax hRelease
  have hLocalCuQ : Epilogue.DrainCuQProtected p Y := by
    unfold Epilogue.DrainCuQProtected at hCuQ ⊢
    rwa [hWriters]
  have hSync := guardedOfTmaSafe hY.1 (Safety.noTmaUnsafe hp hY.1 hLocalCuQ)
  have hBase : (1627,b32 (l.sharedBase+4*rowOf l thread)) ∈ F := by
    simp [F,thread,correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts]
  have hPass := terminalStatsSumRecorded hp hY hSync hg 0 cur hBase
  rw [hPos] at hPass
  obtain ⟨pub,sum,max,hWords,hGeneration,hValid⟩ := hMatched Y hY hTrace hWriters hPass
  have hWait : Thread.CorrectionWaits Y (thread,c.index) .terminal 0 := by
    obtain ⟨e,he,hKind⟩ := c.waited
    exact ⟨e,by simpa only [Execution.get,hTrace] using he,hKind⟩
  have hFresh : ∀ pair ∈ F,
      pair.1 ≠ statsReg 0 .sum ∧ pair.1 ≠ statsReg 0 .maximum := by
    intro pair hm
    refine ⟨fun h => ?_,fun h => ?_⟩ <;>
      have hR := List.mem_map_of_mem (f := Prod.fst) hm <;>
      rw [h] at hR
    · exact (of_decide_eq_true rfl : statsReg 0 .sum ∉ F.map Prod.fst) hR
    · exact (of_decide_eq_true rfl : statsReg 0 .maximum ∉ F.map Prod.fst) hR
  have hSize : (scoreValue max).bytes = 4 := by cases max <;> rfl
  have hScalar : rebuild 3 ((scoreValue max).toBytes.map some) = .ok (scoreValue max) := by
    apply PTX.Proof.rebuild_scalar (by rw [hSize]; decide)
    cases max <;> rfl
  obtain ⟨nextC,hPosNew,hSum,hMaxWord⟩ :=
    terminalStatsWordsOfMaximal hp hY hSync hg hWait hWords rfl hSize
    hGeneration cur hPos hBase hFresh
    (PTX.Proof.rebuild_scalar (by change 0 < 4; decide) rfl) hScalar
  exact ⟨Y,hY,hTrace,hWriters,⟨⟨c.index,sum,max,hValid,hWait,hSum,hMaxWord,nextC,hPosNew⟩⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
