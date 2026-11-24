-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxSingleVisitRetire
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Correction Protocol.Statistics

/-- The loop's terminal row with its actual mass, named generation, and next credit parity. -/
structure TerminalProducerRow (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (trips : Nat) where
  sum : ℝ
  maximum : Option ℝ
  valid : DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g 7605
    (terminalRowFrame p l g warp (trips%2) (fl sum) (scoreValue maximum))
  ordinal : observedBarrierOrdinal X (g,cursor.pos+2) (3+warpIndex l g) = trips

theorem TerminalProducerRow.published {p : Params} {l : Launch} {X : Execution} {m : Mem0}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g trips : Nat}
    (hg : g < l.threads) {warp : Fin 8} (w : warp.val = warpIndex l g)
    (row : TerminalProducerRow p l X g warp trips) :
    X.Writes (g,row.cursor.pos) (statsAcc l g warp 2) (fl row.sum).toBytes ∧
      X.Writes (g,row.cursor.pos+1) (statsAcc l g warp 3) (scoreValue row.maximum).toBytes ∧
      Scores.Publishes X (g,row.cursor.pos+2) .final := by
  have bytes : (scoreValue row.maximum).bytes = 4 := by cases row.maximum <;> rfl
  obtain ⟨s,m,bar,pos⟩ := terminalPublicationCursorOfRow hp hMax hg warp w rfl bytes row.cursor
  obtain ⟨he,_,_⟩ := statsArrivalOfMaximal hp none warp hg bar.positive bar.bounded
    (bar.checkpoint.mono ⟨bar.checkpoint.2.2.2.2.1,trivial⟩)
    bar.recorded bar.localSteps bar.remaining (fun h => ⟨X,hMax,rfl,bar.released h⟩)
  rw [pos] at he
  exact ⟨s,m,_,he,rfl⟩

/-- The softmax scheduler scans all groups with the named generation and final
mbarrier phase for the selected tile, including any number of steady visits. -/
theorem allocationArrivalsOfTerminalRows {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g batch trips : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (rows : ∀ lane < 32, Nonempty (TerminalProducerRow p l X (warpLane l g lane)
      ⟨warpIndex l g,hw⟩ trips))
    (released : CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g) trips)
    (available : TerminalCreditAvailable l X g (stageOf ⟨warpIndex l g,hw⟩) (trips%2)) :
    ∀ lane < 32, ∃ j, FinalAllocationArrival X (warpLane l g lane,j) .arrive := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  have work := hi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
  obtain ⟨count,_,⟨active⟩⟩ := activeWarpOfMaximal hp hMax hg hw hCuQ hb lo hi
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have each (lane : Nat) (hl : lane < 32) :
      ∃ drain : TerminalDrainLane p l X (warpLane l g lane) warp (trips%2),
        ((X.tr (warpLane l g lane)).take drain.first.pos).countP Execution.isShfl = count ∧
        ((X.tr (warpLane l g lane)).take drain.first.pos).countP isFullWarpVote = 1 := by
    obtain ⟨row⟩ := rows lane hl
    have same := (Step.sameWarp_lane hBlock hg hl).1
    have w : warp.val = warpIndex l (warpLane l g lane) := same.2
    have cta := same.1.2.2
    have bytes : (scoreValue row.maximum).bytes = 4 := by cases row.maximum <;> rfl
    obtain ⟨_,⟨drain⟩⟩ := terminalDrainLaneOfRow hp hMax hCuQ same.1.2.1 warp w rfl bytes
      row.cursor (fun _ => by
        change CtaBarrier.Released l.block (X.barriers (warpLane l g lane/l.block))
          (3+warpIndex l (warpLane l g lane))
          (observedBarrierOrdinal X (warpLane l g lane,row.cursor.pos+2)
            (3+warpIndex l (warpLane l g lane)))
        have owner : g/l.block = warpLane l g lane/l.block := cta
        rw [row.ordinal,← w,← owner]
        exact released)
    have ord := terminalOrdinalsOfActiveCursor (terminalWarpLaneCursor active lane hl) drain.first
    exact ⟨drain,ord.1.trans (active.ordinals.shfl lane hl),
      ord.2.trans (active.ordinals.vote lane hl)⟩
  choose drain ord using each
  have finish := terminalFinishedOfDrainLanes hp hMax hCuQ hg hw work (fun _ => trips%2) drain ord
  intro lane hl
  have same := (Step.sameWarp_lane hBlock hg hl).1
  apply finalAllocationArrivalOfSchedulerFinished hp hMax same.1.2.1 warp
    (Nat.mod_lt _ (by decide)) (finish lane hl)
  simpa only [TerminalCreditAvailable,← same.1.2.2] using available

end PTX.Kernels.TmlFa4Fwd.Softmax
