-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalSingleVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainLoopSearch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Correction

/-- The lane view of a reached warp carries its original recorded checkpoint. -/
def terminalWarpLaneCursor {l : Launch} {X : Execution} {g pc shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g pc F shuffles votes ends) (lane : Nat) (hl : lane < 32) :
    OpeningTripCursor l X (warpLane l g lane) pc (F lane) :=
  ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,cur.bounded lane hl,
    cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,
    cur.continuation lane hl,cur.localSteps lane hl⟩

private theorem reachedFirstOfDrainLanes {p : Params} {l : Launch} {X : Execution}
    {g shuffles votes : Nat} {warp : Fin 8} {parity : Nat → Nat}
    (lanes : ∀ lane < 32, TerminalDrainLane p l X (warpLane l g lane) warp (parity lane))
    (hOrd : ∀ lane (hl : lane < 32),
      let tr := (X.tr (warpLane l g lane)).take (lanes lane hl).first.pos
      tr.countP Execution.isShfl = shuffles ∧ tr.countP isFullWarpVote = votes) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 7622
      (fun lane => let t := warpLane l g lane
        (7259,b32 (terminalFirstWord p l t))::RowDrainRole.softmax.roots p l t)
      shuffles votes ends) := by
  let pos (lane : Nat) := if hl : lane < 32 then (lanes lane hl).first.pos else 0
  let before (lane : Nat) := if hl : lane < 32 then (lanes lane hl).first.before else {}
  let ready (lane : Nat) := if hl : lane < 32 then (lanes lane hl).first.ready else {}
  let ends (lane : Nat) := if hl : lane < 32 then (lanes lane hl).first.ending else none
  refine ⟨ends,⟨⟨⟨pos,before,ready,⟨?_,?_⟩,?_,?_,?_⟩,?_,?_,?_,?_⟩⟩⟩
  · intro lane hl
    simpa only [pos,dite_eq_left hl] using (hOrd lane hl).1
  · intro lane hl
    simpa only [pos,dite_eq_left hl] using (hOrd lane hl).2
  · intro lane hl
    simpa only [before,pos,ends,dite_eq_left hl] using (lanes lane hl).first.remaining
  · intro lane hl
    simpa only [before,ready,dite_eq_left hl] using (lanes lane hl).first.localSteps
  · intro lane hl
    simpa only [ready,dite_eq_left hl] using (lanes lane hl).first.checkpoint
  · intro lane hl
    simpa only [pos,dite_eq_left hl] using (lanes lane hl).first.positive
  · intro lane hl
    simpa only [pos,dite_eq_left hl] using (lanes lane hl).first.bounded
  · intro lane hl
    simpa only [pos,dite_eq_left hl] using (lanes lane hl).first.released
  · intro lane hl
    simpa only [pos,before,dite_eq_left hl] using (lanes lane hl).first.recorded

private theorem terminalFinishAtSelectedWithOriginalAbi {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) (hLow : tilePrefix p first*p.heads ≤ g/l.block)
    (hHigh : g/l.block < tilePrefix p (min p.batch (first+31))*p.heads)
    (warp : Fin 8) (parity : Nat → Nat) {ends : Nat → Option TState}
    (lanes : ∀ lane < 32, TerminalDrainLane p l X (warpLane l g lane) warp (parity lane))
    (selected : SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p first (laneOf l t)))::terminalSelectedGroup p l t first)
      shuffles votes ends) :
    ∀ lane < 32, TerminalSchedulerFinished l X (warpLane l g lane) warp (parity lane) := by
  have hFrame : Nonempty (SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p first (laneOf l t)))::
          (terminalSelectedGroup p l t first ++ terminalRetained l warp (parity lane)))
      shuffles votes ends) := by
    apply selected.advanceLocal
    intro lane hl
    let target := terminalWarpLaneCursor selected lane hl
    have hKept := terminalRetainedAtComparison hp (lanes lane hl).start target
    have ht := selected.checkpoint lane hl
    exact ⟨_,.refl,ht.mono ⟨ht.2.2.2.2.1,(holds_append ..).mpr ⟨ht.2.2.2.2.2,hKept⟩⟩⟩
  obtain ⟨cur⟩ := hFrame
  exact terminalFinishedOfSelectedGroup hp hMax hg hFirst hLow hHigh warp parity cur

/-- A reached active warp scans to its selected request and preserves its actual
original terminal parity and ABI until each lane is ready for the final credit. -/
theorem terminalFinishedOfDrainLanes {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (parity : Nat → Nat)
    (lanes : ∀ lane < 32, TerminalDrainLane p l X (warpLane l g lane)
      ⟨warpIndex l g,hw⟩ (parity lane))
    (hOrd : ∀ lane (hl : lane < 32),
      let tr := (X.tr (warpLane l g lane)).take (lanes lane hl).first.pos
      tr.countP Execution.isShfl = shuffles ∧ tr.countP isFullWarpVote = votes) :
    ∀ lane < 32, TerminalSchedulerFinished l X (warpLane l g lane) ⟨warpIndex l g,hw⟩
      (parity lane) := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  obtain ⟨ends,⟨cur⟩⟩ := reachedFirstOfDrainLanes lanes hOrd
  obtain ⟨down⟩ := terminalDrainConsumesFirstShuffle hp hMax hg cur
  obtain ⟨up⟩ := terminalDrainSecondShuffleOfWarp hp hg down
    (terminalRequestGuardOfWarp hp hMax hCuQ hg hw down)
  obtain ⟨scan⟩ := terminalDrainFirstUpScanOfMaximal hp hMax hg up
  obtain ⟨total⟩ := terminalDrainFirstTotalOfMaximal hp hMax hg scan
  by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · have hTiles (lane : Nat) (hl : lane < 32) : (total.state lane).regs 7262 =
        some (b32 (groupLaneTiles p 0 (laneOf l (warpLane l g lane)))) := by
      let c := terminalWarpLaneCursor up lane hl
      let before : OpeningTripCursor l X (warpLane l g lane) 7642
          [(7262,b32 (groupLaneTiles p 0 (laneOf l (warpLane l g lane))))] :=
        ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,
          c.checkpoint.mono ⟨c.checkpoint.2.2.2.2.1,trivial⟩,c.recorded,c.remaining,c.localSteps⟩
      exact (terminalFirstCountAtTotal hp before (terminalWarpLaneCursor total lane hl)).1
    obtain ⟨selected⟩ := terminalFirstSelectedWithTileCount hp hg hFirst total hTiles
    exact terminalFinishAtSelectedWithOriginalAbi hp hMax hg hp.shape.1 (by simp [tilePrefix])
      hFirst warp parity lanes selected
  · have hBack := terminalDrainFirstRouteOfMaximal hp hg total
    rw [ite_eq_right hFirst] at hBack
    obtain ⟨loop⟩ := hBack
    have hs := terminalDrainSearchOfMaximal hp hMax hCuQ hg (Nat.zero_le _)
      (Nat.le_of_not_gt hFirst) loop
    rcases hs with ⟨hExhausted,_⟩ | ⟨first,_,_,hFirst,hLow,hHigh,⟨selected⟩⟩
    · exact (Nat.not_le_of_lt hActive hExhausted).elim
    · exact terminalFinishAtSelectedWithOriginalAbi hp hMax hg hFirst hLow hHigh
        warp parity lanes selected

end PTX.Kernels.TmlFa4Fwd.Softmax
