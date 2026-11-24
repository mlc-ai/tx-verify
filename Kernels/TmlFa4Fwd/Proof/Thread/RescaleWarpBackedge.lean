-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpRoundProgress
import Lemmas.Step.WarpLanes
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The nonterminal stage pair consumes exactly one remaining KV visit and
joins stage zero again with the same tensor and vote counts. -/
theorem RescaleWarpReturned.nextRound {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch blocks ord rank : Nat} {gen : Fin 2 → Nat} (many : 2 < blocks) (bound : blocks < 2^31)
    (c : RescaleWarpReturned p l X g batch blocks 1 gen ord rank) :
    Nonempty (RescaleWarpJoin p l X g batch (blocks-1) 0 gen ord rank) := by
  classical
  have each (h : Nat) (hs : SameWarp l g h) :
      ∃ d : RescaleWaitReached l X h 0 (rescaleLaneFrame p l h batch (blocks-1)),
        d.index = (c.lane h hs).pos := by
    let a := c.lane h hs
    have next := rescaleCountSteps (l := l) (thread := h) (Nat.le_of_lt many) bound a.checkpoint
      (correctionRescaleFrame_next p l h batch (laneOf l h))
    obtain ⟨v,hv,ht⟩ := next
    rw [ite_eq_left many] at ht
    let b : OpeningTripCursor l X h (statsBarrierPc 0 true)
        (rescaleLaneFrame p l h batch (blocks-1)) :=
      ⟨a.pos,a.before,v,a.ending,a.positive,a.bounded,a.released,ht,
        a.recorded,a.remaining,a.localSteps.trans hv⟩
    exact rescaleWaitReachedOfMaximal hp hMax hs.1.2.1 0
      (rescaleLaneFrame_visit hs.1.2.1 batch (blocks-1) 0) b
  choose d pos using each
  exact ⟨⟨d,fun h hs => by rw [pos]; exact c.rank h hs,
    fun h hs s => by rw [pos]; exact c.named h hs s⟩⟩

/-- The last pair returns its slot, joins the first terminal wait and
preserves the continuation needed to finish output staging. -/
theorem RescaleWarpReturned.terminal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch ord rank : Nat} {gen : Fin 2 → Nat}
    (c : RescaleWarpReturned p l X g batch 2 1 gen ord rank) {h : Nat} (hs : SameWarp l g h) :
    X.Arrive (h,(c.lane h hs).pos) ⟨.shared,h/l.block,l.sharedBase+200⟩ 0 1 true .cta ∧
      ∃ d : FirstTerminalStatisticsCursor p l X h batch (laneOf l h),
        d.index = (c.lane h hs).pos+1 := by
  let a := c.lane h hs
  have self : warpLane l h (laneOf l h) = h :=
    Step.warpLane_of_sameWarp ⟨⟨hs.1.2.1,hs.1.2.1,rfl⟩,rfl⟩
  obtain ⟨v,hv,ht⟩ := rescaleCountSteps (l := l) (thread := h) (Nat.le_refl 2) (by decide)
    a.checkpoint
    (correctionRescaleFrame_next p l h batch (laneOf l h))
  let b : OpeningTripCursor l X h 8447 (rescaleLaneFrame p l h batch 1) :=
    ⟨a.pos,a.before,v,a.ending,a.positive,a.bounded,a.released,ht,
      a.recorded,a.remaining,a.localSteps.trans hv⟩
  let lane : OpeningTripCursor l X (warpLane l h (laneOf l h)) 8447
      (rescaleLaneFrame p l h batch 1) :=
    self.symm ▸ b
  have move {x y} (e : x = y) {pc F} (u : OpeningTripCursor l X x pc F) :
      (e ▸ u : OpeningTripCursor l X y pc F).pos = u.pos := by cases e; rfl
  have pos : lane.pos = a.pos := move self.symm b
  obtain ⟨credit,d,hd⟩ := firstTerminalOfRescaleExit hp hMax (self.symm ▸ hs.1.2.1) lane
  rw [pos,self] at credit
  exact ⟨credit,d,hd.trans (congrArg (·+1) pos)⟩

/-- The terminal statistics waits retain one common vote and tensor ordinal
even when the earlier rescale votes selected different paths in different rounds. -/
structure RescaleWarpTerminal (p : Params) (l : Launch) (X : Execution) (g batch : Nat)
    (votes tensor : Nat) where
  lane : ∀ h, SameWarp l g h → FirstTerminalStatisticsCursor p l X h batch (laneOf l h)
  rank : ∀ h (hs : SameWarp l g h),
    ((X.tr h).take (lane h hs).index).countP isTcColl = tensor ∧
    ((X.tr h).take (lane h hs).index).countP isFullWarpVote = votes

theorem RescaleWarpReturned.terminalWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch ord rank : Nat} {gen : Fin 2 → Nat}
    (c : RescaleWarpReturned p l X g batch 2 1 gen ord rank) :
    Nonempty (RescaleWarpTerminal p l X g batch ord rank) := by
  classical
  have each (h : Nat) (hs : SameWarp l g h) := c.terminal hp hMax hs
  choose d pos using fun h hs => (each h hs).2
  refine ⟨⟨d,?_⟩⟩
  intro h hs
  obtain ⟨_,he⟩ := (each h hs).1
  rw [pos,countP_take_succ_false (p := isTcColl) he rfl,
    countP_take_succ_false (p := isFullWarpVote) he rfl]
  exact c.rank h hs

end PTX.Kernels.TmlFa4Fwd.Correction
