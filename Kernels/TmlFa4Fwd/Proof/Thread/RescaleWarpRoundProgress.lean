-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpVisitProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleLoopExitProgress
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The remaining counter and both banks of row addresses in this lane. -/
def rescaleLaneFrame (p : Params) (l : Launch) (h batch blocks : Nat) :=
  rescaleLoopFacts (correctionRescaleFrame p l h batch) blocks (laneOf l h)

theorem rescaleLaneFrame_visit {p : Params} {l : Launch} {h : Nat} (hh : h < l.threads)
    (batch blocks : Nat) (stage : Fin 2) :
    RescaleVisitFrame l h stage (rescaleLaneFrame p l h batch blocks) := by
  have self : warpLane l h (laneOf l h) = h := Step.warpLane_of_sameWarp ⟨⟨hh,hh,rfl⟩,rfl⟩
  have f := correctionRescaleFrame_visit p l h batch blocks (laneOf l h) stage
  rwa [self] at f

/-- A warp at a rescale rendezvous, including both statistics generations. -/
structure RescaleWarpJoin (p : Params) (l : Launch) (X : Execution) (g batch blocks : Nat)
    (stage : Fin 2) (generation : Fin 2 → Nat) (votes tensor : Nat) where
  lane : ∀ h, SameWarp l g h → RescaleWaitReached l X h stage (rescaleLaneFrame p l h batch blocks)
  rank : ∀ h (hs : SameWarp l g h),
    ((X.tr h).take (lane h hs).index).countP isTcColl = tensor ∧
    ((X.tr h).take (lane h hs).index).countP isFullWarpVote = votes
  named : ∀ h (hs : SameWarp l g h) s, Thread.observedBarrierOrdinal X (h,(lane h hs).index)
    (statsBarrierId l h s) = generation s

/-- After the warp's two slot notifications, its next stage can use the
updated collective ordinals and the same counter and row addresses. -/
structure RescaleWarpReturned (p : Params) (l : Launch) (X : Execution) (g batch blocks : Nat)
    (stage : Fin 2) (generation : Fin 2 → Nat) (votes tensor : Nat) where
  lane : ∀ h, SameWarp l g h → OpeningTripCursor l X h (rescaleSignalPc stage+3)
    (rescaleLaneFrame p l h batch blocks)
  credits : ∀ h (hs : SameWarp l g h), X.Arrive (h,(lane h hs).pos-2)
      (creditLoc l h stage) 0 1 true .cta ∧
    X.Arrive (h,(lane h hs).pos-1) (rescaleReuseLoc l h stage) 0 1 true .cta
  rank : ∀ h (hs : SameWarp l g h), ((X.tr h).take (lane h hs).pos).countP isTcColl = tensor ∧
    ((X.tr h).take (lane h hs).pos).countP isFullWarpVote = votes
  named : ∀ h (hs : SameWarp l g h) s, Thread.observedBarrierOrdinal X (h,(lane h hs).pos)
    (statsBarrierId l h s) = generation s

def rescaleNextGeneration (counts : Fin 2 → Nat) (stage s : Fin 2) :=
  counts s + (if s = stage then 1 else 0)

theorem RescaleWarpJoin.returnOfRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch blocks ord rank : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    {stage : Fin 2} {gen : Fin 2 → Nat}
    (c : RescaleWarpJoin p l X g batch blocks stage gen ord rank)
    (release : ∀ h (hs : SameWarp l g h), (c.lane h hs).index+1 = (X.tr h).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Y.MemWrites = X.MemWrites ∧ Step.Released l Y h) :
    ∃ n, (n = 0 ∨ n = 25) ∧ Nonempty (RescaleWarpReturned p l X g batch blocks stage
      (rescaleNextGeneration gen stage) (ord+1) (rank+n)) := by
  classical
  obtain ⟨n,hn,all⟩ := rescaleWarpVisitOfRelease hp hMax hFrame hg hw stage
    (fun h => rescaleLaneFrame p l h batch blocks)
    (fun _ hs => rescaleLaneFrame_visit hs.1.2.1 batch blocks stage) c.lane c.rank release
  choose lane a b tc v named using all
  refine ⟨n,hn,⟨⟨lane,fun h hs => ⟨a h hs,b h hs⟩,fun h hs => ⟨tc h hs,v h hs⟩,?_⟩⟩⟩
  intro h hs s
  have eq : statsBarrierId l h s = statsBarrierId l h stage ↔ s = stage := by
    simp [statsBarrierId,Fin.ext_iff]
  exact (named h hs _).trans (by
    change Thread.observedBarrierOrdinal X (h,(c.lane h hs).index) (statsBarrierId l h s) + _ = _
    rw [c.named h hs s]
    simp only [rescaleNextGeneration,eq])

theorem RescaleWarpReturned.stageOne {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g batch blocks ord rank : Nat}
    {gen : Fin 2 → Nat} (c : RescaleWarpReturned p l X g batch blocks 0 gen ord rank) :
    Nonempty (RescaleWarpJoin p l X g batch blocks 1 gen ord rank) := by
  classical
  have reached (h : Nat) (hs : SameWarp l g h) := rescaleWaitReachedOfMaximal hp hMax hs.1.2.1 1
    (rescaleLaneFrame_visit hs.1.2.1 batch blocks 1) (c.lane h hs)
  choose d pos using reached
  exact ⟨⟨d,fun h hs => by rw [pos]; exact c.rank h hs,
    fun h hs s => by rw [pos]; exact c.named h hs s⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
