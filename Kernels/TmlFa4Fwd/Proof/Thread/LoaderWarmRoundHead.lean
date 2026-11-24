-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCacheLoopProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundUseRank
import all Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import all Kernels.TmlFa4Fwd.Proof.SchedulerFrame
import Kernels.TmlFa4Fwd.Proof.LoaderTransparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (kvUseStage kvEmptyPhase loaderPhaseWord vPrimingResidual warmStartFrame
    primingSearchShuffleCount loaderOutCore loaderLinear)

/-- Warp 14 toggles both Bias phase registers once per warm round. Warp 15 skips the Bias
block and keeps the value seeded by its role test. -/
def warmBiasPhase (warp round : Nat) : Bool :=
  if warp = 14 then decide (round % 2 = 1) else true

/-- The KV tile loaded by warm round `round`. The opening packet loads the last tile and
the warm rounds proceed towards tile zero. -/
def warmRoundTile (p : Params) (l : Launch) (g batch round : Nat) : Nat :=
  Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-2-round

/-- The live registers of a loader lane at the head of warm round `round`. Only the round
counter, the ring cursor and the two Bias phases change between rounds. -/
def warmRoundFrame (p : Params) (l : Launch) (g batch round lane : Nat) : List (Nat × Value) :=
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let residual := vPrimingResidual p batch co.1
  let use := cacheUseOfRound round
  let bias := loaderPhaseWord (warmBiasPhase (warpIndex l g) round)
  [(7174,b32 round),(7178,bias),(7179,b32 (kvUseStage use).val),
    (7180,loaderPhaseWord (kvEmptyPhase use)),
    (1117,b32 (residual/2^31)),(1116,b32 (n-2)),
    (7,.pred (decide (10 < n) && warmResidueFlag residual))] ++
    [(164,.pred (warmResidueFlag residual)),(7177,bias)] ++
    openingWarmFrame p l g batch lane ++ drainSchedulerFrame p l (warpLane l g lane)

theorem warmBiasPhase_zero (warp : Nat) : warmBiasPhase warp 0 = decide (warp ≠ 14) := by
  unfold warmBiasPhase
  by_cases h : warp = 14 <;> simp [h]

/-- The first warm frame is the round-zero instance of the round frame. -/
theorem warmFirstFrame_eq_round (p : Params) (l : Launch) (g batch lane : Nat) :
    warmFirstFrame p l g batch lane = warmRoundFrame p l g batch 0 lane := by
  simp only [warmFirstFrame,warmRoundFrame,openingWarmPublishedFrame,warmBiasPhase_zero,
    cacheUseOfRound]
  rfl

/-- On straight-line loader code, a run of the full model is a run without assumptions. -/
theorem loaderRunWithoutAssumptions {l : Launch} {g n lo len : Nat} {t u : TState}
    (hLo0 : 174 ≤ lo) (hHi0 : lo+len ≤ 1906)
    (hFallthrough : ((kernel.code.drop lo).take (len-1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hRun : run kernel Assumptions.all l g n t = some u) (hLo : lo ≤ t.pc)
    (hHi : t.pc+n ≤ lo+len) : run kernel [] l g n t = some u := by
  induction n generalizing t with
  | zero => exact hRun
  | succ n ih =>
    have hEq : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t := by
      rw [tauStep,loaderOutCore (by omega) (by omega),← tauStep]
    simp only [run,hEq] at hRun ⊢
    cases hStep : tauStep kernel [] l g t with
    | none => simp [hStep] at hRun
    | some v =>
      simp only [hStep,Option.bind_some] at hRun ⊢
      cases n with
      | zero => exact hRun
      | succ n =>
        obtain ⟨ins,hc,hp,_⟩ := tauWrites hStep
        have hs := List.all_eq_true.mp hFallthrough ins (insideSlice hLo (by omega) hc)
        have hv := straightPc hs hp
        exact ih hRun (by omega) (by omega)

section
variable {l : Launch} {g n begin finish : Nat} {A F G : List (Nat × Value)} (hLo : 174 ≤ begin)
    (hHi : begin+n ≤ 1906)
    (hKeep : ((kernel.code.drop begin).take n).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hSeq : ((kernel.code.drop begin).take (n-1)).all (fun i => schedulerFallsThrough i.op) = true)
include hLo hHi hKeep hSeq

/-- A straight-line segment keeps the registers of a frame that it does not write. -/
theorem roundStraightFrame (hCore : Seg kernel [] l g n begin A finish G) {s : TState}
    (hs : At s begin (A++F)) :
    ∃ u, run kernel Assumptions.all l g n s = some u ∧ At u finish (G++F) := by
  have hFields := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u,hu,hU⟩ := hCore s (hs.mono hFields.1)
  obtain ⟨huA,huF⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hKeep hSeq hu
  exact ⟨u,huA,hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,
    holdsSchedulerFrame hFields.2 huF (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

/-- The same frame rule for a segment proved in the full model. -/
theorem roundStraightFrameAll (hCore : Seg kernel Assumptions.all l g n begin A finish G)
    {s : TState} (hs : At s begin (A++F)) :
    ∃ u, run kernel Assumptions.all l g n s = some u ∧ At u finish (G++F) := by
  have hFields := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨u,hu,hU⟩ := hCore s (hs.mono hFields.1)
  have hu' := loaderRunWithoutAssumptions hLo hHi hSeq hu (le_of_eq hs.1.symm)
    (by rw [hs.1])
  obtain ⟨_,huF⟩ := loaderLinear (regs := F.map Prod.fst) hLo hHi hs.1 hKeep hSeq hu'
  exact ⟨u,hu,hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,
    holdsSchedulerFrame hFields.2 huF (fun _ hm => List.mem_map_of_mem hm)⟩)⟩
end

/-- The warp has reached the head of warm round `round`. The shuffle rank records the
priming search, the opening packets and 64 shuffles for each completed warm round. -/
structure WarmRoundHead (p : Params) (l : Launch) (X : Execution) (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 917 (fun lane => warmRoundFrame p l g batch round lane)
    shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+64*round

/-- The first warm cursor with its exact shuffle rank is the head of round zero. -/
def WarmCacheStarted.roundHead {p : Params} {l : Launch} {X : Execution} {g batch : Nat}
    (c : WarmCacheStarted p l X g batch)
    (hRank : c.shuffles = primingSearchShuffleCount batch+64) :
    WarmRoundHead p l X g batch 0 :=
  ⟨c.shuffles,c.votes,c.ends,
    c.reached.reframe ⟨c.reached.pos,c.reached.before,c.reached.state,c.reached.ordinals,
      c.reached.continuation,c.reached.localSteps,fun lane hl => by
        rw [← warmFirstFrame_eq_round]
        exact c.reached.checkpoint lane hl⟩ rfl rfl,
    by rw [hRank]⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
