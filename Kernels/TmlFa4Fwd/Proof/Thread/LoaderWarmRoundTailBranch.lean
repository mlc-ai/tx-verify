-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailDone
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundHead
import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- Whether a loader warp skips the optional tail Bias block: warp 15 always does, and warp 14
does unless the tile has more than ten trips and an odd residual Bias half. -/
def warmTailSkips (p : Params) (l : Launch) (g batch : Nat) : Bool :=
  let co := assignedCoordinates p batch (g/l.block)
  decide (warpIndex l g ≠ 14) ||
    !(decide (10 < Mma.trips p batch co.1) && warmResidueFlag (vPrimingResidual p batch co.1))

private theorem tailSelectSeg {l : Launch} {t w : Nat} (hw : w = 14 ∨ w = 15) (b : Bool) :
    Seg kernel [] l t 3 1355 [(1062,b32 w),(7,.pred b)] 1358
      [(202,.pred (decide (w ≠ 14) || !b))] := by
  rcases hw with rfl | rfl <;> cases b <;> intro a ha <;> seg_fp ha using rfl

set_option maxRecDepth 4096 in
/-- From the warm exit, the steady counter starts at the number of warm rounds and the warp
either skips the tail Bias block or enters it. -/
theorem warmTailBranchLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch lane : Nat} (hw : 14 ≤ warpIndex l g)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 < 2^31)
    {s : TState}
    (hs : At s 1353 (warmCacheHeadFrame l (warmRounds p l g batch)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
      (warmRoundCarry p l g batch (warmRounds p l g batch) lane))) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) s u ∧
      At u (if warmTailSkips p l g batch then 1384 else 1359) (warmTailFrame p l g batch lane) := by
  let t := warpLane l g lane
  let co := assignedCoordinates p batch (g/l.block)
  let T := Mma.trips p batch co.1-1
  let W := warmRounds p l g batch
  let C := warmRoundCarry p l g batch W lane
  let F := drainCarry l (cacheUseOfRound W) ++ C
  have hParts := (holds_append ..).mp hs.2.2.2.2
  have hIn : At s 1353 ([(1091,b32 T)] ++ F) :=
    hs.mono ((holds_append ..).mpr ⟨⟨hParts.1.2.1,trivial⟩,
      (holds_append ..).mpr ⟨hParts.1.2.2,hParts.2⟩⟩)
  obtain ⟨v,hv,hV⟩ := roundStraightFrame (F := F) (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (loaderSteadyCounterInitCore (l := l) (g := t) hTrip) hIn
  have hFrame : At v 1355 (warmTailFrame p l g batch lane) := hV
  have hC : Holds v.regs C := ((holds_append ..).mp hFrame.2.2.2.2).2
  have hWarp : v.regs 1062 = some (b32 (warpIndex l g)) :=
    holds_mem hC (by simp [C,warmRoundCarry,openingWarmFrame,warmStartFrame])
  let b := decide (10 < Mma.trips p batch co.1) && warmResidueFlag (vPrimingResidual p batch co.1)
  have hSeven : v.regs 7 = some (.pred b) :=
    holds_mem hC (by simp [C,warmRoundCarry,b,co])
  have hw' : warpIndex l g = 14 ∨ warpIndex l g = 15 := by
    have := warpIndex_lt hp g
    omega
  obtain ⟨u,hu,hU⟩ := roundStraightFrame (F := warmTailFrame p l g batch lane) (by decide)
    (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (tailSelectSeg (l := l) (t := t) hw' b)
    (hFrame.mono ⟨hWarp,hSeven,hFrame.2.2.2.2⟩)
  obtain ⟨w,hwRun,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t)
    Flow.code_1358 (decide (warpIndex l g ≠ 14) || !b) hU hU.2.2.2.2.1 (by simp)
  have hwAll := (loaderLinear (regs := []) (by decide) (by decide) hU.1
    (by simp) (by decide) hwRun).1
  refine ⟨w,(run_rtg hv).trans ((run_rtg hu).trans (run_rtg hwAll)),hW.mono hW.2.2.2.2.2⟩

/-- A warp that skips the tail Bias block reaches the steady counter gate with the warm exit's
rank. -/
theorem WarmRoundsDone.tailSkipOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch : Nat} (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSkip : warmTailSkips p l g batch = true) (d : WarmRoundsDone p l X g batch) :
    Nonempty (WarmTailDone p l X g batch) := by
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  obtain ⟨u⟩ := d.reached.advanceLocal (pc' := 1384) (G := warmTailFrame p l g batch)
    (fun lane hl => by
      obtain ⟨w,hw',hW⟩ := warmTailBranchLocal hp hw (by omega)
        (d.reached.checkpoint lane hl)
      rw [hSkip] at hW
      exact ⟨w,hw',hW⟩)
  exact ⟨⟨d.shuffles,d.votes,d.ends,u,d.rank⟩⟩

/-- A warp that runs the tail Bias block enters it at pc 1359 with the warm exit's
positions. -/
theorem WarmRoundsDone.tailBiasEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch : Nat} (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSkip : warmTailSkips p l g batch = false) (d : WarmRoundsDone p l X g batch) :
    ∃ cur : SchedulerWarpReached l X g 1359 (warmTailFrame p l g batch) d.shuffles d.votes
      d.ends, cur.pos = d.reached.pos := by
  have hCount := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  exact d.reached.advanceLocalWithPosition (pc' := 1359) (G := warmTailFrame p l g batch)
    (fun lane hl => by
      obtain ⟨w,hw',hW⟩ := warmTailBranchLocal hp hw (by omega)
        (d.reached.checkpoint lane hl)
      rw [hSkip] at hW
      exact ⟨w,hw',hW⟩)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
