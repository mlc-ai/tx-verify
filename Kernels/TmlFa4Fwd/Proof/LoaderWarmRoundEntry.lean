-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmIterationCursor
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmFirstObserved

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- A within-warm observation can name a round by its ordinal. A reached later
phase also certifies all warm rounds below the launch's actual warm bound. -/
def WarmRoundDemand (p : Params) (l : Launch) (X : Execution) (g lane batch round j : Nat)
    (e : Event) : Prop :=
  (round < min (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1) 9 ∨
    e.pc < 1353) ∧
  (1348 ≤ e.pc ∨ primingSearchShuffleCount batch + 64 + 64 * round <
    ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl)

set_option maxRecDepth 100000 in
/-- A recorded event of a warm traversal exposes that round's actual loop-entry state. -/
theorem warmRoundEntryOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 917 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    iteration < min (trips - 1) 9 ∧ iteration ≤ trips - 2 ∧ 128 * (trips - 2) + 127 < 2 ^ 31 ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 917 ([(7174, b32 iteration), (1116, b32 (trips - 2))] ++
          warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64 * iteration := by
  have hWarm : e.pc < 1353 ∨ HasWarmTile p l g := by
    rcases hDemand.1 with hBound | hEarly
    · refine .inr ⟨batch, hb, hLo, hHi, ?_⟩
      have hLimit := hBound.trans_le (Nat.min_le_left _ _)
      omega
    · exact .inl hEarly
  obtain ⟨b, hb', hlo, hhi, hTwo, index, hBefore, s, ending, hs, hr, hsRank⟩ :=
    warmFirstIterationOfEventRanked hp hX hg hw hl writes hCTA he hPc hWarm hSafe
  obtain ⟨_, _, only⟩ := tileBatch_existsUnique p hCTA
  have same : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let F := (1116, b32 (trips - 2)) :: warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by
    simp [F, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by
    simp [F, warmStartFrame, hWarp]
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrips
  have hLen := (hp.lengths batch hb).2.2
  have hTileBound : 128 * (trips - 2) + 127 < 2 ^ 31 := by omega
  have hLimit : trips - 1 < 2 ^ 31 := by omega
  change 2 ≤ trips at hTwo
  have hInitial : 0 < min (trips - 1) 9 := by omega
  have hStart : At s 917 ([(7174, b32 0), (1091, b32 (trips - 1))] ++ F) :=
    hs.mono ⟨hs.2.2.2.2.1, holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2.2⟩
  have hBody (n : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true := by kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    kernel_rfl
  obtain ⟨pos, hOrder, t, stop, hIter, ht, htRun, htRank⟩ :=
    warmObservedIterations (hops := iteration) warp hLimit hInitial hShared hRole hBody hTail
      hStart hr he hBefore
      (hDemand.1.imp_left (fun h => by simpa only [Nat.zero_add] using h)) hSafe
      (hDemand.2.imp_right (fun h => by rw [hsRank]; exact h))
  simp only [Nat.zero_add] at hIter ht
  change iteration < min (trips - 1) 9 at hIter
  have hBelow : iteration < trips - 1 := hIter.trans_le (Nat.min_le_left _ _)
  have hLe : iteration ≤ trips - 2 := by omega
  refine ⟨hIter, hLe, hTileBound, pos, hOrder, t, stop, ?_, htRun, ?_⟩
  · exact ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩
  · exact htRank.trans (congrArg (· + 64 * iteration) hsRank)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g lane j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {e : Event}
    (he : X.get (warpLane l g lane, j) = some e)
include hp hX hg hw hl writes hCTA he

set_option maxRecDepth 100000 in
/-- The selected request's real control flow classifies the round of a recorded
body event and its exact shuffle ordinal within that round. -/
theorem actualWarmEventCheckpoint (hPc : 917 ≤ e.pc ∧ e.pc < 1348) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ iteration < min (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1) 9,
        (((X.tr (warpLane l g lane)).take j).countP Execution.isShfl +
          loaderShuffleTail 1348 e.pc =
            primingSearchShuffleCount batch + 64 + 64 * iteration + 64) ∧
        let co := assignedCoordinates p batch (g / l.block)
        let thread := warpLane l g lane
        let trips := Mma.trips p batch co.1
        ∃ pos ≤ j, ∃ u stop,
          At u 917 ([(7174, b32 iteration), (1116, b32 (trips - 2))] ++
            warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)) ∧
          Run kernel Assumptions.all l thread u ((X.tr thread).drop pos) stop ∧
          ((X.tr thread).take pos).countP Execution.isShfl =
            primingSearchShuffleCount batch + 64 + 64 * iteration := by
  obtain ⟨batch, hb, hLo, hHi, hTwo, index, hBefore, s, ending, hs, hr, hsRank⟩ :=
    warmFirstIterationOfEventRanked hp hX hg hw hl writes hCTA he hPc.1 (.inl (by omega)) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let F := (1116, b32 (trips - 2)) :: warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by simp [F, warmStartFrame, hWarp]
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrips
  have hLen := (hp.lengths batch hb).2.2
  have hLimit : trips - 1 < 2 ^ 31 := by omega
  change 2 ≤ trips at hTwo
  have hInitial : 0 < min (trips - 1) 9 := by omega
  have hStart : At s 917 ([(7174, b32 0), (1091, b32 (trips - 1))] ++ F) :=
    hs.mono ⟨hs.2.2.2.2.1, holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2.2⟩
  have hBody (n : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true := by kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    kernel_rfl
  obtain ⟨iteration, _, hIter, hRank, sz, hSz, u, stop, hU, hRun, hRankStart⟩ :=
    warmCheckpointOfObservedEvent warp hLimit hInitial hShared hRole hBody hTail
      hStart hr he hBefore hPc.2 hSafe
  refine ⟨batch, hb, hLo, hHi, iteration, hIter, ?_, sz, hSz, u, stop, ?_, hRun, ?_⟩
  · simpa only [hsRank, Nat.sub_zero] using hRank
  · exact hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.2⟩
  · simpa only [hsRank, Nat.sub_zero] using hRankStart

/-- The shuffle ordinal of the actual warm traversal containing this observation. -/
theorem actualWarmEventRound (hPc : 917 ≤ e.pc ∧ e.pc < 1348) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ iteration < min (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1) 9,
        ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl +
          loaderShuffleTail 1348 e.pc =
            primingSearchShuffleCount batch + 64 + 64 * iteration + 64 := by
  obtain ⟨batch, hb, hLo, hHi, iteration, hIter, hRank, _⟩ :=
    actualWarmEventCheckpoint hp hX hg hw hl writes hCTA he hPc hSafe
  exact ⟨batch, hb, hLo, hHi, iteration, hIter, hRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
