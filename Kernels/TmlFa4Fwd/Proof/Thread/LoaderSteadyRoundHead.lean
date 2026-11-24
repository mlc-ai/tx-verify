-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailDone
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageSeed
import all Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageSeed
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed
import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A register list holds when each of its facts is a member of a list that holds. -/
theorem steadyHoldsOfSubset {R : Nat → Option Value} {L : List (Nat × Value)}
    (h : Holds R L) : ∀ {M : List (Nat × Value)}, (∀ x ∈ M, x ∈ L) → Holds R M
  | [], _ => trivial
  | _ :: _, hM => ⟨holds_mem h (hM _ (List.mem_cons_self ..)),
      steadyHoldsOfSubset h (fun x hx => hM x (List.mem_cons_of_mem _ hx))⟩

/-- The registers that every steady round passes unchanged to the next round. The steady
prelude adds the lane row offset, the lane column in two widths, the lane's row within its
group of eight, and the selected page-table row. The warm carry keeps the Bias phases of
the last warm round. -/
def steadyRoundCarry (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  let tid := warpLane l g lane%l.block
  [(2130,b32 (primingLaneRow 0 tid)),(1147,b32 (8*(tid%8))),(1146,b32 (tid/8%8)),
    (7781,b64 (16*(tid%8))),(7763,b64 (p.pageTableBase+4*(batch*p.pageTableStride)))] ++
    warmRoundCarry p l g batch (warmRounds p l g batch) lane

/-- The warp has reached the head of steady round `round` at pc 1396. The round counter is
`round`, the ring cursor is the K use of the round, and the shuffle rank counts 64 shuffles
for each earlier warm or steady round. -/
structure SteadyRoundHead (p : Params) (l : Launch) (X : Execution) (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SteadyCacheHead l X g round
    (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (steadyRoundCarry p l g batch) shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+64+64*round

set_option maxRecDepth 4096 in
/-- When steady rounds remain after the warm rounds, the warp passes the steady counter gate
and the one-time steady prelude and reaches the head of the first steady round. -/
theorem WarmTailDone.steadyHead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hLong : warmRounds p l g batch <
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    (d : WarmTailDone p l X g batch) :
    Nonempty (SteadyRoundHead p l X g batch (warmRounds p l g batch)) := by
  let n := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  let wr := warmRounds p l g batch
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hCount := (Mma.trips_bounds hp hb hTile).2.1
  have hLen := (hp.lengths batch hb).2.2
  have hQ : 0 < p.qLength batch := by omega
  have hTrip : n-1 < 2^31 := by omega
  have hWr : wr < 2^31 := by
    have : wr ≤ 9 := Nat.min_le_right _ _
    omega
  obtain ⟨u⟩ := d.reached.advanceLocal (pc' := 1396)
      (G := fun lane => steadyCacheHeadFrame l wr (n-1) (steadyRoundCarry p l g batch lane)) (by
    intro lane hl
    let t := warpLane l g lane
    let tid := t%l.block
    let D := drainCarry l (cacheUseOfRound wr) ++ warmRoundCarry p l g batch wr lane
    have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
    have hs : At (d.reached.state lane) 1384 ([(7181,b32 wr),(1091,b32 (n-1))] ++ D) :=
      d.reached.checkpoint lane hl
    obtain ⟨a,ha,hA⟩ := loaderSteadyCounterGateWithFrame (l := l) (g := t) (F := D) hTrip hWr
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) _ hs
    rw [ite_eq_left hLong] at hA
    let E := [(7181,b32 wr),(1091,b32 (n-1))] ++ D
    have hA' : At a 1386 ([(1061,b32 tid)] ++ E) :=
      hA.mono ⟨holds_mem hA.2.2.2.2 (by simp [D,warmRoundCarry,openingWarmFrame,
        warmStartFrame,warmPageRoots,warmLaneRoots,tid,t]),hA.2.2.2.2⟩
    obtain ⟨b,hbRun,hB⟩ := roundStraightFrame (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (show Seg kernel [] l t 5 1386 [(1061,b32 tid)] 1391
        [(2130,b32 (primingLaneRow 0 tid)),(1147,b32 (8*(tid%8))),(1146,b32 (tid/8%8))] from
        recurringLaneOffsetWithColumnAndRowCore hTid 1) hA'
    let E' := [(2130,b32 (primingLaneRow 0 tid)),(1147,b32 (8*(tid%8))),
      (1146,b32 (tid/8%8))] ++ E
    have hB' : At b 1391 ([(7170,b32 batch),(7505,b64 p.pageTableStride),
        (7504,b64 p.pageTableBase),(1147,b32 (8*(tid%8)))] ++ E') := by
      refine hB.mono ⟨holds_mem hB.2.2.2.2 ?_,holds_mem hB.2.2.2.2 ?_,
        holds_mem hB.2.2.2.2 ?_,holds_mem hB.2.2.2.2 ?_,hB.2.2.2.2⟩ <;>
        simp [E,D,warmRoundCarry,openingWarmFrame,warmStartFrame,warmPageRoots,warmLaneRoots]
    obtain ⟨c,hcRun,hC⟩ := roundStraightFrame (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (steadyPageBaseCore (l := l) (g := t) (tid := tid) hp hb hQ) hB'
    refine ⟨c,run_rtg (run_comp ha (run_comp hbRun hcRun)),hC.mono ?_⟩
    apply steadyHoldsOfSubset hC.2.2.2.2
    intro x hx
    have hx' : (x ∈ [(7181,b32 wr),(1091,b32 (n-1))] ∨ x ∈ drainCarry l (cacheUseOfRound wr)) ∨
        (x ∈ [(2130,b32 (primingLaneRow 0 tid)),(1147,b32 (8*(tid%8))),(1146,b32 (tid/8%8)),
          (7781,b64 (16*(tid%8))),(7763,b64 (p.pageTableBase+4*(batch*p.pageTableStride)))] ∨
        x ∈ warmRoundCarry p l g batch wr lane) := by
      simpa only [steadyCacheHeadFrame,steadyRoundCarry,List.mem_append] using hx
    show x ∈ [(7763,b64 (p.pageTableBase+4*(batch*p.pageTableStride))),
      (7781,b64 (16*(tid%8)))] ++ ([(2130,b32 (primingLaneRow 0 tid)),(1147,b32 (8*(tid%8))),
      (1146,b32 (tid/8%8))] ++ ([(7181,b32 wr),(1091,b32 (n-1))] ++
      (drainCarry l (cacheUseOfRound wr) ++ warmRoundCarry p l g batch wr lane)))
    simp only [List.mem_append]
    rcases hx' with (hx | hx) | (hx | hx)
    · exact .inr (.inr (.inl hx))
    · exact .inr (.inr (.inr (.inl hx)))
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
    · exact .inr (.inr (.inr (.inr hx))))
  exact ⟨⟨d.shuffles,d.votes,d.ends,u,d.rank⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
