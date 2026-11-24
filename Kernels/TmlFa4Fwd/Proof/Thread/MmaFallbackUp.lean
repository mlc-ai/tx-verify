-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackTileCount
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackScan
import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue Mma

def fallbackScanFrame (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  fallbackScanPredicates (laneOf l g) ++
    (7196, b32 (groupLaneTiles p first (laneOf l g))) :: fallbackReadFrame p l g first

def fallbackUpFacts (p : Params) (l : Launch) (g first round : Nat) : List (Nat × Value) :=
  (fallbackRoundReg round, b32 (prefixWindow (groupLaneTiles p first) (2 ^ round) (laneOf l g))) ::
    fallbackScanFrame p l g first

private def fallbackUpRegs : List Nat :=
  [355, 356, 357, 358, 359, 7196, 1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139,
    2535, 7502, 7506, 7503]

private theorem prepareFallbackUp {l : Launch} {p : Params} {g first : Nat} {t : TState}
    (ht : At t 2017 ((7196, b32 (groupLaneTiles p first (laneOf l g))) ::
      fallbackReadFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (fallbackRoundPc 0) (fallbackUpFacts p l g first 0) := by
  obtain ⟨u, hu, hU⟩ := initializeFallbackPredicates l g (Nat.mod_lt _ (by decide)) t
    (by at_select ht)
  have hWrites : ((kernel.code.drop 2017).take 5).all
      (fun i => ((7196 :: [1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139, 2535,
        7502, 7506, 7503]).all fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
  have hStraight : ((kernel.code.drop 2017).take 4).all
      (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
  have hKeep := holdsSchedulerFrame ht.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hu ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u, run_rtg (localRun (pc := 2017) (n := 5) (by decide) (by decide)
    ht.1 hStraight hu), hU.mono ?_⟩
  refine ⟨?_, (holds_append _ _ _).mpr ⟨hU.2.2.2.2, hKeep⟩⟩
  simpa only [fallbackRoundReg, ↓reduceIte, pow_zero, prefixWindow_one] using hKeep.1

private theorem fallbackUpSafety : ∀ stage : Fin 5,
    let site := fallbackRoundPc stage.val + 1
    ((kernel.code.drop site).take 2).all
      (fun i => fallbackUpRegs.all (fun r => !(writesRegs i.op).contains r)) = true ∧
    ((kernel.code.drop site).take 1).all (fun i => schedulerFallsThrough i.op) = true := by
  decide +kernel

/-- Replay one actual up exchange and the guarded addition for its prefix window. -/
theorem fallbackUpRoundOfMaximal {l : Launch} {p : Params} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first count : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch) (stage : Fin 5)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h (fallbackRoundPc stage.val) count
      (fallbackUpFacts p l h first stage.val)) :
    Nonempty (FallbackScanCursor l X g (fallbackRoundPc (stage.val + 1)) (count + 1)
      (fallbackUpFacts p l g first (stage.val + 1))) := by
  let lane := laneOf l g
  let part := prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
  have hFresh : ∀ pair ∈ fallbackUpFacts p l g first stage.val,
      pair.1 ≠ fallbackShuffleDst stage := by
    intro pair hPair
    have hReg := List.mem_map_of_mem (f := Prod.fst) hPair
    change pair.1 ∈ fallbackRoundReg stage.val :: fallbackUpRegs at hReg
    have h : ∀ s : Fin 5, fallbackShuffleDst s ∉ fallbackRoundReg s.val :: fallbackUpRegs := by
      decide
    exact fun hEq => h stage (hEq ▸ hReg)
  obtain ⟨read⟩ := FallbackScanCursor.shuffleOfMaximal hp hMax hg .up (2 ^ stage.val) 0
    (fun h => fallbackUpFacts p l h first stage.val) (fun lane => b32 (part lane)) cur
    (fun h hWarp => fallbackUpTemplate hp stage _
      ((cur h hWarp).checkpoint.mono ⟨(cur h hWarp).checkpoint.2.2.2.2.1, trivial⟩)) hFresh
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hSaved : Holds read.state.regs (fallbackScanFrame p l g first) :=
    read.checkpoint.2.2.2.2.2.2
  have hGuard : read.state.regs (359 - stage.val) =
      some (.pred (fallbackRoundGuard stage lane)) :=
    holds_mem hSaved (List.mem_append_left _ (fallbackRoundGuardFact stage lane))
  obtain ⟨u, hu, hU⟩ := fallbackRoundFold stage l g (groupLaneTiles p first) hLane
    (groupPrefixOperands_fit hp hFirst hLane stage) read.state
    (read.checkpoint.mono ⟨hGuard, read.checkpoint.2.2.2.2.2.1,
      read.checkpoint.2.2.2.2.1, trivial⟩)
  have ⟨hWrites, hStraight⟩ := fallbackUpSafety stage
  have hSite := read.checkpoint.1
  have hBound1 : 1904 ≤ fallbackRoundPc stage.val + 1 := by
    have := stage.isLt
    unfold fallbackRoundPc
    omega
  have hBound2 : fallbackRoundPc stage.val + 1 + 2 ≤ 2768 := by
    have := stage.isLt
    unfold fallbackRoundPc
    omega
  have hKeep := holdsSchedulerFrame hSaved
    (fun _ hr => schedulerLocalFrame hWrites hStraight hu hSite.ge (by rw [hSite]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At u (fallbackRoundPc (stage.val + 1))
      (fallbackUpFacts p l g first (stage.val + 1)) :=
    hU.mono ⟨by simpa only [Nat.pow_succ, Nat.mul_comm] using hU.2.2.2.2.1, hKeep⟩
  exact ⟨⟨read.pos, read.before, u, read.lastState, read.pos_pos, read.pos_le, read.shuffleCount,
    read.ballotCount, read.released, hAt, read.runPrefix,
    read.localSteps.trans (run_rtg (localRun hBound1 hBound2 hSite hStraight hu)),
    read.continuation⟩⟩

/-- A maximal fallback scan performs all five exchanges with the launch tile counts. -/
theorem fallbackUpOfMaximal {l : Launch} {p : Params} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first count : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h 2017 count
      ((7196, b32 (groupLaneTiles p first (laneOf l h))) :: fallbackReadFrame p l h first)) :
    Nonempty (FallbackScanCursor l X g 2037 (count + 5) (fallbackUpFacts p l g first 5)) := by
  classical
  have initial : ∀ h, SameWarp l g h → Nonempty (FallbackScanCursor l X h
      (fallbackRoundPc 0) count (fallbackUpFacts p l h first 0)) := by
    intro h hWarp
    let c := cur h hWarp
    obtain ⟨u, hLocal, hU⟩ := prepareFallbackUp c.checkpoint
    exact ⟨⟨c.pos, c.before, u, c.lastState, c.pos_pos, c.pos_le, c.shuffleCount, c.ballotCount,
      c.released, hU, c.runPrefix, c.localSteps.trans hLocal, c.continuation⟩⟩
  have allRounds (r : Nat) (hr : r ≤ 5) (h : Nat) (hw : SameWarp l g h) :
      Nonempty (FallbackScanCursor l X h (fallbackRoundPc r) (count + r)
        (fallbackUpFacts p l h first r)) := by
    induction r generalizing h with
    | zero => exact initial h hw
    | succ r ih =>
      have hs : r < 5 := by omega
      exact fallbackUpRoundOfMaximal hp hMax hw.1.2.1 hFirst ⟨r, hs⟩
        (fun peer hPeer => Classical.choice (ih (by omega) peer (Step.sameWarp_trans hw hPeer)))
  exact allRounds 5 le_rfl g ⟨⟨hg, hg, rfl⟩, rfl⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
