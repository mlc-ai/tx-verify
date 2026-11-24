-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.WarpFollows
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.Determinism
public import Lemmas.Register.RegisterFrame
public import Lemmas.Flow.Scalars
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.ReadValue
public import Lemmas.Flow.ContinuingEvent
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.TauFrame
public import Lemmas.Step.WarpVote
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Lemmas.Flow.Local
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Step.WarpShfl
public import Kernels.TmlFa4Fwd.Proof.CuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Proof.PrologueScheduler
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerCoordinates
public import Kernels.TmlFa4Fwd.Proof.SchedulerFrame
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionPath
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads
public import Kernels.TmlFa4Fwd.Proof.SchedulerStartWord

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A warp's actual trace suffixes together with a common decoded scheduler checkpoint. -/
structure SchedulerWarpAt (l : Launch) (X : Execution) (g pc : Nat)
    (facts : Nat → List (Nat × Value)) (shuffles votes : Nat)
    (ends : Nat → Option TState := fun _ => none) where
  pos : Nat → Nat
  before : Nat → TState
  state : Nat → TState
  ordinals : WarpOrdinals l X g pos shuffles votes
  continuation : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) (before lane)
    ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane)
  localSteps : ∀ lane < 32,
    Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane))
      (before lane) (state lane)
  checkpoint : ∀ lane < 32, At (state lane) pc (facts lane)

section
variable {l : Launch} {X : Execution} {g pc pc' shuffles votes : Nat}
    {F G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g pc F shuffles votes ends)
    (hStep : ∀ lane < 32, ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (cur.state lane) u ∧
        At u pc' (G lane))
include cur hStep

/-- Perform decoded local steps in each lane while keeping the trace positions unchanged. -/
theorem SchedulerWarpAt.advanceLocalPreserving :
    ∃ next : SchedulerWarpAt l X g pc' G shuffles votes ends, next.pos = cur.pos ∧
      next.before = cur.before := by
  have hStep' (lane : Nat) : ∃ u, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (cur.state lane) u ∧
        At u pc' (G lane) := by
    by_cases hl : lane < 32
    · obtain ⟨u, hu, hU⟩ := hStep lane hl
      exact ⟨u, fun _ => ⟨hu, hU⟩⟩
    · exact ⟨cur.state lane, fun hh => False.elim (hl hh)⟩
  choose u h using hStep'
  exact ⟨⟨cur.pos, cur.before, u, cur.ordinals, cur.continuation,
    fun lane hl => (cur.localSteps lane hl).trans (h lane hl).1,
    fun lane hl => (h lane hl).2⟩, rfl, rfl⟩

/-- Perform decoded local steps while keeping the trace positions unchanged. -/
theorem SchedulerWarpAt.advanceLocalAt :
    ∃ next : SchedulerWarpAt l X g pc' G shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := cur.advanceLocalPreserving hStep
  exact ⟨next,hPos⟩

/-- Perform decoded local steps in each lane while keeping the trace positions unchanged. -/
theorem SchedulerWarpAt.advanceLocal :
    Nonempty (SchedulerWarpAt l X g pc' G shuffles votes ends) := by
  obtain ⟨next, _⟩ := cur.advanceLocalAt hStep
  exact ⟨next⟩
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pc shuffles votes dst : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g pc F shuffles votes ends) (mode : ShflMode) (a : Nat → Value)
    (b c : Nat → Nat) (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst)
    (hOut : ∀ lane < 32,
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl mode (a lane) (b lane) (c lane)
          (fun v _ => next (setReg (cur.state lane) dst v))))
include hp hX hg cur mode a b c hFresh hOut

/-- Consume a shuffle in each lane's actual suffix and keep its observed source word. -/
theorem SchedulerWarpAt.consumeShufflePresent
    (hSuffix : ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ []) :
    ∃ result : SchedulerWarpAt l X g (pc + 1)
        (fun lane => (dst, a (shflSource mode lane (b lane) (c lane)).1) :: F lane)
        (shuffles + 1) votes ends,
      result.pos = (fun lane => cur.pos lane + 1) ∧
      ∃ (recv : Nat → Value) (ok : Nat → Bool), ∀ lane < 32,
        X.get (warpLane l g lane, cur.pos lane) =
          some ⟨pc, .shfl mode (a lane) (b lane) (c lane) (recv lane) (ok lane)⟩ ∧
        result.before lane = next (setReg (cur.state lane) dst (recv lane)) := by
  let thread := warpLane l g
  let after := fun lane v => next (setReg (cur.state lane) dst v)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (thread lane) (cur.before lane) (cur.state lane)
        (.shfl mode (a lane) (b lane) (c lane) (fun v _ => after lane v)) :=
    ⟨cur.localSteps lane hl, hOut lane hl⟩
  have hEvent (lane : Nat) (hl : lane < 32) : ∃ recv ok,
      X.get (thread lane, cur.pos lane) = some ⟨pc, .shfl mode (a lane) (b lane) (c lane) recv ok⟩ ∧
        Run kernel Assumptions.all l (thread lane) (after lane recv)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    obtain ⟨recv, ok, he, _, hRun⟩ := (hNext lane hl).shuffle_at_nonempty
      (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.shfl lane hl)
    rw [(cur.checkpoint lane hl).1] at he
    exact ⟨recv, ok, he, hRun⟩
  have hEvent' (lane : Nat) : ∃ recv ok, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨pc, .shfl mode (a lane) (b lane) (c lane) recv ok⟩ ∧
        Run kernel Assumptions.all l (thread lane) (after lane recv)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨recv, ok, he, hr⟩ := hEvent lane hl
      exact ⟨recv, ok, fun _ => ⟨he, hr⟩⟩
    · exact ⟨b32 0, false, fun hh => False.elim (hl hh)⟩
  choose recv ok h using hEvent'
  have hObserve := fun lane hl => (h lane hl).1
  have hRun := fun lane hl => (h lane hl).2
  have hOrd := (cur.ordinals.shuffle (fun _ => pc) mode a recv b c ok hObserve).2
  have hValue := cur.ordinals.shuffle_value hX hBlock hg (fun _ => pc) mode a recv b c ok hObserve
  refine ⟨⟨fun lane => cur.pos lane + 1, fun lane => after lane (recv lane),
    fun lane => after lane (recv lane), hOrd, hRun, fun _ _ => .refl, ?_⟩,
    rfl, recv, ok, fun lane hl => ⟨hObserve lane hl, rfl⟩⟩
  · intro lane hl
    have ht := (cur.checkpoint lane hl).set (v := recv lane) (hFresh lane hl)
    simpa only [(hValue lane hl).1] using ht

/-- Record the shuffle consumed by each lane while preserving the target suffix. -/
theorem SchedulerWarpAt.consumeShuffleToRecorded {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : pc < target.pc) :
    ∃ result : SchedulerWarpAt l X g (pc + 1)
        (fun lane => (dst, a (shflSource mode lane (b lane) (c lane)).1) :: F lane)
        (shuffles + 1) votes ends,
      result.pos = (fun lane => cur.pos lane + 1) ∧
      (∀ lane < 32, ∃ recv ok, X.get (warpLane l g lane, cur.pos lane) =
        some ⟨pc, .shfl mode (a lane) (b lane) (c lane) recv ok⟩) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target) := by
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSuffix : ∀ lane < 32, (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with he | hw
    · intro lane hl hNil
      have hr := cur.continuation lane hl
      rw [hNil, he lane hl] at hr
      cases hr
    · exact hw.shuffleSuffix hX cur.ordinals hBlock hg
        ⟨cur.localSteps src hw.lane, hOut src hw.lane⟩ (cur.continuation src hw.lane)
  obtain ⟨result, hPos, recv, ok, hEvent⟩ :=
    cur.consumeShufflePresent hp hX hg mode a b c hFresh hOut hSuffix
  refine ⟨result,hPos,fun lane hl => ⟨recv lane,ok lane,(hEvent lane hl).1⟩,fun h => ?_⟩
  rw [hPos]
  exact h.afterShuffle hX hBlock hg hPc mode a recv b c ok (fun lane hl => (hEvent lane hl).1)

/-- Consume a shuffle while preserving the target's position in the suffix. -/
theorem SchedulerWarpAt.consumeShuffleTo {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : pc < target.pc) :
    ∃ result : SchedulerWarpAt l X g (pc + 1)
        (fun lane => (dst, a (shflSource mode lane (b lane) (c lane)).1) :: F lane)
        (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  obtain ⟨result,_,_,hFollow⟩ :=
    cur.consumeShuffleToRecorded hp hX hg mode a b c hFresh hOut hProgress hPc
  exact ⟨result,hFollow⟩
end

/-- Consume a shuffle in each lane's actual suffix and keep its observed source word. -/
theorem SchedulerWarpAt.consumeShuffle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pc shuffles votes dst : Nat} (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g pc F shuffles votes) (mode : ShflMode)
    (a : Nat → Value) (b c : Nat → Nat)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst)
    (hOut : ∀ lane < 32,
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl mode (a lane) (b lane) (c lane)
          (fun v _ => next (setReg (cur.state lane) dst v)))) :
    Nonempty (SchedulerWarpAt l X g (pc + 1)
      (fun lane => (dst, a (shflSource mode lane (b lane) (c lane)).1) :: F lane)
      (shuffles + 1) votes) := by
  obtain ⟨result, _⟩ := cur.consumeShuffleTo hp hX hg mode a b c hFresh hOut
    (src := 0) (index := 0) (target := ⟨pc + 1, .exit⟩) (.inl (fun _ _ => rfl)) (Nat.lt_succ_self _)
  exact ⟨result⟩

variable {p : Params} {l : Launch} {m : Mem0}

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
