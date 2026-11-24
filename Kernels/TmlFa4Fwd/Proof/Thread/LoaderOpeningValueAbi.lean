-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue

set_option maxRecDepth 100000 in
private theorem abiCarryCode (p : Params) (l : Launch) (batch head tile : Nat) :
    ((kernel.code.drop 488).take (786-488)).all
      (fun i => loaderPipelineCutOp 488 786 786
        ((primingVAdmissionCarry p l batch head tile).map Prod.fst) i.op) = true := by kernel_rfl

set_option maxRecDepth 15000 in
private theorem abiTailCode :
    (kernel.code.drop 786).all (fun i => Thread.staysPastEvent 786 i.op) = true := by kernel_rfl

private theorem abiTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (786 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem valueAbiCarry {p : Params} {l : Launch} {g batch head tile : Nat}
    {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t)
    (hLo : 488 ≤ s.pc) (hEnd : t.pc = 785) (hShape : RingShape s)
    (hRegs : Holds s.regs (primingVAdmissionCarry p l batch head tile)) :
    Holds t.regs (primingVAdmissionCarry p l batch head tile) := by
  have below {u : TState} {es : List Event}
      (hr : TraceReach kernel Assumptions.all l g u es t) : u.pc < 786 := by
    by_contra! hHigh
    have := Thread.Loader.traceRetainsFloor abiTailCode abiTailSegments hr hHigh
    omega
  induction h with
  | refl => exact hRegs
  | tau ht hTail ih =>
    obtain ⟨hLow,_,hRing,hKeep⟩ := pipelineCutStep (by decide) (by decide)
      ⟨hLo,below (.tau ht hTail)⟩ (abiCarryCode p l batch head tile)
      (.inl ⟨rfl,ht⟩) hShape hRegs
    exact ih hLow hEnd hRing hKeep below
  | event he hTail ih =>
    obtain ⟨hLow,_,hRing,hKeep⟩ := pipelineCutStep (by decide) (by decide)
      ⟨hLo,below (.event he hTail)⟩ (abiCarryCode p l batch head tile)
      (.inr ⟨_,rfl,he⟩) hShape hRegs
    exact ih hLow hEnd hRing hKeep below

/-- The exact V address ABI remains live on the actual path from the selected request
through both the first K packet and the opening V empty acquire. -/
theorem openingValueAbiFromAddresses {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch shStart shEnd votesStart votesEnd : Nat}
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (hRank : shStart < shEnd)
    {endsStart endsEnd : Nat → Option TState}
    (start : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      shStart votesStart endsStart)
    (done : OpeningValueAcquired l X g shEnd votesEnd endsEnd) :
    ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      Holds (done.state lane).regs (primingVAdmissionCarry p l batch co.2 co.1) := by
  intro lane hl
  let co := assignedCoordinates p batch (g/l.block)
  let thread := warpLane l g lane
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have ht := start.checkpoint lane hl
  obtain ⟨_,u,hLocal,hAdmission⟩ := primingVAdmissionWithTripsLane hp (g := thread) hb
    (hHead.trans hp.heads_signed) hTile hl (ht.mono ((holds_append ..).mp ht.2.2.2.2).1)
  have hFrame := ((holds_append ..).mp ((holds_append ..).mp hAdmission.2.2.2.2).1).2
  have hPos : start.pos lane < done.pos lane := by
    by_contra! h
    have hCount := Flow.countP_take_mono Execution.isShfl (X.tr thread) h
    rw [done.ordinals.shfl lane hl,start.ordinals.shfl lane hl] at hCount
    omega
  let whole := (X.tr thread).take (done.pos lane)
  have hTake : whole.take (start.pos lane) = (X.tr thread).take (start.pos lane) := by
    rw [show whole = (X.tr thread).take (done.pos lane) from rfl,List.take_take,
      Nat.min_eq_left hPos.le]
  have hCut : whole = (X.tr thread).take (start.pos lane) ++ whole.drop (start.pos lane) := by
    simpa only [hTake] using (List.take_append_drop (start.pos lane) whole).symm
  have hWhole : Run kernel Assumptions.all l thread {} whole (some (done.before lane)) :=
    done.recorded lane hl
  have hpast := (start.recorded lane hl).after_returned_prefix (hCut ▸ hWhole)
  have hn : whole.drop (start.pos lane) ≠ [] := by
    intro h
    have hz := congrArg List.length h
    have hBound : done.pos lane ≤ (X.tr thread).length := done.bounded lane hl
    simp [whole,List.length_take,Nat.min_eq_left hBound] at hz
    omega
  have hr := hpast.after_local_nonempty ((start.localSteps lane hl).trans hLocal) hn
  have hTrace := hr.returning_reach.append (TraceReach.of_local (done.localSteps lane hl))
  exact valueAbiCarry hTrace (by rw [hAdmission.1]) (done.checkpoint lane hl).1
    (ringShapeOfAt hAdmission) hFrame

end PTX.Kernels.TmlFa4Fwd.Loader
