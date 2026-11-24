-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondBiasBoxes
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueProgress
import Lemmas.Flow.RecordedCheckpointPath
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue

set_option maxRecDepth 15000 in
private theorem valueSetupTailCode :
    (kernel.code.drop 780).all (fun i => Thread.staysPastEvent 780 i.op) = true := by kernel_rfl

private theorem valueSetupTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (780 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 15000 in
private theorem valueSetupAfterCode :
    (kernel.code.drop 781).all (fun i => Thread.staysPastEvent 781 i.op) = true := by kernel_rfl

private theorem valueSetupAfterSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (781 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem valueSetupBaseCode (l : Launch) :
    ((kernel.code.drop 673).take (781-673)).all
      (fun i => loaderPipelineCutOp 673 781 781 ((openingValueBase l).map Prod.fst) i.op) =
      true := by kernel_rfl

private theorem valueSetupRetainsFloor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} {floor : Nat}
    (hCode : (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true)
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : floor ≤ s.pc) : floor ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hs (.inr ⟨_,rfl,he⟩))

private theorem valueSetupBase {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u)
    (hLo : 673 ≤ s.pc) (hEnd : u.pc = 780) (hShape : RingShape s)
    (hRegs : Holds s.regs (openingValueBase l)) :
    Holds u.regs (openingValueBase l) := by
  have below {v : TState} {es : List Event}
      (hr : TraceReach kernel Assumptions.all l g v es u) : v.pc < 781 := by
    by_contra! hHigh
    have := valueSetupRetainsFloor valueSetupAfterCode
      valueSetupAfterSegments hr hHigh
    omega
  induction h with
  | refl => exact hRegs
  | tau ht hTail ih =>
    obtain ⟨hLow,_,hRing,hKeep⟩ := pipelineCutStep (F := openingValueBase l)
      (lower := 673) (cut := 781) (branch := 781) (by decide) (by decide)
      ⟨hLo,below (.tau ht hTail)⟩ (valueSetupBaseCode l) (.inl ⟨rfl,ht⟩) hShape hRegs
    exact ih hLow hEnd hRing hKeep below
  | event he hTail ih =>
    obtain ⟨hLow,_,hRing,hKeep⟩ := pipelineCutStep (F := openingValueBase l)
      (lower := 673) (cut := 781) (branch := 781) (by decide) (by decide)
      ⟨hLo,below (.event he hTail)⟩ (valueSetupBaseCode l) (.inr ⟨_,rfl,he⟩) hShape hRegs
    exact ih hLow hEnd hRing hKeep below

/-- The first loader's actual path past the second Bias box retains the V setup bases. -/
theorem openingValueReachedByFirstLoader {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g keyShuffles keyVotes shuffles votes row head : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hSh : 5 ≤ keyShuffles)
    {keyEnds ends : Nat → Option TState}
    (key : PrimingKeyCommitReached l X g keyShuffles keyVotes keyEnds)
    (cur : SchedulerWarpReached l X g 780
      (fun _ => secondBiasBoxFrame l row head) shuffles votes ends) :
    OpeningValueReached l X g shuffles votes ends := by
  obtain ⟨F,⟨prior⟩⟩ := key
  apply cur.advanceLocal
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  let thread := warpLane l g lane
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hWarp : warpIndex l thread = 14+(0 : Fin 2).val := hSame.2.symm.trans hw
  have hPos : 5 ≤ prior.pos lane := by
    have hBound : ((X.tr thread).take (prior.pos lane)).countP Execution.isShfl
        ≤ ((X.tr thread).take (prior.pos lane)).length := List.countP_le_length
    rw [prior.ordinals.shfl lane hl,List.length_take] at hBound
    omega
  have hPrior := prior.checkpoint lane hl
  have hCur := cur.checkpoint lane hl
  have hFrame := loaderRoleFrameAtKeyCommit hp hX hSame.1.2.1 0 hWarp hPos
    (prior.bounded lane hl) (prior.recorded lane hl) (prior.localSteps lane hl) hPrior.1
  have hNoBack es : ¬ TraceReach kernel Assumptions.all l thread (cur.state lane)
      es (prior.state lane) := by
    intro hr
    have hFloor := valueSetupRetainsFloor valueSetupTailCode valueSetupTailSegments
      hr (Nat.le_of_eq hCur.1.symm)
    rw [hPrior.1] at hFloor
    omega
  obtain ⟨_,hTrace⟩ := recordedCheckpointsPath (prior.bounded lane hl) (cur.bounded lane hl)
    (prior.recorded lane hl) (prior.localSteps lane hl) (cur.recorded lane hl)
    (cur.localSteps lane hl) hNoBack
  have hKeep := valueSetupBase hTrace hPrior.1.ge hCur.1 (ringShapeOfAt hPrior) hFrame.2
  exact ⟨cur.state lane,.refl,hCur.mono hKeep⟩

end PTX.Kernels.TmlFa4Fwd.Loader
