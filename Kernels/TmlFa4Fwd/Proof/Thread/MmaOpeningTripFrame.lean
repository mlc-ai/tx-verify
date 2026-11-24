-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitProgress
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
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
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue

set_option maxRecDepth 100000 in
private theorem openingTripCode :
    ((kernel.code.drop 2144).take (2276-2144)).all
      (fun i => !((mmaWrites i.op).contains 1189)) = true := by kernel_rfl

private def openingTripFloor : Fin 3 → Nat
  | 0 => 2144
  | 1 => 2275
  | _ => 2276

set_option maxRecDepth 15000 in
private theorem openingTripTailCode (cut : Fin 3) :
    (kernel.code.drop (openingTripFloor cut)).all
      (fun i => Thread.staysPastEvent (openingTripFloor cut) i.op) = true := by
  fin_cases cut <;> kernel_rfl

private theorem openingTripTailSegments (cut : Fin 3) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (openingTripFloor cut ≤ seg.stop)
      | none => false) = true := by fin_cases cut <;> kernel_rfl

private theorem openingTripRetainsFloor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (cut : Fin 3) (h : TraceReach kernel Assumptions.all l g s events t)
    (hs : openingTripFloor cut ≤ s.pc) : openingTripFloor cut ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit (openingTripTailCode cut)
      (openingTripTailSegments cut) hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit (openingTripTailCode cut)
      (openingTripTailSegments cut) hs (.inr ⟨_,rfl,he⟩))

private theorem openingTripFrameStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hpc : 2144 ≤ s.pc ∧ s.pc < 2276) (hStep : WStep kernel Assumptions.all l g s e u) :
    2144 ≤ u.pc ∧ u.regs 1189 = s.regs 1189 := by
  have hLow : 2144 ≤ u.pc := Thread.eventTailStepOfAudit (openingTripTailCode 0)
    (openingTripTailSegments 0) hpc.1 hStep
  refine ⟨hLow,mmaStepReg (by omega) (by omega) (fun ins hc => ?_) hStep⟩
  have hGet : ((kernel.code.drop 2144).take (2276-2144))[s.pc-2144]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hpc.1]
    exact hc
  have hHold := List.all_eq_true.mp openingTripCode ins (List.mem_of_getElem? hGet)
  simpa using hHold

private theorem openingTripFrameTrace {l : Launch} {g n : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t)
    (hs : 2144 ≤ s.pc) (ht : t.pc = 2275) (hTrip : s.regs 1189 = some (b32 n)) :
    t.regs 1189 = some (b32 n) := by
  have below {u : TState} {es : List Event}
      (hRest : TraceReach kernel Assumptions.all l g u es t) : u.pc < 2276 := by
    by_contra! hHigh
    have hEnd := openingTripRetainsFloor 2 hRest hHigh
    change 2276 ≤ t.pc at hEnd
    omega
  induction h with
  | refl => exact hTrip
  | tau hs' hTail ih =>
    have hNext := openingTripFrameStep ⟨hs,below (.tau hs' hTail)⟩ (.inl ⟨rfl,hs'⟩)
    exact ih hNext.1 ht (hNext.2.trans hTrip) below
  | event he hTail ih =>
    have hNext := openingTripFrameStep ⟨hs,below (.event he hTail)⟩ (.inr ⟨_,rfl,he⟩)
    exact ih hNext.1 ht (hNext.2.trans hTrip) below

/-- The actual post-QK cursor retains the loop trip count established at the opening Q wait. -/
theorem openingTripAtKeyReturn {l : Launch} {X : Execution}
    {g start finish n : Nat} {s₀ s t₀ t : TState}
    (hS : At s 2144 [(1189,b32 n)]) (hT : t.pc = 2275)
    (hStart : start ≤ (X.tr g).length) (hFinish : finish ≤ (X.tr g).length)
    (hFirst : Run kernel Assumptions.all l g {} ((X.tr g).take start) (some s₀))
    (hNext : Run kernel Assumptions.all l g {} ((X.tr g).take finish) (some t₀))
    (hLocal₀ : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s₀ s)
    (hLocal₁ : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t₀ t) :
    t.regs 1189 = some (b32 n) := by
  have hNoBack es : ¬ TraceReach kernel Assumptions.all l g t es s := by
    intro h
    have hFloor := openingTripRetainsFloor 1 h hT.ge
    change 2275 ≤ s.pc at hFloor
    rw [hS.1] at hFloor
    omega
  obtain ⟨_,h⟩ := recordedCheckpointsPath hStart hFinish hFirst hLocal₀ hNext hLocal₁ hNoBack
  exact openingTripFrameTrace h hS.1.ge hT hS.2.2.2.2.1

end PTX.Kernels.TmlFa4Fwd.Mma
