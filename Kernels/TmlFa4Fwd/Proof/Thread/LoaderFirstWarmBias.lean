-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmBiasExpectationProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
public import Kernels.TmlFa4Fwd.Flow.Code.Part018
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryOperandsProgress
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.MBarrier PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The first recurring lower Bias packet has issued its expectation and both tensor halves. -/
structure FirstWarmBiasIssued (p : Params) (l : Launch) (X : Execution) (g batch : Nat) : Prop where
  expectation : ∃ e, X.Arrive e (biasReadyObject l (g/l.block) 0) 32768 1 true .cta ∧
    0 < arrivals (biasReadyObject l (g/l.block) 0) ((X.tr e.1).take e.2)
  halves : ∀ half : Fin 2, ∃ issue spec, issue.1/l.block = g/l.block ∧
    BiasSubbox p l X issue 0 half spec ∧
    biasTensorOrdinal l X 0 half issue = 1

set_option maxRecDepth 100000 in
private theorem loaderBiasMapPreserved {l : Launch} {t : Nat} {s u : TState}
    {es : List Event} (hRun : TraceReach kernel Assumptions.all l t s es u)
    (hLo : 174 ≤ s.pc) (hHi : u.pc < 1901) (hShape : RingShape s)
    (hMap : s.regs 7289 = some (.ptr 64 false (.param (param 11)) 0)) :
    u.regs 7289 = some (.ptr 64 false (.param (param 11)) 0) := by
  have floorCode : (kernel.code.drop 1901).all (fun i => Thread.staysPastEvent 1901 i.op) =
      true := by kernel_rfl
  have floorSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (1901 ≤ seg.stop) | none => false) = true := by kernel_rfl
  have floor {a b : TState} {fs : List Event}
      (h : TraceReach kernel Assumptions.all l t a fs b) (ha : 1901 ≤ a.pc) : 1901 ≤ b.pc := by
    induction h with
    | refl => exact ha
    | tau ht _ ih =>
      exact ih (Thread.eventTailStepOfAudit floorCode floorSegments ha (.inl ⟨rfl,ht⟩))
    | event he _ ih =>
      exact ih (Thread.eventTailStepOfAudit floorCode floorSegments ha (.inr ⟨_,rfl,he⟩))
  let F := [(7289,Value.ptr 64 false (.param (param 11)) 0)]
  have keep : ((kernel.code.drop 174).take (1901-174)).all
      (fun i => loaderPipelineCutOp 174 1901 1901 (F.map Prod.fst) i.op) = true := by kernel_rfl
  have step {a b : TState} {e : Option Event} (he : WStep kernel Assumptions.all l t a e b)
      (ha : 174 ≤ a.pc ∧ a.pc < 1901) (shape : RingShape a)
      (reg : a.regs 7289 = some (.ptr 64 false (.param (param 11)) 0)) :
      174 ≤ b.pc ∧ RingShape b ∧ b.regs 7289 = some (.ptr 64 false (.param (param 11)) 0) := by
    obtain ⟨hv,_,hs,hR⟩ := pipelineCutStep (F := F) (by decide) (by decide) ha keep he
      shape ⟨reg,trivial⟩
    exact ⟨hv,hs,hR.1⟩
  induction hRun with
  | refl => exact hMap
  | tau ht hRest ih =>
    have h := step (.inl ⟨rfl,ht⟩)
      ⟨hLo,Nat.lt_of_not_ge (fun x => (Nat.not_le_of_lt hHi) (floor (.tau ht hRest) x))⟩
      hShape hMap
    exact ih h.1 hHi h.2.1 h.2.2
  | event he hRest ih =>
    have h := step (.inr ⟨_,rfl,he⟩)
      ⟨hLo,Nat.lt_of_not_ge (fun x => (Nat.not_le_of_lt hHi) (floor (.event he hRest) x))⟩
      hShape hMap
    exact ih h.1 hHi h.2.1 h.2.2

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
