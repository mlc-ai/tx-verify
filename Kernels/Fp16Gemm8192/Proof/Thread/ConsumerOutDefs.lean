-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Consumer
public import Lemmas.Flow.BulkCount
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

/-! # The consumer's output quantities

The counts a consumer's epilogue keeps (its output barrier arrivals and bulk commits, by site)
and the staging addresses its stores and TMA stores use. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Consumer

/-- The output barrier of the thread's warp group. -/
abbrev outId (L : Launch) (g : Nat) : Nat := tidOf L g / 32 / 4 + 10

/-- An arrival on the thread's output barrier. -/
def isOutBar (L : Launch) (g : Nat) (e : Event) : Bool :=
  match e.kind with | .bar id .. => decide (id = outId L g) | _ => false

/-- The thread's arrivals on its output barrier. -/
def outBars (L : Launch) (g : Nat) (es : List Event) : Nat := es.countP (isOutBar L g)

/-- The output barrier arrivals of a thread are the barrier events on its output barrier. -/
theorem outBars_eq (L : Launch) (g : Nat) (es : List Event) :
    outBars L g es = es.countP (Execution.isBarId (outId L g)) := by
  unfold outBars
  congr 1

/-- The output barrier arrivals at a site, modulo a tile's sixteen. -/
def D.outPhase (d : D) : Nat := match d.site with
  | .drain k | .barA k => 2 * k.val
  | .store k _ _ | .barB k => 2 * k.val + 1
  | .fence k | .tma k | .commit k => 2 * k.val + 2
  | _ => 0

/-- How many arrivals the commits trail at a site: none before a slice's first barrier, one
between its barriers, two after its second barrier until its commit. -/
def D.outLag (d : D) : Nat := match d.site with
  | .drain _ | .barA _ => 0
  | .store .. | .barB _ => 1
  | .fence _ | .tma _ | .commit _ => 2
  | _ => 0

/-- Whether a state is inside a slice of the epilogue: from the first drain to the last commit. -/
def D.inEpi (d : D) : Nat := match d.site with
  | .drain _ | .barA _ | .store .. | .barB _ | .fence _ | .tma _ | .commit _ => 1
  | _ => 0

/-- Whether a state has started an epilogue: from the first drain through the final drain. -/
def D.started (d : D) : Nat := match d.site with
  | .drain _ | .barA _ | .store .. | .barB _ | .fence _ | .tma _ | .commit _ | .finalDrain => 1
  | _ => 0

/-- Whether a state is past its final drain: in the exit stage after the drain's bulk wait. -/
def D.drained (d : D) : Bool := match d.site with
  | .exitArrive | .exitWait | .relinquish | .ldBase | .dealloc | .exit => true
  | _ => false

/-- The data events a consumer has made in the tile it is loading, at a site: two per load (the
load and its wait), thirty-two at the accumulator release. -/
def D.tcPos (d : D) : Nat := match d.site with
  | .load j => 2 * j.val
  | .loadWait j => 2 * j.val + 1
  | .accArrive => 32
  | _ => 0

/-- The output counts along a consumer's run. -/
def OutRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  outBars L g es % 16 = d.outPhase % 16 ∧ 2 * commits es + d.outLag = outBars L g es

/-- Whether a state is between its slice's TMA store and the slice's commit: at the commit. -/
def D.tmaPend (d : D) : Nat := match d.site with
  | .commit _ => 1
  | _ => 0

/-- The TMA stores along a consumer's run: only the group's first thread reaches a slice's proxy
fence and TMA store; on a trace without undefined behaviour, the first thread has issued one TMA
store per commit, plus the one of the slice it is committing, and another thread none. -/
def TmaRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  (∀ k, d.site = .fence k ∨ d.site = .tma k → first L g = true) ∧
  ((∀ e ∈ es, ∀ f, e.kind ≠ .ub f) →
    storeIssues es = if first L g then commits es + d.tmaPend else 0)

/-- The CLC response a consumer holds at a site, from its successful poll to its group's CLC
barrier: one from its read to its group barrier arrival, none before or after. -/
def D.clcHold (d : D) : Nat := match d.site with
  | .clcLoad | .clcStatus | .clcFirst | .clcFence | .clcBar => 1
  | _ => 0

/-- The staging byte offset of element `el` of the thread's chunk `i` in the buffer of parity
`b`, from the shared base. -/
def stagingOff (tid b i el : Nat) : Nat := 197632 + 8192 * b + 2 * stage tid i + 4 * el

/-- The staging buffer of slice parity `b` of the thread's warp group, from the shared base. -/
def stagingBase (tid b : Nat) : Nat := 197632 + 8192 * b + 16384 * (tid / 32 / 4)

/-- The word a staging store of element `el` of chunk `i` of slice `k` writes: the pair the
conversion makes of two consecutive accumulator values, the lower in the low half. -/
def storeWord (acc : Nat → Value) (k i el : Nat) : Value :=
  Flow.cvtPairV (acc (32 * k + 8 * i + 2 * el + 1)) (acc (32 * k + 8 * i + 2 * el))

end Consumer

end
end PTX.Kernels.Fp16Gemm8192.Proof
