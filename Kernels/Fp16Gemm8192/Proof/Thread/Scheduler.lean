-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.Loader
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.RoundTrip

@[expose] public section

/-! # The CLC scheduler as abstract states

The elected lane of warp 10 runs the task loop of its CTA. On the cluster's leader CTA it
waits until every consumer of the previous response has released it (the acknowledgement
barrier) and issues the next cancellation request, multicast to both CTAs. Each CTA's
scheduler then arrives on its own CLC barrier expecting the 16-byte response, waits for it,
reads it, queries it and releases it; with no claimed CTA it leaves.

An abstract state is the next event with the acknowledgement and CLC parities (`ap`,
`cp`), the response read and the claimed first CTA `x`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Scheduler
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

inductive Site where
  | elect
  /-- The leader's acknowledgement poll and cancellation request. -/
  | ackWait | tryCancel
  /-- The arrival expecting the response, its poll, read, queries, fence and release. -/
  | arriveTx | clcWait | clcLoad | clcStatus | clcFirst | clcFence | ack
  | exitArrive | exitWait | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .elect => Flow.elect_2
  | .ackWait => Flow.mbarWait_13 | .tryCancel => Flow.clcIssue_0
  | .arriveTx => Flow.mbarArrive_9 | .clcWait => Flow.mbarWait_14
  | .clcLoad => Flow.loadAcquire_1 | .clcStatus => Flow.clcQuery_2 | .clcFirst => Flow.clcQuery_3
  | .clcFence => Flow.fenceProxy_2 | .ack => Flow.mbarArrive_10
  | .exitArrive => Flow.clusterArrive_1 | .exitWait => Flow.clusterWait_1 | .exit => Flow.exit_0

structure D where
  site : Site
  ap : Nat
  cp : Nat
  resp : Value
  x : Nat

def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(48, b32 10), (629, b32 0), (630, b32 4294967295),
   (636, b32 L.sharedBase), (632, b32 (L.sharedBase + 128)), (633, b32 10000000),
   (880, b32 d.cp), (881, b32 d.ap),
   (634, b32 (L.sharedBase + 144)), (635, b32 (L.sharedBase + 104)),
   (647, b32 L.sharedBase), (637, b32 (L.sharedBase + 104)), (638, b32 16),
   (639, b32 10000000), (640, b32 (L.sharedBase + 144)), (971, d.resp),
   (998, .pred (decide (d.site = .clcFirst))), (641, b32 d.x),
   (999, .pred true),
   (645, .ptr 32 false (.shared (g / L.block) (2 *
     ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 128))),
   (42, .pred true)]

def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values L g d).lookup r).getD (b32 0)

def factsAt (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

structure Inv (d : D) : Prop where
  ap : d.ap < 2
  cp : d.cp < 2
  x : d.x < 2 ^ 32

/-- The head of the task loop: the leader CTA requests, the other CTA only receives. -/
def loopHead (L : Launch) (g : Nat) : Site := if Loader.leader L g then .ackWait else .arriveTx

def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .elect =>
    match e.kind with
    | .elect _ _ leader =>
      if laneOf L g = leader then some (some { d with site := loopHead L g, ap := 1, cp := 0 })
      else some (some { d with site := .exitArrive })
    | _ => none
  | .ackWait =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then some (some { d with site := .tryCancel, ap := 1 - d.ap })
      else some (some d)
    | _ => none
  | .tryCancel => some (some { d with site := .arriveTx })
  | .arriveTx => some (some { d with site := .clcWait })
  | .clcWait =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then some (some { d with site := .clcLoad, cp := 1 - d.cp })
      else some (some d)
    | _ => none
  | .clcLoad =>
    match e.kind with
    | .rd _ bs => (Flow.responseOf bs).map fun r => some { d with site := .clcStatus,
                                                                  resp := .clc r }
    | _ => none
  | .clcStatus =>
    match e.kind with
    | .clcQuery _ r =>
      some (some { d with
        site := (if r.firstCta.isSome then .clcFirst else .clcFence), x := Loader.none32 })
    | _ => none
  | .clcFirst =>
    match e.kind with
    | .clcQuery _ r =>
      some (some { d with
        site := .clcFence, x := ((r.firstCta.map fun c => c.1.toNat).getD Loader.none32) })
    | _ => none
  | .clcFence => some (some { d with site := .ack })
  | .ack =>
    if d.x = Loader.none32 then some (some { d with site := .exitArrive })
    else some (some { d with site := loopHead L g })
  | .exitArrive => some (some { d with site := .exitWait })
  | .exitWait => some (some { d with site := .exit })
  | _ => none

/-- The value-table reduction used after evaluating a segment. -/
macro "sched_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- Evaluate a scheduler segment from `h` and close the facts of its end state. -/
syntax "sched_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sched_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try sched_values
        all_goals seg_close [Launch.oneDim_ctaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_clusterCtaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_rankOfCta ($hpre).oneDimLaunch.1, Dim3.get, ($hpre).cluster,
          Loader.none32, $extra,*]))

end
end PTX.Kernels.Fp16Gemm8192.Proof.Scheduler
