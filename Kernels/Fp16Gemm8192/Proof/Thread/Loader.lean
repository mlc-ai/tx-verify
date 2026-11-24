-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Kernels.Fp16Gemm8192.Flow.Sites
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderValues
public import Lemmas.Flow.Code
public import Lemmas.Flow.RoundTrip
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next
public import Kernels.Fp16Gemm8192.Flow.Code
public import Lemmas.Flow.Bits
public import Kernels.Fp16Gemm8192.Proof.Support.AssumptionFacts
public import Lemmas.Flow.Footprint

@[expose] public section

/-! # The loader as abstract states

The loader (the elected lane of warp 11) loops over tasks. For each task it runs the K loop:
sixteen trips of eight K blocks, each block waiting for its input slot to be empty, issuing
three tensor loads and, on the cluster's leader CTA, arriving on the slot's full barrier.
At the end of a task it polls the CLC response, reads it, queries it, releases it with an
arrival on the leader CTA's acknowledgement barrier and either continues with the claimed
tile or drains the four empty slots and leaves through the common exit.

An abstract state is the loader's next event with the data that determines the registers
it carries: the tile `(m, n)`, the first K block `q` of the trip, the CLC phase `cp`, the
response value read and the claimed first CTA `x`. The registers are the live registers of
the site (`Flow.live`), valued by `valueOf`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The loader's next event. -/
inductive Site where
  /-- Block `b` of a trip: the empty-slot poll, the three loads, the full-slot arrival. -/
  | wait (b : Fin 8)
  | load (b : Fin 8) (j : Fin 3)
  | arrive (b : Fin 8)
  /-- End of a task: poll, read, status query, first-CTA query, fence, acknowledgement. -/
  | clcWait | clcLoad | clcStatus | clcFirst | clcFence | ack
  /-- No task left: wait for each input slot to be empty. -/
  | drain (i : Fin 4)
  /-- The common exit: the cluster barrier and the return. -/
  | exitArrive | exitWait | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .wait 0 => Flow.mbarWait_0 | .wait 1 => Flow.mbarWait_1 | .wait 2 => Flow.mbarWait_2
  | .wait 3 => Flow.mbarWait_3 | .wait 4 => Flow.mbarWait_4 | .wait 5 => Flow.mbarWait_5
  | .wait 6 => Flow.mbarWait_6 | .wait 7 => Flow.mbarWait_7
  | .load 0 0 => Flow.tensorCopy_0 | .load 0 1 => Flow.tensorCopy_1 | .load 0 2 => Flow.tensorCopy_2
  | .load 1 0 => Flow.tensorCopy_3 | .load 1 1 => Flow.tensorCopy_4 | .load 1 2 => Flow.tensorCopy_5
  | .load 2 0 => Flow.tensorCopy_6 | .load 2 1 => Flow.tensorCopy_7 | .load 2 2 => Flow.tensorCopy_8
  | .load 3 0 => Flow.tensorCopy_9 | .load 3 1 => Flow.tensorCopy_10 | .load 3 2 =>
    Flow.tensorCopy_11
  | .load 4 0 => Flow.tensorCopy_12 | .load 4 1 => Flow.tensorCopy_13 | .load 4 2 =>
    Flow.tensorCopy_14
  | .load 5 0 => Flow.tensorCopy_15 | .load 5 1 => Flow.tensorCopy_16 | .load 5 2 =>
    Flow.tensorCopy_17
  | .load 6 0 => Flow.tensorCopy_18 | .load 6 1 => Flow.tensorCopy_19 | .load 6 2 =>
    Flow.tensorCopy_20
  | .load 7 0 => Flow.tensorCopy_21 | .load 7 1 => Flow.tensorCopy_22 | .load 7 2 =>
    Flow.tensorCopy_23
  | .arrive 0 => Flow.mbarArrive_0 | .arrive 1 => Flow.mbarArrive_1 | .arrive 2 => Flow.mbarArrive_2
  | .arrive 3 => Flow.mbarArrive_3 | .arrive 4 => Flow.mbarArrive_4 | .arrive 5 => Flow.mbarArrive_5
  | .arrive 6 => Flow.mbarArrive_6 | .arrive 7 => Flow.mbarArrive_7
  | .clcWait => Flow.mbarWait_8 | .clcLoad => Flow.loadAcquire_0 | .clcStatus => Flow.clcQuery_0
  | .clcFirst => Flow.clcQuery_1 | .clcFence => Flow.fenceProxy_1 | .ack => Flow.mbarArrive_8
  | .drain 0 => Flow.mbarWait_9 | .drain 1 => Flow.mbarWait_10 | .drain 2 => Flow.mbarWait_11
  | .drain 3 => Flow.mbarWait_12
  | .exitArrive => Flow.clusterArrive_1 | .exitWait => Flow.clusterWait_1 | .exit => Flow.exit_0

/-- A loader state. `x` is the first CTA claimed by the current response (`none32` when
the response cancels nothing). -/
structure D where
  site : Site
  m : Nat
  n : Nat
  q : Nat
  cp : Nat
  resp : Value
  x : Nat

/-- The value `2^32 - 1` that marks the absence of a claimed CTA. -/
abbrev none32 : Nat := 4294967295

/-- A response claims a CTA: it names a first CTA, decoded as other than `none32`. -/
def claims (rr : ClcResponse) : Prop := (rr.firstCta.map fun c => c.1.toNat).getD none32 ≠ none32

/-- Registers outside the K-loop table. `%r2` holds the warp index the opening shuffle
returned; the loader is the thread whose shuffle returned 11. -/
def extra (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(48, b32 11), (876, b32 d.cp), (878, b32 d.n), (879, b32 d.m),
    (821, b32 L.sharedBase), (812, b32 (L.sharedBase + 104)), (813, b32 10000000),
    (814, b32 (L.sharedBase + 144)), (817, b32 (L.sharedBase + 128)), (818, b32 0), (973, d.resp),
    (815, b32 d.x),
    (988, .pred (decide (d.site = .clcFirst))),
    (989, .pred true),
    (819, .ptr 32 false (.shared (g / L.block) (2 *
    ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 128))),
    (833, b32 L.sharedBase), (827, b32 (L.sharedBase + 40)), (828, b32 1),
    (829, b32 10000000), (830, b32 (L.sharedBase + 48)),
    (831, b32 (L.sharedBase + 56)), (832, b32 (L.sharedBase + 64)),
    (42, .pred true), (34, .pred (decide (d.q ≠ 128))),
    (35, .pred (decide (d.x = none32))), (36, .pred (decide (d.x > 1023))),
    (37, .pred (decide (d.x ≠ none32)))]

def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((extra L g d).lookup r).getD (value L g d.m d.n d.q r)

/-- The registers live at `pc`, with their values in state `d`. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

/-- The live registers of the site, with their values. -/
abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- The leader CTA of the cluster arrives on full barriers. -/
def leader (L : Launch) (g : Nat) : Bool := (g / L.block) % 2 = 0

/-- Bounds every loader state satisfies. -/
structure Inv (d : D) : Prop where
  m : d.m < 16
  n : d.n < 32
  q : d.q < 128
  q8 : d.q % 8 = 0
  cp : d.cp < 2
  x : d.x < 2 ^ 32

/-- The tile claimed by a first CTA `x` (the code's arithmetic, including its fallback). -/
def claimM (x : Nat) : Nat := if x > 1023 then 0 else x / 512 % 2 * 8 + x / 2 % 8
def claimN (x : Nat) : Nat := if x > 1023 then 0 else x / 16 % 32

/-- The state after the last block of a trip: the next trip, or the end of the task. -/
def endOfTrip (d : D) : D :=
  if d.q + 8 < 128 then { d with site := .wait 0, q := d.q + 8 }
  else { d with site := .clcWait }

/-- The abstract successor after event `e`. After the read of the CLC response the code moves
the value through two halves and queries it: unless the bytes are a response
(`Flow.responseOf`), the thread faults (`none`), in the read or in the moves and the query. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .wait b =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .load b 0 else .wait b })
    | _ => none
  | .load b j =>
    if h : j.val + 1 < 3 then some (some { d with site := .load b ⟨j.val + 1, h⟩ })
    else if leader L g then some (some { d with site := .arrive b })
    else if h : b.val + 1 < 8 then some (some { d with site := .wait ⟨b.val + 1, h⟩ })
    else some (some (endOfTrip d))
  | .arrive b =>
    if h : b.val + 1 < 8 then some (some { d with site := .wait ⟨b.val + 1, h⟩ })
    else some (some (endOfTrip d))
  | .clcWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .clcLoad else .clcWait })
    | _ => none
  | .clcLoad =>
    match e.kind with
    | .rd _ bs => (Flow.responseOf bs).map fun r =>
      some { d with site := .clcStatus, resp := .clc r }
    | _ => none
  | .clcStatus =>
    match e.kind with
    | .clcQuery _ r =>
      some (some { d with site := if r.firstCta.isSome then .clcFirst else .clcFence, x := none32 })
    | _ => none
  | .clcFirst =>
    match e.kind with
    | .clcQuery _ r =>
      some (some { d with site := .clcFence, x :=
        ((r.firstCta.map fun c => c.1.toNat).getD none32) })
    | _ => none
  | .clcFence => some (some { d with site := .ack })
  | .ack =>
    if d.x = none32 then some (some { d with site := .drain 0 })
    else some (some { d with site := .wait 0, m := claimM d.x, n := claimN d.x, q := 0, cp := 1 -
      d.cp })
  | .drain i =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then
        if h : i.val + 1 < 4 then some (some { d with site := .drain ⟨i.val + 1, h⟩ })
        else some (some { d with site := .exitArrive })
      else some (some d)
    | _ => none
  | .exitArrive => some (some { d with site := .exitWait })
  | .exitWait => some (some { d with site := .exit })
  | _ => none

/-- The value-table reduction used after evaluating a segment. -/
macro "loader_values" : tactic => `(tactic| simp only [valueOf, value, PTX.Flow.lookupLit,
  Option.getD_some, Option.getD_none])

/-- Evaluate a loader segment from `h` and close the facts of its end state: syntactically,
by deciding a closed fact, by rebuilding a split value, or by `close_fact` with the given
rewrites (equations for the code's bit arithmetic on bounded values). -/
syntax "loader_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| loader_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try loader_values
        all_goals seg_close [Launch.oneDim_clusterCtaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_rankOfCta ($hpre).oneDimLaunch.1, ($hpre).cluster, Dim3.get, outputRow,
          none32, $extra,*]))

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
