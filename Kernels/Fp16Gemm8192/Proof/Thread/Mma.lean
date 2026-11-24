-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.Loader
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.RoundTrip

@[expose] public section

/-! # The MMA warps as abstract states

On the leader CTA of each cluster, the elected lane of warp 8 and of warp 9 (`w`) each
compute half of the tile's accumulator: Tensor Memory columns `256 * (w % 2)` from the A
rows at shared offset `1024 * (w % 2)`. For each task the thread polls the CLC response
(which says whether a next task follows), releases it, waits for its accumulator to be
empty, and runs the K loop: thirty-two trips over the four input slots, each waiting for
the slot to be full, issuing four MMAs and committing to the slot's empty barrier. It then
commits to its accumulator-full barrier and either takes the next task or leaves.

An abstract state is the next event with the data that determines the live registers:
the K block `q` of the trip (a multiple of four), the parities of the full barriers (`fp`),
of the accumulator-empty barrier (`ap`) and of the CLC barrier (`cp`), the response read
and the claimed first CTA `x`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

inductive Site where
  /-- The election of the warp's MMA lane. -/
  | elect
  /-- The CLC response: poll, read, status query, first-CTA query, fence, release. -/
  | clcWait | clcLoad | clcStatus | clcFirst | clcFence | ack
  /-- The accumulator-empty poll. -/
  | accWait
  /-- Slot `s` of a trip: the full poll, four MMAs, the commit to its empty barrier. -/
  | full (s : Fin 4)
  | mma (s : Fin 4) (j : Fin 4)
  | commit (s : Fin 4)
  /-- The commit to the accumulator-full barrier. -/
  | accCommit
  /-- The common exit. -/
  | exitArrive | exitWait | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .elect => Flow.elect_3
  | .clcWait => Flow.mbarWait_15 | .clcLoad => Flow.loadAcquire_2 | .clcStatus => Flow.clcQuery_4
  | .clcFirst => Flow.clcQuery_5 | .clcFence => Flow.fenceProxy_3 | .ack => Flow.mbarArrive_11
  | .accWait => Flow.mbarWait_16
  | .full s => Flow.mbarWait.getD (17 + s.val) 0
  | .mma s j => Flow.mma.getD (4 * s.val + j.val) 0
  | .commit s => Flow.tcCommit.getD s.val 0
  | .accCommit => Flow.tcCommit_4
  | .exitArrive => Flow.clusterArrive_1 | .exitWait => Flow.clusterWait_1 | .exit => Flow.exit_0

structure D where
  site : Site
  w : Nat
  q : Nat
  fp : Nat
  ap : Nat
  cp : Nat
  resp : Value
  x : Nat

/-- The instruction-descriptor constant of the MMAs (the descriptor's fixed fields). -/
abbrev descC : Nat := 4611756662049472512

/-- The A and B operand descriptors of slot 0 (the start address in units of 16 bytes). -/
def aDesc (L : Launch) (w : Nat) : Nat := descC + (L.sharedBase + 1024) / 16 + 1024 * (w % 2)
def bBase (L : Launch) : Nat := (L.sharedBase + 132096) / 16

/-- Whether the MMA at slot `s`, position `j` of the trip at `q` accumulates. -/
def accumulates (q : Nat) (s j : Nat) : Bool := !(q = 0 && s = 0 && j = 0)

/-- The descriptor registers of the MMAs after the first of a trip: slot `s`, position `j`
(A then B). -/
def mmaRegs (L : Launch) (w : Nat) : List (Nat × Value) :=
  [(939, b64 (descC + bBase L + 4)), (940, b64 (aDesc L w + 6)),
   (941, b64 (descC + bBase L + 6)),
   (942, b64 (aDesc L w + 2048)), (943, b64 (descC + bBase L + 1024)),
   (944, b64 (aDesc L w + 2050)), (945, b64 (descC + bBase L + 1026)),
   (946, b64 (aDesc L w + 2052)), (947, b64 (descC + bBase L + 1028)),
   (948, b64 (aDesc L w + 2054)), (949, b64 (descC + bBase L + 1030)),
   (950, b64 (aDesc L w + 4096)), (951, b64 (descC + bBase L + 2048)),
   (952, b64 (aDesc L w + 4098)), (953, b64 (descC + bBase L + 2050)),
   (954, b64 (aDesc L w + 4100)), (955, b64 (descC + bBase L + 2052)),
   (956, b64 (aDesc L w + 4102)), (957, b64 (descC + bBase L + 2054)),
   (958, b64 (aDesc L w + 6144)), (959, b64 (descC + bBase L + 3072)),
   (960, b64 (aDesc L w + 6146)), (961, b64 (descC + bBase L + 3074)),
   (962, b64 (aDesc L w + 6148)), (963, b64 (descC + bBase L + 3076)),
   (964, b64 (aDesc L w + 6150)), (965, b64 (descC + bBase L + 3078))]

/-- The MMA thread's register values. -/
def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(48, b32 d.w), (835, b32 0), (836, b32 4294967295),
   (858, b32 L.sharedBase), (849, b32 (L.sharedBase + 104)), (850, b32 10000000),
   (851, b32 (L.sharedBase + 144)), (975, d.resp), (852, b32 d.x),
   (1003, .pred (decide (d.site = .clcFirst))), (1004, .pred true),
   (855, .ptr 32 false (.shared (g / L.block) (2 *
     ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 128))),
   (884, b32 d.q),
   (857, b32 (L.sharedBase + 8 * (d.w % 2) + 88)),
   (872, b32 (L.sharedBase + 8 * (d.w % 2) + 72)),
   (861, b32 (256 * (d.w % 2))),
   (882, b32 d.ap), (883, b32 d.cp), (885, b32 d.fp),
   (898, b64 (bBase L)), (934, b64 (aDesc L d.w)), (935, b64 (descC + bBase L)),
   (936, b64 (aDesc L d.w + 2)), (937, b64 (descC + bBase L + 2)),
   (938, b64 (aDesc L d.w + 4)),
   (871, b32 L.sharedBase), (860, b32 10000000),
   (859, b32 (L.sharedBase + 8)), (865, b32 (L.sharedBase + 16)),
   (867, b32 (L.sharedBase + 24)), (869, b32 (L.sharedBase + 32)),
   (864, b32 (L.sharedBase + 40)), (866, b32 (L.sharedBase + 48)),
   (868, b32 (L.sharedBase + 56)), (870, b32 (L.sharedBase + 64)),
   (862, b32 272629776), (863, b32 0),
   (886, b32 (if d.site = .full 0 ∧ d.q = 0 then 0 else 1)),
   (44, .bits 16 (BitVec.ofNat 64 3)), (45, .bits 16 (BitVec.ofNat 64 3)),
   (1007, .pred (accumulates d.q 0 0)), (1008, .pred true),
   (1009, .pred true), (1010, .pred true), (1012, .pred true),
   (1013, .pred true), (1014, .pred true), (1015, .pred true),
   (1017, .pred true), (1018, .pred true), (1019, .pred true),
   (1020, .pred true), (1022, .pred true), (1023, .pred true),
   (1024, .pred true), (1025, .pred true),
   (42, .pred true)] ++ mmaRegs L d.w

def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values L g d).lookup r).getD (b32 0)

def factsAt (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

structure Inv (d : D) : Prop where
  w : d.w = 8 ∨ d.w = 9
  q : d.q < 128
  q4 : d.q % 4 = 0
  fp : d.fp < 2
  ap : d.ap < 2
  cp : d.cp < 2
  x : d.x < 2 ^ 32

/-- The state after the last slot of a trip: the next trip, or the accumulator commit. -/
def endOfTrip (d : D) : D :=
  if d.q + 4 < 128 then { d with site := .full 0, q := d.q + 4, fp := 1 - d.fp }
  else { d with site := .accCommit, fp := 1 - d.fp }

/-- The abstract successor after event `e`; `none` after an event into a dead state. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .elect =>
    match e.kind with
    | .elect _ _ leader =>
      if laneOf L g = leader then
        some (some { d with site := .clcWait, q := 0, fp := 0, ap := 1, cp := 0 })
      else some (some { d with site := .exitArrive })
    | _ => none
  | .clcWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .clcLoad else .clcWait })
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
  | .clcFence => some (some { d with site := .ack, q := 0 })
  | .ack => some (some { d with site := .accWait })
  | .accWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .full 0 else .accWait })
    | _ => none
  | .full s =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .mma s 0 else .full s })
    | _ => none
  | .mma s j =>
    if h : j.val + 1 < 4 then some (some { d with site := .mma s ⟨j.val + 1, h⟩ })
    else some (some { d with site := .commit s })
  | .commit s =>
    if h : s.val + 1 < 4 then some (some { d with site := .full ⟨s.val + 1, h⟩ })
    else some (some (endOfTrip d))
  | .accCommit =>
    if d.x = Loader.none32 then some (some { d with site := .exitArrive })
    else some (some { d with site := .clcWait, ap := 1 - d.ap, cp := 1 - d.cp })
  | .exitArrive => some (some { d with site := .exitWait })
  | .exitWait => some (some { d with site := .exit })
  | .exit => none

/-- The value-table reduction used after evaluating a segment. -/
macro "mma_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- Evaluate an MMA segment from `h` and close the facts of its end state (as
`Loader.loader_seg`, with the MMA thread's value table). -/
syntax "mma_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| mma_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try mma_values
        all_goals seg_close [Launch.oneDim_ctaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_clusterCtaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_rankOfCta ($hpre).oneDimLaunch.1, Dim3.get, ($hpre).cluster,
          Loader.none32, $extra,*]))

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
