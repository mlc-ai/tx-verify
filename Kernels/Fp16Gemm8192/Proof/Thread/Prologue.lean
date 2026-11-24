-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Isa.Tmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.Loader
public import Kernels.Fp16Gemm8192.Proof.Thread.Mma
public import Kernels.Fp16Gemm8192.Proof.Thread.Scheduler
public import Kernels.Fp16Gemm8192.Proof.Thread.Consumer
public import Lemmas.Flow.Footprint

@[expose] public section

/-! # The common prologue as abstract states

Every thread broadcasts its warp index with a shuffle and branches on the value it receives
(`w`). Warp 0 elects a lane that prefetches the tensor maps; thread 0 initializes the
eighteen mbarriers; warp 0 allocates Tensor Memory (lane 0 then stores the returned address
to shared memory) and synchronizes. Every thread then fences, arrives on and waits at the
cluster barrier, and goes to its role: warps 8 to 11 first lower their register count; in
warp 11 one elected lane becomes the loader while the others leave, warp 10 goes to the
scheduler's election, and warps 8 and 9 go to the MMA election on the cluster's leader CTA
and leave on the other CTA; warps 0 to 7 go to the consumers' register increase.

That `w` is the warp index is a fact about the shuffle collective (`Warp.lean`); here the
role is selected by `w` as the code selects it, and a consumer only when `w` is the thread's
warp index, which its first state relies on. A received value that is
not a warp index of the block (a 32-bit integer below 12) is not followed further; along an
execution the shuffle returns the thread's warp index, so this never happens (`tracked`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

inductive Site where
  | shfl | elect | init (i : Fin 18) | alloc | allocWrite | warpBar | fence | fenceInit
  | arrive | wait | setMaxReg | roleElect
  deriving DecidableEq

def Site.pc : Site → Nat
  | .shfl => Flow.shfl_0 | .elect => Flow.elect_0
  | .init i => Flow.mbarInit.getD i.val 0
  | .alloc => Flow.tmemAlloc_0 | .allocWrite => Flow.tmemAlloc_0 | .warpBar => Flow.warpBar_0
  | .fence => Flow.fenceProxy_0 | .fenceInit => Flow.fenceMbarInit_0
  | .arrive => Flow.clusterArrive_0 | .wait => Flow.clusterWait_0
  | .setMaxReg => Flow.setMaxReg_0 | .roleElect => Flow.elect_1

/-- A prologue state: the site and the warp index the shuffle returned. -/
structure D where
  site : Site
  w : Nat

/-- The prologue's register values. -/
def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(47, b32 (g % L.block)), (55, b32 (g % L.block / 32)),
   (894, .ptr 64 false (.param "gemm_kernel_param_2") 0),
   (895, .ptr 64 false (.param "gemm_kernel_param_1") 0),
   (896, .ptr 64 false (.param "gemm_kernel_param_0") 0),
   (48, b32 d.w), (56, b32 0), (57, b32 4294967295),
   (2, .pred (decide (d.w ≠ 0))), (4, .pred (decide (g % L.block ≠ 0))),
   (5, .pred (decide (d.w ≠ 0))), (6, .pred (decide (d.w / 4 ≠ 2))),
   (20, .pred (decide (d.w = 10))), (21, .pred (decide (d.w ≠ 11))),
   (87, b32 L.sharedBase), (66, b32 1), (71, b32 2), (78, b32 256),
   (84, b32 10),
   (65, b32 (L.sharedBase + 8)), (67, b32 (L.sharedBase + 16)),
   (68, b32 (L.sharedBase + 24)), (69, b32 (L.sharedBase + 32)),
   (70, b32 (L.sharedBase + 40)), (72, b32 (L.sharedBase + 48)),
   (73, b32 (L.sharedBase + 56)), (74, b32 (L.sharedBase + 64)),
   (75, b32 (L.sharedBase + 72)), (76, b32 (L.sharedBase + 80)),
   (77, b32 (L.sharedBase + 88)), (79, b32 (L.sharedBase + 96)),
   (80, b32 (L.sharedBase + 104)), (81, b32 (L.sharedBase + 112)),
   (82, b32 (L.sharedBase + 120)), (83, b32 (L.sharedBase + 128)),
   (85, b32 (L.sharedBase + 160)), (86, b32 (L.sharedBase + 168)),
   (903, b64 L.sharedBase),
   (904, .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 L.sharedBase)),
   (902, .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 (L.sharedBase + 8))),
   (88, b32 0),
   (926, .ptr 64 true (.shared (g / L.block) (2 * ((g / L.block) / 2)))
       (BitVec.ofNat 64 (L.sharedBase +
     8))),
   (90, b32 L.sharedBase), (91, b32 512),
   (648, b32 0), (649, b32 4294967295),
   (899, .ptr 64 true (.param "gemm_kernel_param_0") 0),
   (900, .ptr 64 true (.param "gemm_kernel_param_1") 0),
   (901, .ptr 64 true (.param "gemm_kernel_param_2") 0),
   (650, b32 (g / L.block)), (878, b32 (Loader.claimN (g / L.block))),
   (834, b32 ((g / L.block) % 2)), (38, .pred (decide ((g / L.block) % 2 ≠ 0))),
   (925, .ptr 64 false (.shared (g / L.block) (2 *
     ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8)))]

def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values L g d).lookup r).getD (b32 0)

def factsAt (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- Between the allocation and its address store lane 0 is at the instruction's second step. -/
def sub (d : D) : Nat := if d.site = .allocWrite then 1 else 0

structure Inv (d : D) : Prop where
  w : d.w < 12

/-- Thread 0 of each CTA initializes the mbarriers. -/
def first (L : Launch) (g : Nat) : Bool := g % L.block = 0

/-- The site after the barrier initializations (or instead of them). -/
def afterInits (w : Nat) : Site := if w = 0 then .alloc else .fence

/-- The site after the shuffle's branch for a thread that does not elect. -/
def afterElect (L : Launch) (g w : Nat) : Site := if first L g then .init 0 else afterInits w

/-- The loader's first state, for the tile the CTA starts with. -/
def loaderStart (L : Launch) (g : Nat) : Loader.D :=
  ⟨.wait 0, Loader.claimM (g / L.block), Loader.claimN (g / L.block), 0, 0, b32 0, g / L.block⟩

/-- The state of warp 11's other lanes: the common exit. -/
def loaderIdle : Loader.D := ⟨.exitArrive, 0, 0, 0, 0, b32 0, 0⟩

/-- The roles a thread takes after the prologue. -/
inductive Role where
  | loader (l : Loader.D)
  | mma (m : Mma.D)
  | sched (s : Scheduler.D)
  | cons (c : Consumer.D)

/-- The MMA warps' first state: the election on the cluster's leader CTA, the exit on the
other CTA. -/
def mmaStart (L : Launch) (g : Nat) (w : Nat) : Mma.D :=
  ⟨if Loader.leader L g then .elect else .exitArrive, w, 0, 0, 0, 0, b32 0, 0⟩

/-- The consumers' first state: raising the register count. -/
def consStart : Consumer.D := ⟨.setMaxReg, 0, 0, 0, 0, 0, 0, b32 0, 0, fun _ => .float .f32 0,
    b32 0⟩

/-- The scheduler's first state: its election. -/
def schedStart : Scheduler.D := ⟨.elect, 0, 0, b32 0, 0⟩

/-- The abstract successor after event `e`. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option (D ⊕ Role)) :=
  match d.site with
  | .shfl =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      if wd = 32 ∧ v.toNat < 12 then
        some (some (.inl ⟨if v.toNat = 0 then .elect else afterElect L g v.toNat, v.toNat⟩))
      else some none
    | _ => some none
  | .elect => some (some (.inl { d with site := afterElect L g d.w }))
  | .init i =>
    if h : i.val + 1 < 18 then some (some (.inl { d with site := .init ⟨i.val + 1, h⟩ }))
    else some (some (.inl { d with site := afterInits d.w }))
  | .alloc =>
    match e.kind with
    | .tc (.resource _ _ (.alloc _)) =>
      if laneOf L g = 0 then some (some (.inl { d with site := .allocWrite }))
      else some (some (.inl { d with site := .warpBar }))
    | _ => none
  | .allocWrite => some (some (.inl { d with site := .warpBar }))
  | .warpBar => some (some (.inl { d with site := .fence }))
  | .fence => some (some (.inl { d with site := .fenceInit }))
  | .fenceInit => some (some (.inl { d with site := .arrive }))
  | .arrive => some (some (.inl { d with site := .wait }))
  | .wait =>
    if d.w / 4 = 2 then some (some (.inl { d with site := .setMaxReg }))
    else if d.w < 8 ∧ d.w = Consumer.tidOf L g / 32 then some (some (.inr (.cons consStart)))
    else some none
  | .setMaxReg =>
    if d.w = 11 then some (some (.inl { d with site := .roleElect }))
    else if d.w = 10 then some (some (.inr (.sched schedStart)))
    else if d.w = 8 ∨ d.w = 9 then some (some (.inr (.mma (mmaStart L g d.w))))
    else some none
  | .roleElect =>
    match e.kind with
    | .elect _ _ leader =>
      if d.w = 11 then
        some (some (.inr (.loader (if laneOf L g = leader then loaderStart L g else loaderIdle))))
      else some none
    | _ => none

/-- The value-table reduction used after evaluating a segment. -/
macro "pro_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- Evaluate a prologue segment from `h` and close the facts of its end state (as
`Loader.loader_seg`, with the prologue's value table). -/
syntax "pro_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| pro_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try pro_values
        all_goals seg_close [Launch.oneDim_ctaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_clusterCtaidOf ($hpre).oneDimLaunch.1,
          Launch.oneDim_rankOfCta ($hpre).oneDimLaunch.1, Dim3.get, ($hpre).cluster, $extra,*]))

end
end PTX.Kernels.Fp16Gemm8192.Proof.Prologue
