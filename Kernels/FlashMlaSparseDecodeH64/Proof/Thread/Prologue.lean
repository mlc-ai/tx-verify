-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Local
public import Lemmas.Flow.Alloc
public import Lemmas.Flow.AllocTmpl
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.RunInv
public import Lemmas.Flow.Bar
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.Async

@[expose] public section

/-! # The prologue of the sparse decode kernel, as a site machine

Every thread of the CTA runs PTX lines 39 to 272 before its role starts: it reads its place in
the launch (`%ctaid.x`, `%ctaid.y`, `%tid.x`) and broadcasts its warpgroup and warp index from
lane 0 with two `shfl.sync.idx`. Warp 0's elected lane prefetches the three tensor-map
descriptors, initializes the 23 `mbarrier`s of the barrier rings with their counts, fences the
initializations, and — elected again — allocates 512 columns of Tensor Memory and relinquishes
the allocation permit; the thread reads the allocated address back and traps unless it is zero.
Every thread passes `bar.sync 0`, and the warpgroup index then selects the role: warpgroup 0
continues at pc 103 (`setmaxnreg.inc 224`), warpgroup 1 at pc 1842 (`setmaxnreg.dec 72`) and
warpgroup 2 at pc 2606 (`setmaxnreg.inc 208`).

The abstract states of the machine are the prologue's event instructions (`Site`): the two
shuffles, the two elections, the 23 initializations, the fence, the allocation's request, its
lane-0 store and the read-back of the allocated address, the relinquish, the CTA barrier, and
one hand-off state per warpgroup. The hand-off states are the role's first event (its
`setmaxnreg`) with the prologue's register facts live there; the machine stops following the
thread after them (`next = some none`).

A shuffle continues only when it returns the value lane 0 holds (the warpgroup index for the
first, the warp index for the second); any other received value is not followed further, which
is what a full-warp `shfl.sync.idx` from lane 0 of a warp-uniform operand returns for every
thread of the warp. The allocation read follows the frozen program's integer comparison.
A zero word reaches relinquishment. A nonzero word reaches `trap`, and a word the
comparison cannot read reaches a fault. The execution-level allocator supplies the value
needed to prove that the read can reach relinquishment safely.

## The tensor-map descriptor range

The elected lane's three descriptor additions write the numeric addresses
`param_1 + 128`, `param_1 + 512` and `param_1 + 768`, and each prefetch continues only when its
numeric address is a published map. The `paramPointers` reading checks the truncated 64-bit
pattern of the address, so it names a descriptor exactly when the object's base satisfies
`P.param1Base + 1024 ≤ 2 ^ 64`. `Pre` states the base's alignment and its disjointness from
`param_0` but not this bound, so the elected lane's path is proved under the bound
(`leader_run`, `step_elect0`) and every other site from `Pre` alone. With the bound as a further
premise the whole machine is sound (`steps_of_param1Range`, `sound_of_param1Range`); without it
only the first election's elected-lane branch is open (`steps_except_elect0`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions the prologue is evaluated under. The prefetch of the three tensor-map
descriptors reads the descriptor addresses as numeric addresses of the `param_1` object
(`Assumptions.paramPointers`); every other instruction of the prologue is the Core rule. -/
abbrev asms : List Assumption := Assumptions.all

/-! ### A thread's place in the launch -/

/-- The thread's CTA. -/
def ctaOf (L : Launch) (g : Nat) : Nat := g / L.block

/-- The thread's linear thread index in its CTA (`%tid.x`). -/
def tidOf (L : Launch) (g : Nat) : Nat := (L.tidOf g).x

/-- The thread's warpgroup (`%tid.x / 128`): the value of the first shuffle. -/
def wgOf (L : Launch) (g : Nat) : Nat := tidOf L g / 128

/-- The thread's warp (`%tid.x / 32`): the value of the second shuffle. -/
def warpOf (L : Launch) (g : Nat) : Nat := tidOf L g / 32

/-- The thread's lane in its warp (`%tid.x % 32`). -/
def laneOf (L : Launch) (g : Nat) : Nat := tidOf L g % 32

/-- `%ctaid.x` of the thread's CTA: the query index of the kernel's `(s_q, b, 1)` grid. -/
def ctaidX (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).x % 2 ^ 32

/-- `%ctaid.y` of the thread's CTA: the batch of the kernel's `(s_q, b, 1)` grid. -/
def ctaidY (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).y % 2 ^ 32

/-- A shared address `off` bytes above the dynamic shared base, as the kernel's 32-bit
registers hold it. -/
def sb (L : Launch) (off : Nat) : Value := b32 (L.sharedBase + off)

variable {P : Params} {L : Launch} {mem0 : Mem0}

theorem tidOf_eq (hpre : Pre P L mem0) (g : Nat) : tidOf L g = g % 384 := by
  simp only [tidOf, Launch.tidOf, Dim3.coord, hpre.ntid, hpre.block, Nat.mod_mod,
    Nat.mod_one, Nat.mul_one]

theorem tidOf_lt (hpre : Pre P L mem0) (g : Nat) : tidOf L g < 2 ^ 32 := by
  rw [tidOf_eq hpre]; omega

/-- `%tid.x` of the thread in a `(384, 1, 1)` CTA. -/
theorem tidOf_x_eq (hpre : Pre P L mem0) (g : Nat) : (L.tidOf g).x = g % 384 := by
  simp only [Launch.tidOf, Dim3.coord, hpre.ntid, hpre.block, Nat.mod_mod, Nat.mod_one,
    Nat.mul_one]

/-- The dynamic shared base plus the last byte the kernel addresses is below `2 ^ 32`. -/
theorem sharedBase_lt (hpre : Pre P L mem0) : L.sharedBase + 222952 < 2 ^ 32 := by
  have h := hpre.sharedRange
  rw [← hpre.sharedBase] at h
  unfold sharedBytes at h
  omega

/-! ### The sites -/

/-- The prologue's event instructions. -/
inductive Site where
  /-- The broadcast of the warpgroup index. -/
  | shfl0
  /-- The broadcast of the warp index. -/
  | shfl1
  /-- Warp 0's election of the lane that prefetches the tensor maps. -/
  | elect0
  /-- Warp 0's election of the lane that initializes the barriers. -/
  | elect1
  /-- Warp 0's initialization of barrier ring entry `j`. -/
  | init (j : Fin 23)
  /-- The fence of the barrier initializations. -/
  | fence
  /-- The allocation request of `tcgen05.alloc`. -/
  | alloc
  /-- Lane 0's store of the allocated address. -/
  | allocStore
  /-- The read-back of the allocated address. -/
  | allocRead
  /-- The relinquishment of the allocation permit. -/
  | relinquish
  /-- The CTA barrier. -/
  | barrier
  /-- The hand-off to the role of warpgroup `wg`. -/
  | handoff (wg : Fin 3)
  deriving DecidableEq

/-- The program counter of a role's first event. -/
def entryPc (wg : Fin 3) : Nat :=
  [Flow.setMaxReg_0, Flow.setMaxReg_1, Flow.setMaxReg_2].getD wg.val 0

def Site.pc : Site → Nat
  | .shfl0 => Flow.shfl_0
  | .shfl1 => Flow.shfl_1
  | .elect0 => Flow.elect_0
  | .elect1 => Flow.elect_1
  | .init j => Flow.mbarInit.getD j.val 0
  | .fence => Flow.fenceMbarInit_0
  | .alloc | .allocStore => Flow.tmemAlloc_0
  | .allocRead => Flow.load_0
  | .relinquish => Flow.tmemRelinquish_0
  | .barrier => Flow.bar_0
  | .handoff wg => entryPc wg

/-- `tcgen05.alloc` performs two events: lane 0's store of the allocated address is the
instruction's second step, at the same program counter. -/
def Site.sub : Site → Nat
  | .allocStore => 1
  | _ => 0

/-! ### The register values -/

/-- The barriers warp 0 initializes: the byte above the dynamic shared base, in program
order. -/
def initOff : Fin 23 → Nat
  | ⟨0, _⟩ => 222768
  | ⟨1, _⟩ => 222776
  | ⟨2, _⟩ => 222784
  | ⟨3, _⟩ => 222792
  | ⟨4, _⟩ => 222808
  | ⟨5, _⟩ => 222824
  | ⟨6, _⟩ => 222904
  | ⟨7, _⟩ => 222920
  | ⟨8, _⟩ => 222936
  | ⟨9, _⟩ => 222800
  | ⟨10, _⟩ => 222816
  | ⟨11, _⟩ => 222832
  | ⟨12, _⟩ => 222912
  | ⟨13, _⟩ => 222928
  | ⟨14, _⟩ => 222944
  | ⟨15, _⟩ => 222840
  | ⟨16, _⟩ => 222872
  | ⟨17, _⟩ => 222848
  | ⟨18, _⟩ => 222880
  | ⟨19, _⟩ => 222856
  | ⟨20, _⟩ => 222888
  | ⟨21, _⟩ => 222864
  | ⟨22, _⟩ => 222896
  | ⟨_ + 23, h⟩ => absurd h (by omega)

/-- The expected arrival counts of the 23 barriers. -/
def initCount : Fin 23 → Nat
  | 0 => 128
  | 1 => 1
  | 2 => 1
  | 3 => 128
  | 4 => 1
  | 5 => 128
  | 6 => 1
  | 7 => 128
  | 8 => 1
  | 9 => 128
  | 10 => 1
  | 11 => 128
  | 12 => 1
  | 13 => 128
  | 14 => 1
  | 15 => 32
  | 16 => 129
  | 17 => 32
  | 18 => 129
  | 19 => 32
  | 20 => 129
  | 21 => 32
  | 22 => 129
  | ⟨_ + 23, h⟩ => absurd h (by omega)

/-- The register holding the address of barrier `j`. -/
def initAddrReg : Fin 23 → Nat
  | ⟨0, _⟩ => 527
  | ⟨1, _⟩ => 529
  | ⟨2, _⟩ => 530
  | ⟨3, _⟩ => 531
  | ⟨4, _⟩ => 532
  | ⟨5, _⟩ => 533
  | ⟨6, _⟩ => 534
  | ⟨7, _⟩ => 535
  | ⟨8, _⟩ => 536
  | ⟨9, _⟩ => 537
  | ⟨10, _⟩ => 538
  | ⟨11, _⟩ => 539
  | ⟨12, _⟩ => 540
  | ⟨13, _⟩ => 541
  | ⟨14, _⟩ => 542
  | ⟨15, _⟩ => 544
  | ⟨16, _⟩ => 546
  | ⟨17, _⟩ => 547
  | ⟨18, _⟩ => 548
  | ⟨19, _⟩ => 549
  | ⟨20, _⟩ => 550
  | ⟨21, _⟩ => 551
  | ⟨22, _⟩ => 552
  | ⟨_ + 23, h⟩ => absurd h (by omega)

/-- The base register of barrier `j`'s address: the second ring's addresses are formed from
`%r85`/`%r87`, the others from `%r95`. The address itself is in `initAddrReg j`. -/
def initCountReg : Fin 23 → Nat
  | ⟨0, _⟩ => 526
  | ⟨1, _⟩ => 528
  | ⟨2, _⟩ => 528
  | ⟨3, _⟩ => 526
  | ⟨4, _⟩ => 528
  | ⟨5, _⟩ => 526
  | ⟨6, _⟩ => 528
  | ⟨7, _⟩ => 526
  | ⟨8, _⟩ => 528
  | ⟨9, _⟩ => 526
  | ⟨10, _⟩ => 528
  | ⟨11, _⟩ => 526
  | ⟨12, _⟩ => 528
  | ⟨13, _⟩ => 526
  | ⟨14, _⟩ => 528
  | ⟨15, _⟩ => 543
  | ⟨16, _⟩ => 545
  | ⟨17, _⟩ => 543
  | ⟨18, _⟩ => 545
  | ⟨19, _⟩ => 543
  | ⟨20, _⟩ => 545
  | ⟨21, _⟩ => 543
  | ⟨22, _⟩ => 545
  | ⟨_ + 23, h⟩ => absurd h (by omega)

/-- The registers read but never written in the program: `%r492` and `%r1257` are packed with
a written word into a `b64` register and discarded when it is unpacked, so their value is
immaterial and the prologue does not track it. -/
def skipRegs : List Nat := [950, 1715]

/-- The registers the hand-off states carry beyond the live ones: the prologue's launch reads,
which the roles use and which stay true at the role's entry. -/
def extraLive : Nat → List Nat
  | 103 => [459, 460, 461, 462, 463, 464, 465, 466]
  | 1842 => [459, 460, 461, 462, 463, 464, 465, 466]
  | 2606 => [459, 460, 461, 462, 463, 464, 465, 466]
  | _ => []

/-- The registers the prologue's states give a value: the live registers of the program
counter, without the two the program never writes, plus the hand-off's extras. -/
def liveAll (pc : Nat) : List Nat :=
  (Flow.live pc).filter (fun r => !skipRegs.contains r) ++ extraLive pc

/-- The prologue's registers, as functions of the launch and the thread. -/
def values (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (459, b32 (ctaidX L g)), (460, b32 (ctaidY L g)), (461, b32 (tidOf L g)),
   (519, b32 (tidOf L g / 128)), (462, b32 (wgOf L g)),
   (463, b32 (tidOf L g % 128)), (464, b32 (warpOf L g)), (465, b32 (warpOf L g)),
   (466, b32 (laneOf L g)),
   (521, b32 0), (522, b32 4294967295), (524, b32 0), (525, b32 4294967295),
   (526, b32 128), (527, sb L 222768), (528, b32 1), (529, sb L 222776),
   (530, sb L 222784), (531, sb L 222792), (532, sb L 222808), (533, sb L 222824),
   (534, sb L 222904), (535, sb L 222920), (536, sb L 222936), (537, sb L 222800),
   (538, sb L 222816), (539, sb L 222832), (540, sb L 222912), (541, sb L 222928),
   (542, sb L 222944), (543, b32 32), (544, sb L 222840), (545, b32 129),
   (546, sb L 222872), (547, sb L 222848), (548, sb L 222880), (549, sb L 222856),
   (550, sb L 222888), (551, sb L 222864), (552, sb L 222896),
   (553, sb L 0), (554, sb L 222752), (555, b32 512),
   (2880, b32 4286578688)]

def valueOf (L : Launch) (g : Nat) (r : Nat) : Value :=
  ((values L g).lookup r).getD (b32 0)

/-- The registers live at `pc`, valued by the table. -/
def factsAt (L : Launch) (g pc : Nat) : List (Nat × Value) :=
  factsFrom (liveAll pc) (valueOf L g)

abbrev facts (L : Launch) (g : Nat) (s : Site) : List (Nat × Value) := factsAt L g s.pc

/-- The table's values, as `simp` reduces them after a segment's evaluation. -/
macro "pro_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-! ### The machine -/

/-- How the integer comparison reads the value just loaded into the allocator register. -/
def allocWord (L : Launch) (g : Nat) (v : Value) : Exec (BitVec 64) :=
  readBits L g { regs := fun _ => some v } 32 (.reg 557)

/-- The abstract successor after event `e`.

A shuffle continues only on the value lane 0 holds: the warpgroup index for the first, the warp
index for the second. An election continues to its own next site; its leader decides the local
path. The read of the allocated word continues to the relinquishment only when the word is zero,
the case in which the kernel does not trap. The CTA barrier continues by the thread's warpgroup
to that warpgroup's role. The hand-off states are not followed further. -/
def next (L : Launch) (g : Nat) : Site → Event → Option (Option Site)
  | .shfl0, e =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      some (if wd = 32 ∧ v = BitVec.ofNat 64 (wgOf L g) then some .shfl1 else none)
    | .shfl .. => some none
    | _ => none
  | .shfl1, e =>
    match e.kind with
    | .shfl _ _ _ _ (.bits wd v) _ =>
      some (if wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g) then
        some (if warpOf L g = 0 then .elect0 else .barrier) else none)
    | .shfl .. => some none
    | _ => none
  | .elect0, e =>
    match e.kind with
    | .elect .. => some (some .elect1)
    | _ => none
  | .elect1, e =>
    match e.kind with
    | .elect _ _ ld => some (some (if laneOf L g = ld then .init 0 else .alloc))
    | _ => none
  | .init j, _ => some (some (if h : j.val + 1 < 23 then .init ⟨j.val + 1, h⟩ else .fence))
  | .fence, _ => some (some .alloc)
  | .alloc, e =>
    match e.kind with
    | .tc (.resource _ _ (.alloc _)) =>
      some (some (if laneOf L g = 0 then .allocStore else .allocRead))
    | _ => none
  | .allocStore, _ => some (some .allocRead)
  | .allocRead, e =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs >>= allocWord L g with
      | .ok v => if v.toNat = 0 then some (some .relinquish) else none
      | .error _ => none
    | _ => none
  | .relinquish, _ => some (some .barrier)
  | .barrier, _ =>
    some (some (if wgOf L g = 1 then .handoff 1
      else if wgOf L g = 0 then .handoff 0 else .handoff 2))
  | .handoff _, _ => some none

/-- A concrete state of a prologue site. -/
def Good (L : Launch) (g : Nat) (s : Site) (t : TState) : Prop :=
  t.pc = s.pc ∧ t.sub = s.sub ∧ t.acc = [] ∧ t.fault = none ∧ Holds t.regs (facts L g s)

/-- The obligation of one prologue event: a pending fault, local steps to a concrete state of
the successor, or a dead thread. -/
abbrev Step (L : Launch) (g : Nat) (s : Site) (u : TState) (e : Event) : Prop :=
  (next L g s e = some none ∨ ∃ s' t', next L g s e = some (some s') ∧
      Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ Good L g s' t') ∨
    (next L g s e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-- The prologue of thread `g` as a code machine. -/
def code (L : Launch) (g : Nat) : PTX.Flow.Code kernel asms L g where
  D := Site
  init := .shfl0
  pc := Site.pc
  facts := facts L g
  sub := Site.sub
  inv := fun _ => True
  next := next L g

/-! ### Reading and writing the facts

The prologue's local segments are evaluated by `seg_fp`. A one-instruction step whose result the
evaluation cannot see (the descriptor-address arithmetic of the parameter object) is taken by
`run_local` with the result computed separately, as in the other kernels' prologues. -/

/-- The empty state is at pc 0 with no facts. -/
theorem at_init : At ({} : TState) 0 ([] : List (Nat × Value)) :=
  ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- Facts at the next instruction from a state whose registers differ in `ws` only. -/
theorem at_next_of {t t' : TState} {pc : Nat} {ws : List Nat}
    (h : At t pc (factsAt L g pc)) (hpc : t'.pc = pc + 1) (hs : t'.sub = t.sub)
    (ha : t'.acc = t.acc) (hf : t'.fault = t.fault)
    (hw : ∀ r ∈ ws, r ∈ liveAll (pc + 1) → t'.regs r = some (valueOf L g r))
    (hfr : ∀ r, r ∉ ws → t'.regs r = t.regs r)
    (hl : ∀ r ∈ liveAll (pc + 1), r ∈ ws ∨ r ∈ liveAll pc) :
    At t' (pc + 1) (factsAt L g (pc + 1)) := by
  refine ⟨hpc, hs.trans h.2.1, ha.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr => ?_⟩
  by_cases hm : r ∈ ws
  · exact hw r hm hr
  · rw [hfr r hm]
    rcases hl r hr with h' | h'
    · exact absurd h' hm
    · exact holds_mem h.2.2.2.2 (mem_factsFrom h')

/-- An election that writes the leader's lane to `d` and the election's predicate to `p`
continues at the next instruction with the site's facts and those two. -/
theorem at_elect {t : TState} {pc d p : Nat} {x : Value} {b : Bool}
    (h : At t pc (factsAt L g pc)) (hd : d ∉ liveAll pc) (hp : p ∉ liveAll pc)
    (hdp : p ≠ d) :
    At (PTX.next (setReg (setReg t d x) p (.pred b))) (pc + 1)
      ((p, .pred b) :: (d, x) :: factsAt L g pc) := by
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_⟩
  · exact congrArg (· + 1) h.1
  · show (PTX.next (setReg (setReg t d x) p (.pred b))).regs p = some (.pred b)
    exact Function.update_self ..
  · show (PTX.next (setReg (setReg t d x) p (.pred b))).regs d = some x
    rw [show (PTX.next (setReg (setReg t d x) p (.pred b))).regs =
        Function.update (Function.update t.regs d (some x)) p (some (.pred b)) from rfl,
      Function.update_of_ne (Ne.symm hdp), Function.update_self]
  · exact holds_update (holds_update h.2.2.2.2 (not_mem_factsFrom hd))
      (not_mem_factsFrom hp)

/-- `a ⊆ ws ∪ b` for literal lists, decided by evaluation of the membership test. -/
theorem mem_or_of_all {a b ws : List Nat}
    (h : a.all (fun r => ws.contains r || b.contains r) = true) : ∀ r ∈ a, r ∈ ws ∨ r ∈ b := by
  intro r hr
  have h1 := List.all_eq_true.mp h r hr
  rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at h1
  exact h1

/-- Close `∀ r ∈ l', r ∈ ws ∨ r ∈ l` for the generated liveness tables. -/
macro "live_or" : tactic => `(tactic| first
  | exact mem_or_of_all (by decide +kernel)
  | (intro r hr; exact Or.inr (by table_decide)))

/-- Rewrite the launch data the prologue's arithmetic reads: the thread's `%tid.x` of a
`(384, 1, 1)` CTA, and the two `%ctaid` components. -/
syntax "launch_norm" term:max : tactic
macro_rules
  | `(tactic| launch_norm $hpre) => `(tactic|
      simp only [ctaidX, ctaidY, ctaOf, tidOf, wgOf, warpOf, laneOf, tidOf_x_eq $hpre,
        Dim3.get, ($hpre).block, Nat.mod_one, Nat.mul_one])

/-- Evaluate a prologue segment from `h` and close the facts of its end state. -/
syntax "pro_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| pro_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := sharedBase_lt $hpre
      seg_fp $h using
        try pro_values
        all_goals (try launch_norm $hpre)
        all_goals (try seg_close [sb, $extra,*])
        all_goals (try simp only [b32, sb, Value.bits.injEq, true_and, $extra,*])
        all_goals decide +kernel))

/-! ### The site instructions

The instruction at each site, by the generated lookups: every site is an event instruction with
no guard, and the 23 initializations are the 23 `mbarrier.init` instructions. -/

theorem site_init_ok (j : Fin 23) :
    ∃ ins, kernel.code[(Site.init j).pc]? = some ins ∧ ins.op.isLocal = false ∧
      ins.guard = none := by
  fin_cases j <;> first
    | exact ⟨ _, Flow.code_mbarInit_0, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_1, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_2, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_3, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_4, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_5, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_6, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_7, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_8, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_9, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_10, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_11, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_12, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_13, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_14, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_15, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_16, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_17, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_18, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_19, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_20, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_21, rfl, rfl⟩
    | exact ⟨ _, Flow.code_mbarInit_22, rfl, rfl⟩

theorem site_handoff_ok (wg : Fin 3) :
    ∃ ins, kernel.code[(Site.handoff wg).pc]? = some ins ∧ ins.op.isLocal = false
      ∧ ins.guard = none := by
  fin_cases wg <;> first
    | exact ⟨ _, Flow.code_setMaxReg_0, rfl, rfl⟩
    | exact ⟨ _, Flow.code_setMaxReg_1, rfl, rfl⟩
    | exact ⟨ _, Flow.code_setMaxReg_2, rfl, rfl⟩

/-- Every prologue site is an unguarded event instruction. -/
theorem site_ok (s : Site) :
    ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧
      ins.guard = none := by
  cases s with
  | shfl0 => exact ⟨ _, Flow.code_shfl_0, rfl, rfl⟩
  | shfl1 => exact ⟨ _, Flow.code_shfl_1, rfl, rfl⟩
  | elect0 => exact ⟨ _, Flow.code_elect_0, rfl, rfl⟩
  | elect1 => exact ⟨ _, Flow.code_elect_1, rfl, rfl⟩
  | init j => exact site_init_ok j
  | fence => exact ⟨ _, Flow.code_fenceMbarInit_0, rfl, rfl⟩
  | alloc => exact ⟨ _, Flow.code_tmemAlloc_0, rfl, rfl⟩
  | allocStore => exact ⟨ _, Flow.code_tmemAlloc_0, rfl, rfl⟩
  | allocRead => exact ⟨ _, Flow.code_load_0, rfl, rfl⟩
  | relinquish => exact ⟨ _, Flow.code_tmemRelinquish_0, rfl, rfl⟩
  | barrier => exact ⟨ _, Flow.code_bar_0, rfl, rfl⟩
  | handoff wg => exact site_handoff_ok wg

/-! ### The opening segment -/

/-- **The prologue opens**: from the empty state, six local instructions read the two parameter
objects' addresses, the thread's `%ctaid.x`, `%ctaid.y` and `%tid.x`, and its warpgroup index
`%tid.x / 128`, reaching the first shuffle. -/
theorem start (hpre : Pre P L mem0) (_hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧
      At t Flow.shfl_0 (facts L g .shfl0) := by
  have htid := tidOf_lt hpre g
  obtain ⟨ t, hr, ht⟩ :
      ∃ t, run kernel asms L g 6 {} = some t ∧ At t Flow.shfl_0 (facts L g .shfl0) := by
    pro_seg at_init hpre
  exact ⟨ t, run_rtg hr, ht⟩

/-- The range of the `param_1` tensor-map object: its last byte is below `2 ^ 64`, so the
truncation of a descriptor address to 64 bits is the identity. `Pre` does not state it; the
elected lane's descriptor prefetches need it (see the module doc). -/
def Param1Range (P : Params) : Prop := P.param1Base + 1024 ≤ 2 ^ 64

/-- A thread of the `(384, 1, 1)` CTA is in warpgroup 0, 1 or 2. -/
theorem wgOf_lt (hpre : Pre P L mem0) : wgOf L g < 3 := by
  simp only [wgOf, tidOf_eq hpre]; omega

/-- A thread of the `(384, 1, 1)` CTA is in warp 0 to 11. -/
theorem warpOf_lt (hpre : Pre P L mem0) : warpOf L g < 12 := by
  simp only [warpOf, tidOf_eq hpre]; omega

/-- `and.b32 d, a, 127` keeps the low seven bits of `a`. -/
theorem land127 (a : Nat) : a &&& 127 = a % 128 := Nat.and_two_pow_sub_one_eq_mod a 7

/-- The model's lane (`g % block % 32`) is the prologue's `%tid.x % 32`. -/
theorem laneOf_core (hpre : Pre P L mem0) : PTX.laneOf (L := L) g = laneOf L g := by
  simp only [PTX.laneOf, laneOf, tidOf, tidOf_x_eq hpre, hpre.block]

/-! ### Local steps no assumption names, and the parameter-pointer steps -/

/-- No assumption takes a segment at a prologue state. -/
theorem asms_segment_free (t : TState) : ∀ a ∈ asms, a.segmentRule L g t = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The local rules of the assumptions on an address instruction are all empty. -/
theorem localRule_none_addr (t : TState) (ai : AddrInstr) :
    ∀ a ∈ asms, a.localRule L g t (.addr ai) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Assumptions.paramPointers]
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule]
  · rfl

/-- A local step whose rule the assumption list selects is that rule's outcome. -/
theorem run_paramRule {t t' : TState} {pc : Nat} {op : Op} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (h : At t pc F) (hl : op.isLocal = true)
    (hfind : asms.findSome? (fun a => a.localRule L g t op) = some (pure t')) :
    run kernel asms L g 1 t = some t' := by
  refine run_local hc hl h ?_
  rw [execLocalA_noSegment (asms_segment_free t)]
  unfold execLocalRule
  rw [hfind]
  rfl

/-- `cvta.param.u64` of the `param_1` object's address: the thread's generic pointer to it. -/
theorem run_cvtaParam {t : TState} {pc d a : Nat} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .addr (.cvta false .param 64 d (.reg a))⟩)
    (h : At t pc F) (hr : t.regs a = some (.ptr 64 false (.param (param "1")) 0)) :
    run kernel asms L g 1 t =
      some (PTX.next (setReg t d (.ptr 64 true (.param (param "1")) 0))) := by
  refine run_local hc rfl h ?_
  rw [execLocalA_noSegment (asms_segment_free t), execLocalRule_of_none (localRule_none_addr t _)]
  simp only [execLocal_cvta (c := .cvta false .param 64 d (.reg a)) (by rfl), execCvta,
    readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
  simp

/-- A descriptor-offset addition is independent of the vector cursor and accumulator. -/
theorem paramAdd_exec {t : TState} {pc d a : Nat} {k : Int}
    (hpc : t.pc = pc) (hcon : paramAdds.contains pc = true)
    (hr : t.regs a = some (.ptr 64 true (.param (param "1")) 0))
    (hp : L.paramObjects (param "1") = some (mapParam, P.param1Base)) (hk : 0 ≤ k) :
    execLocalA asms L g t (.int ⟨.add, .int .s 64, false, [some d], [.reg a, .imm k]⟩) =
      .ok (PTX.next (setReg t d (.bits 64 (BitVec.ofNat 64 (P.param1Base + k.toNat))))) := by
  rw [execLocalA_noSegment (asms_segment_free t)]
  unfold execLocalRule
  simp only [asms, Assumptions.all, List.findSome?_cons, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumption.idealReal, Assumption.approxExact,
    Assumption.ncReadOnly, Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp,
    Assumptions.storeDrain, Assumptions.paramPointers, hpc, hcon, readReg, hr,
    Assumptions.offsetOf, pure, Except.pure]
  repeat' split
  all_goals first | omega | simp_all

/-- A descriptor-offset addition on the `param_1` object's generic address, by the kernel's
parameter-pointer reading: the register receives the numeric address of the descriptor. -/
theorem run_paramAdd {t : TState} {pc d a : Nat} {k : Int} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 64, false, [some d],
      [.reg a, .imm k]⟩⟩)
    (h : At t pc F) (hcon : paramAdds.contains pc = true)
    (hr : t.regs a = some (.ptr 64 true (.param (param "1")) 0))
    (hp : L.paramObjects (param "1") = some (mapParam, P.param1Base)) (hk : 0 ≤ k) :
    run kernel asms L g 1 t =
      some (PTX.next (setReg t d (.bits 64 (BitVec.ofNat 64 (P.param1Base + k.toNat))))) :=
  run_local hc rfl h (paramAdd_exec h.1 hcon hr hp hk)

/-- A `prefetch.tensormap` of a published descriptor of the `param_1` object, by the kernel's
parameter-pointer reading: the prefetch has no effect on the thread's state. -/
theorem run_prefetchMap {t : TState} {pc a : Nat} {x : BitVec 64} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .prefetchTensorMap true 64 (.reg a)⟩)
    (h : At t pc F) (hpub : prefetchTensorMapSites.contains pc = true)
    (hdisj : paramAdds.contains pc = false)
    (hr : t.regs a = some (.bits 64 x))
    (hm : (L.tensorMaps x.toNat).isSome = true) :
    run kernel asms L g 1 t = some (PTX.next t) := by
  have hpc : t.pc = pc := h.1
  refine run_paramRule hc h rfl ?_
  simp only [asms, Assumptions.all, List.findSome?_cons, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumption.idealReal, Assumption.approxExact,
    Assumption.ncReadOnly, Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp,
    Assumptions.storeDrain, Assumptions.paramPointers, hpc, hpub, hdisj, readValue, readReg, hr, hm,
    bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals first | omega | simp_all

/-- A register not among a list's keys, after adding one key. -/
theorem not_mem_facts_cons {F : List (Nat × Value)} {r s : Nat} {v : Value}
    (h1 : s ≠ r) (h2 : ∀ p ∈ F, p.1 ≠ r) : ∀ p ∈ (s, v) :: F, p.1 ≠ r := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h1
  · exact h2 p hp

/-- Warp 0's elected lane prefetches the three tensor-map descriptors: the address of the
`param_1` object is converted to a generic pointer, the three descriptor offsets are added and
each descriptor is prefetched. The steps write only `%rd33`, `%rd30`, `%rd31` and `%rd32`, which
are dead at pc 28. -/
theorem leader_run {t : TState} (h : At t 21 (factsAt L g 21))
    (hp1 : P.param1Base + 1024 ≤ 2 ^ 64)
    (hb : L.paramObjects (param "1") = some (mapParam, P.param1Base))
    (hQ : L.tensorMaps (P.param1Base + 128) = some q)
    (hO : L.tensorMaps (P.param1Base + 512) = some o)
    (hK : L.tensorMaps (P.param1Base + 768) = some k) :
    ∃ t', run kernel asms L g 7 t = some t' ∧ At t' 28 (factsAt L g 28) := by
  have hr0 : t.regs 2990 = some (.ptr 64 false (.param (param "1")) 0) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (by table_decide : (2990 : Nat) ∈ liveAll 21))
    simpa [valueOf, PTX.Flow.lookupLit, Option.getD_some] using hm
  set v1 : Value := .ptr 64 true (.param (param "1")) 0 with hv1
  set t1 := PTX.next (setReg t 3022 v1) with ht1
  have e1 : run kernel asms L g 1 t = some t1 := by
    rw [ht1]; exact run_cvtaParam Flow.code_21 h hr0
  have a1 : At t1 22 ((3022, v1) :: factsAt L g 21) := by
    rw [ht1]; exact At.set h (not_mem_factsFrom (by decide))
  obtain ⟨r1, -⟩ := a1.2.2.2.2
  set v2 : Value := .bits 64 (BitVec.ofNat 64 (P.param1Base + 128)) with hv2
  set t2 := PTX.next (setReg t1 3019 v2) with ht2
  have e2 : run kernel asms L g 1 t1 = some t2 := by
    rw [ht2]
    exact run_paramAdd (pc := 22) (k := 128) Flow.code_22 a1 (by decide) r1 hb (by norm_num)
  have a2 : At t2 23 ((3019, v2) :: (3022, v1) :: factsAt L g 21) := by
    rw [ht2]; exact At.set a1 (not_mem_facts_cons (by decide) (not_mem_factsFrom (by decide)))
  obtain ⟨r2, -, -⟩ := a2.2.2.2.2
  have hmQ : (L.tensorMaps (BitVec.ofNat 64 (P.param1Base + 128)).toNat).isSome = true := by
    have hx : (BitVec.ofNat 64 (P.param1Base + 128)).toNat = P.param1Base + 128 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hx, hQ]; rfl
  set t3 := PTX.next t2 with ht3
  have e3 : run kernel asms L g 1 t2 = some t3 := by
    rw [ht3]
    exact run_prefetchMap (pc := 23) Flow.code_23 a2 (by decide) (by decide)
      (x := BitVec.ofNat 64 (P.param1Base + 128)) (by simpa [hv2] using r2) hmQ
  have a3 : At t3 24 ((3019, v2) :: (3022, v1) :: factsAt L g 21) := by
    rw [ht3]; exact At.next a2
  obtain ⟨-, r3, -⟩ := a3.2.2.2.2
  set v4 : Value := .bits 64 (BitVec.ofNat 64 (P.param1Base + 512)) with hv4
  set t4 := PTX.next (setReg t3 3020 v4) with ht4
  have e4 : run kernel asms L g 1 t3 = some t4 := by
    rw [ht4]
    exact run_paramAdd (pc := 24) (k := 512) Flow.code_24 a3 (by decide) r3 hb (by norm_num)
  have a4 : At t4 25 ((3020, v4) :: (3019, v2) :: (3022, v1) :: factsAt L g 21) := by
    rw [ht4]
    exact At.set a3 (not_mem_facts_cons (by decide)
      (not_mem_facts_cons (by decide) (not_mem_factsFrom (by decide))))
  obtain ⟨r4, -, -, -⟩ := a4.2.2.2.2
  have hmO : (L.tensorMaps (BitVec.ofNat 64 (P.param1Base + 512)).toNat).isSome = true := by
    have hx : (BitVec.ofNat 64 (P.param1Base + 512)).toNat = P.param1Base + 512 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hx, hO]; rfl
  set t5 := PTX.next t4 with ht5
  have e5 : run kernel asms L g 1 t4 = some t5 := by
    rw [ht5]
    exact run_prefetchMap (pc := 25) Flow.code_25 a4 (by decide) (by decide)
      (x := BitVec.ofNat 64 (P.param1Base + 512)) (by simpa [hv4] using r4) hmO
  have a5 : At t5 26 ((3020, v4) :: (3019, v2) :: (3022, v1) :: factsAt L g 21) := by
    rw [ht5]; exact At.next a4
  obtain ⟨-, -, r5, -⟩ := a5.2.2.2.2
  set v6 : Value := .bits 64 (BitVec.ofNat 64 (P.param1Base + 768)) with hv6
  set t6 := PTX.next (setReg t5 3021 v6) with ht6
  have e6 : run kernel asms L g 1 t5 = some t6 := by
    rw [ht6]
    exact run_paramAdd (pc := 26) (k := 768) Flow.code_26 a5 (by decide) r5 hb (by norm_num)
  have a6 : At t6 27 ((3021, v6) :: (3020, v4) :: (3019, v2) :: (3022, v1) :: factsAt L g 21) := by
    rw [ht6]
    exact At.set a5 (not_mem_facts_cons (by decide) (not_mem_facts_cons (by decide)
      (not_mem_facts_cons (by decide) (not_mem_factsFrom (by decide)))))
  obtain ⟨r6, -, -, -, -⟩ := a6.2.2.2.2
  have hmK : (L.tensorMaps (BitVec.ofNat 64 (P.param1Base + 768)).toNat).isSome = true := by
    have hx : (BitVec.ofNat 64 (P.param1Base + 768)).toNat = P.param1Base + 768 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hx, hK]; rfl
  set t7 := PTX.next t6 with ht7
  have e7 : run kernel asms L g 1 t6 = some t7 := by
    rw [ht7]
    exact run_prefetchMap (pc := 27) Flow.code_27 a6 (by decide) (by decide)
      (x := BitVec.ofNat 64 (P.param1Base + 768)) (by simpa [hv6] using r6) hmK
  obtain ⟨-, -, -, -, h21⟩ := a6.2.2.2.2
  refine ⟨t7, ?_, ?_⟩
  · exact run_comp (run_comp (run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5) e6) e7
  · have hsub : t7.sub = 0 := by
      simp only [ht7, ht6, ht5, ht4, ht3, ht2, ht1, PTX.next, setReg]
      exact h.2.1
    have hacc : t7.acc = [] := by
      simp only [ht7, ht6, ht5, ht4, ht3, ht2, ht1, PTX.next, setReg]
      exact h.2.2.1
    have hfault : t7.fault = none := by
      simp only [ht7, ht6, ht5, ht4, ht3, ht2, ht1, PTX.next, setReg]
      exact h.2.2.2.1
    have hpc : t7.pc = 28 := by
      simp only [ht7, ht6, ht5, ht4, ht3, ht2, ht1, PTX.next, setReg, h.1]
    refine ⟨hpc, hsub, hacc, hfault, ?_⟩
    show Holds t7.regs (factsFrom (liveAll 28) (valueOf L g))
    have hle : liveAll 28 = liveAll 21 := by decide +kernel
    rw [hle]
    exact h21

/-- The first shuffle: a `.bits 32` value equal to the warpgroup index continues to the second
shuffle after the `%tid.x % 128` and `%tid.x >> 5` steps; any other received value is not
followed. -/
theorem step_shfl0 (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.shfl_0 (facts L g .shfl0))
    (hc : kernel.code[Flow.shfl_0]? = some ins)
    (hf : Fires Flow.shfl_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .shfl0 u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, he, hu⟩ := fires_shfl (p := some 2) hf
  subst he
  simp only [Option.elim] at hu
  subst hu
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (wgOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      left; right
      have h1 : At (PTX.next (setReg (setReg t 462 (.bits 32 (BitVec.ofNat 64 (wgOf L g))))
          2 (.pred ok))) 7 (factsAt L g 7) := by
        refine at_next_of (ws := [462, 2]) h (by simp [PTX.next, setReg, h.1]) rfl rfl rfl ?_ ?_ ?_
        · intro r hr hrl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · simp only [setReg, PTX.next]
            pro_values
            rfl
          · exact absurd hrl (by decide +kernel)
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2⟩ := hr
          simp [setReg, PTX.next, Function.update_of_ne h1, Function.update_of_ne h2]
        · live_or
      obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 _ = some t2 ∧
          At t2 Flow.shfl_1 (facts L g .shfl1) := by
        pro_seg h1 hpre [land127]
      exact ⟨.shfl1, t2, by simp [next], run_rtg hr2,
        ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩
    · left; left; simp [next, hv]
  all_goals left; left; simp [next]

/-- The second shuffle: a `.bits 32` value equal to the warp index sends warp 0 to its first
election and every other warp to the CTA barrier; any other received value is not followed. -/
theorem step_shfl1 (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.shfl_1 (facts L g .shfl1))
    (hc : kernel.code[Flow.shfl_1]? = some ins)
    (hf : Fires Flow.shfl_1 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .shfl1 u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
  obtain ⟨av, bv, cv, recv, ok, he, hu⟩ := fires_shfl (p := some 3) hf
  subst he
  simp only [Option.elim] at hu
  subst hu
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      left; right
      have h10 : At (PTX.next (setReg (setReg t 465 (.bits 32 (BitVec.ofNat 64 (warpOf L g))))
          3 (.pred ok))) 10 (factsAt L g 10) := by
        refine at_next_of (ws := [465, 3]) h (by simp [PTX.next, setReg, h.1]) rfl rfl rfl ?_ ?_ ?_
        · intro r hr hrl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · simp only [setReg, PTX.next]
            pro_values
            rfl
          · exact absurd hrl (by decide +kernel)
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2⟩ := hr
          simp [setReg, PTX.next, Function.update_of_ne h1, Function.update_of_ne h2]
        · live_or
      have hmk : At (PTX.next (setReg (setReg t 465 (.bits 32 (BitVec.ofNat 64 (warpOf L g))))
          3 (.pred ok))) 10 ((465, b32 (warpOf L g)) :: factsAt L g 10) :=
        ⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, by simp [setReg, PTX.next, b32], h10.2.2.2.2⟩
      by_cases hw0 : warpOf L g = 0
      · rw [hw0] at hmk ⊢
        obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 6 _ = some t2 ∧
            At t2 Flow.elect_0 (facts L g .elect0) := by
          pro_seg hmk hpre [land31]
        exact ⟨.elect0, t2, by simp [next, hw0], run_rtg hr2,
          ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩
      · have hlt : warpOf L g < 12 := warpOf_lt hpre
        obtain ⟨k, hk⟩ : ∃ k, warpOf L g = k := ⟨_, rfl⟩
        have hklt : k < 12 := by omega
        rw [hk] at hmk ⊢
        interval_cases k
        · exact absurd hk hw0
        all_goals
          obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 3 _ = some t2 ∧
              At t2 Flow.bar_0 (facts L g .barrier) := by
            pro_seg hmk hpre [land31]
          exact ⟨.barrier, t2, by simp [next, hk], run_rtg hr2,
            ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩
    · left; left; simp [next, hv]
  all_goals left; left; simp [next]

/-! ### The elections -/

/-- The first election: the elected lane converts the `param_1` address, adds the three
descriptor offsets, prefetches the three maps and reaches the second election; the other lanes
reach it through the four skipped instructions and the shared tail. The elected lane's path
needs the descriptor range (`hp1`). -/
theorem step_elect0 (hpre : Pre P L mem0) (hp1 : P.param1Base + 1024 ≤ 2 ^ 64)
    {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.elect_0 (facts L g .elect0))
    (hc : kernel.code[Flow.elect_0]? = some ins)
    (hf : Fires Flow.elect_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .elect0 u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
  obtain ⟨mk, inst, ld, he, hu⟩ := fires_elect hf
  subst he
  simp only [Option.elim] at hu
  rw [laneOf_core hpre] at hu
  subst hu
  have h1 := at_elect (d := 4071) (p := 4072) (x := .bits 32 (BitVec.ofNat 64 ld))
    (b := (laneOf L g == ld)) h (by decide +kernel) (by decide +kernel) (by decide)
  left; right
  by_cases hl : laneOf L g = ld
  · have hb : (laneOf L g == ld) = true := by simpa using hl
    rw [hb] at h1 ⊢
    obtain ⟨t21, hr21, h21⟩ : ∃ t21, run kernel asms L g 4 _ = some t21 ∧
        At t21 21 (factsAt L g 21) := by
      pro_seg h1 hpre
    obtain ⟨t28, hr28, h28⟩ := leader_run h21 hp1 hpre.param1Object hpre.mapQBind
      hpre.mapOBind hpre.mapKVBind
    obtain ⟨t31, hr31, h31⟩ : ∃ t31, run kernel asms L g 3 _ = some t31 ∧
        At t31 Flow.elect_1 (facts L g .elect1) := by
      pro_seg h28 hpre
    exact ⟨.elect1, t31, by simp [next], run_rtg (run_comp (run_comp hr21 hr28) hr31),
      ⟨h31.1, h31.2.1, h31.2.2.1, h31.2.2.2.1, h31.2.2.2.2⟩⟩
  · have hb : (laneOf L g == ld) = false := by simpa using hl
    rw [hb] at h1 ⊢
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 7 _ = some t2 ∧
        At t2 Flow.elect_1 (facts L g .elect1) := by
      pro_seg h1 hpre
    exact ⟨.elect1, t2, by simp [next], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩

/-- The second election: the elected lane initializes the barrier rings, the other lanes skip
the initializations and the allocation. -/
theorem step_elect1 (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.elect_1 (facts L g .elect1))
    (hc : kernel.code[Flow.elect_1]? = some ins)
    (hf : Fires Flow.elect_1 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .elect1 u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
  obtain ⟨mk, inst, ld, he, hu⟩ := fires_elect hf
  subst he
  simp only [Option.elim] at hu
  rw [laneOf_core hpre] at hu
  subst hu
  have h1 := at_elect (d := 4073) (p := 4074) (x := .bits 32 (BitVec.ofNat 64 ld))
    (b := (laneOf L g == ld)) h (by decide +kernel) (by decide +kernel) (by decide)
  left; right
  by_cases hl : laneOf L g = ld
  · have hb : (laneOf L g == ld) = true := by simpa using hl
    rw [hb] at h1 ⊢
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 7 _ = some t2 ∧
        At t2 (Site.pc (.init 0)) (facts L g (.init 0)) := by
      pro_seg h1 hpre
    exact ⟨.init 0, t2, by simp [next, hl], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩
  · have hb : (laneOf L g == ld) = false := by simpa using hl
    rw [hb] at h1 ⊢
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 7 _ = some t2 ∧
        At t2 Flow.tmemAlloc_0 (facts L g .alloc) := by
      pro_seg h1 hpre
    exact ⟨.alloc, t2, by simp [next, hl], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩

/-! ### The barrier initializations -/

def initNext (j : Fin 23) : Site :=
  if h : j.val + 1 < 23 then .init ⟨j.val + 1, h⟩ else .fence

def initLen : Fin 23 → Nat
  | ⟨0, _⟩ => 2
  | ⟨14, _⟩ => 2
  | ⟨15, _⟩ => 2
  | ⟨22, _⟩ => 0
  | ⟨_, _⟩ => 1

/-- The local code after initialization `j`: the next barrier's address and count, or the fence
after the last one. -/
theorem init_seg (hpre : Pre P L mem0) (j : Fin 23) {u : TState}
    (h1 : At u ((Site.init j).pc + 1) (facts L g (.init j))) :
    ∃ t', run kernel asms L g (initLen j) u = some t' ∧
      At t' (Site.pc (initNext j)) (facts L g (initNext j)) := by
  fin_cases j <;> pro_seg h1 hpre

/-- Warp 0's elected lane initializes barrier `j`; the thread continues in `next t`. -/
theorem step_init (hpre : Pre P L mem0) (j : Fin 23) {t u : TState} {e : Event} {ins : Instr}
    (h : At t (Site.init j).pc (facts L g (.init j)))
    (hc : kernel.code[(Site.init j).pc]? = some ins)
    (hf : Fires (Site.init j).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g (.init j) u e := by
  fin_cases j
  all_goals
    code_at hc
    subst hc
    obtain rfl := fires_next (show AdvancesOp (.mbarInit _ _ _) from trivial) hf
    left; right
    obtain ⟨t2, hr2, h2⟩ := init_seg hpre _ (At.next h)
    exact ⟨_, t2, by simp only [next, initNext], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩

/-- The fence of the initializations, then the allocation's address and count registers. -/
theorem step_fence (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.fenceMbarInit_0 (facts L g .fence))
    (hc : kernel.code[Flow.fenceMbarInit_0]? = some ins)
    (hf : Fires Flow.fenceMbarInit_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .fence u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
  obtain rfl := fires_next (show AdvancesOp .fenceMbarInit from trivial) hf
  left; right
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 3 _ = some t2 ∧
      At t2 Flow.tmemAlloc_0 (facts L g .alloc) := by
    pro_seg (At.next h) hpre
  exact ⟨.alloc, t2, by simp [next], run_rtg hr2,
    ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩

/-! ### The Tensor Memory allocation -/

/-- The allocation's request: lane 0 continues at the address store (sub-step 1), the other
lanes at the read-back. -/
theorem step_alloc (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.tmemAlloc_0 (facts L g .alloc))
    (hc : kernel.code[Flow.tmemAlloc_0]? = some ins)
    (hf : Fires Flow.tmemAlloc_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .alloc u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨dst, n, he, hu⟩ := fires_tcAlloc h.2.1 hf
  subst he
  rw [laneOf_core hpre] at hu
  left; right
  by_cases h0 : laneOf L g = 0
  · rw [ite_eq_left h0] at hu
    subst hu
    refine ⟨.allocStore, { t with sub := 1 }, by simp [next, h0], .refl, ?_⟩
    exact ⟨h.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · rw [ite_eq_right h0] at hu
    subst hu
    refine ⟨.allocRead, PTX.next t, by simp [next, h0], .refl, ?_⟩
    refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1,
      holds_factsFrom_mono h.2.2.2.2 (by table_decide)⟩
    show t.pc + 1 = Site.pc .allocRead
    rw [h.1]; rfl

/-- Lane 0's store of the allocated address, then the read-back. -/
theorem step_allocStore (_hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (hpc : t.pc = Flow.tmemAlloc_0) (hsub : t.sub = 1) (hacc : t.acc = [])
    (hflt : t.fault = none) (hregs : Holds t.regs (facts L g .allocStore))
    (hc : kernel.code[Flow.tmemAlloc_0]? = some ins)
    (hf : Fires Flow.tmemAlloc_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .allocStore u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨a, bs, he, hu⟩ := fires_tcAlloc_write hsub hf
  subst he
  subst hu
  left; right
  refine ⟨.allocRead, { t with pc := t.pc + 1, sub := 0 }, by simp [next], .refl, ?_⟩
  refine ⟨?_, rfl, hacc, hflt, holds_factsFrom_mono hregs (by table_decide)⟩
  show t.pc + 1 = Site.pc .allocRead
  rw [hpc]; rfl

/-- The read-back access of the allocated address: `ld.shared.b32` of the word at byte 222752. -/
def allocLoad : MemAccess :=
  { kind := .load, space := some (.shared (.cta)), sem := .weak, scope := none,
    elem := .int .b 32, vec := 1, ext := .same, nc := false, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .sharedSym 0, off := 222752 }, dsts := [some 557], srcs := [],
    mmio := false }

/-- The read-back of the allocated address: the thread continues to the relinquishment only when
the word read compares equal to zero. A nonzero result reaches `trap`. A failed rebuild or
integer read faults. Both outcomes are dead states of the thread machine. -/
theorem step_allocRead (_hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.load_0 (facts L g .allocRead))
    (hc : kernel.code[Flow.load_0]? = some ins)
    (hf : Fires Flow.load_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .allocRead u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
  change Fires Flow.load_0 (eventTmpl asms L g t (.mem allocLoad)) e (some u) at hf
  generalize ha : allocLoad = a at hf
  obtain ⟨r, bs, he, hu⟩ := fires_load (a := a) (hk := by rw [← ha]; rfl)
    (hnc := by rw [← ha]; rfl) hf (he := by rw [← ha]; rfl)
  rw [← ha] at hu
  simp only [allocLoad, MemAccess.regs, List.filterMap_cons, id_eq, List.filterMap_nil] at hu
  subst he
  subst hu
  cases hv : rebuild 3 bs with
  | error f =>
    refine Or.inr ⟨by simp [next, hv, bind, Except.bind], ?_⟩
    exact Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])
  | ok v =>
    let u₁ := afterLoad t [557] bs
    have hload := afterLoad_ok (d := 557) h.2.1 h.2.2.1 hv
    have hp₁ : u₁.pc = 93 := by simp [u₁, hload, h.1]
    have hf₁ : u₁.fault = none := by simpa [u₁, hload, setReg] using h.2.2.2.1
    have hr₁ : readBits L g u₁ 32 (.reg 557) = allocWord L g v := by
      simp [u₁, hload, setReg, allocWord, readBits, readReg]
    let cmpOp : Op := .int ⟨.setp .eq none, .int .b 32, false, [some 7], [.reg 557, .imm 0]⟩
    have hcmpCode : kernel.code[93]? = some ⟨none, cmpOp⟩ := Flow.code_93
    have hcmpRule : execLocalA asms L g u₁ cmpOp = execLocal L g u₁ cmpOp := by
      rw [execLocalA_noSegment (asms_segment_free u₁)]
      apply execLocalRule_of_none
      intro a ha
      simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | simp [Assumptions.paramPointers, hp₁,
        paramAdds, prefetchTensorMapSites, cmpOp, Assumptions.sharedBits,
        Assumptions.sharedBitsSites, Assumptions.deadPackRule, Assumptions.peerPackRule]
    have hcmp :
        out kernel asms L g u₁ =
          match allocWord L g v with
          | .error f => .ev (.ub f)
          | .ok x => .tau (PTX.next (setReg u₁ 7 (.pred (decide (x.toNat = 0))))) := by
      rw [out, hf₁, hp₁, hcmpCode]
      change (match execLocalA asms L g u₁ cmpOp with
        | .ok t' => Out.tau t'
        | .error f => Out.ev (.ub f)) = _
      rw [hcmpRule]
      change (match ((readBits L g u₁ 32 (.reg 557)).bind fun x =>
        .ok (PTX.next (setReg u₁ 7 (.pred (compare .eq .b 32 x 0))))) with
        | .ok t' => Out.tau t'
        | .error f => Out.ev (.ub f)) = _
      rw [hr₁]
      cases allocWord L g v <;> simp [Except.bind, compare]
    cases hx : allocWord L g v with
    | error f =>
      exact .inr ⟨by simp [next, hv, bind, Except.bind, hx],
        Machine.dead_of_ub (by simpa only [hx] using hcmp)⟩
    | ok x =>
      let u₂ := PTX.next (setReg u₁ 7 (.pred (decide (x.toNat = 0))))
      have hstep : Tau kernel asms L g u₁ u₂ := by
        change out kernel asms L g u₁ = .tau u₂
        simpa only [hx] using hcmp
      have hp₂ : u₂.pc = 94 := by simp [u₂, PTX.next, setReg, hp₁]
      have hf₂ : u₂.fault = none := by simpa [u₂, PTX.next, setReg] using hf₁
      have hguard : guardHolds u₂ (some (7, false)) = .ok (decide (x.toNat = 0)) := by
        simp [guardHolds, u₂, PTX.next, setReg, readReg, pure, Except.pure,
          bind, Except.bind]
      by_cases hz : x.toNat = 0
      · let u₃ := { u₂ with pc := 96 }
        have hbra : Tau kernel asms L g u₂ u₃ := by
          change out kernel asms L g u₂ = .tau u₃
          rw [out, hf₂, hp₂, Flow.code_94]
          simp only [hguard, decide_eq_true hz]
          change (match execLocalA asms L g u₂ (.bra 96 false) with
            | .ok t' => Out.tau t'
            | .error f => Out.ev (.ub f)) = _
          rw [execLocalA_noSegment (asms_segment_free u₂)]
          have hlocal : execLocalRule asms L g u₂ (.bra 96 false) =
              execLocal L g u₂ (.bra 96 false) := by
            apply execLocalRule_of_none
            intro a ha
            simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals first | rfl | simp [Assumptions.paramPointers, Assumptions.sharedBits,
              Assumptions.sharedBitsSites, Assumptions.deadPackRule, Assumptions.peerPackRule, hp₂]
          rw [hlocal]
          rfl
        refine .inl (.inr ⟨.relinquish, u₃, by simp [next, hv, bind, Except.bind, hx, hz],
          .head hstep (.single hbra), rfl, ?_, ?_, hf₂, ?_⟩)
        · simp [u₃, u₂, PTX.next, setReg, u₁, hload, Site.sub]
        · simp [u₃, u₂, PTX.next, setReg, u₁, hload]
        have hlive : liveAll 92 = liveAll 96 := by table_decide
        change Holds u₃.regs (factsAt L g 96)
        simp only [factsAt, u₃, u₂, PTX.next, u₁, hload]
        exact holds_update (holds_update (by
          simpa only [facts, Site.pc, Flow.load_0, factsAt, hlive] using h.2.2.2.2)
          (not_mem_factsFrom (by table_decide : 557 ∉ liveAll 96)))
          (not_mem_factsFrom (by table_decide : 7 ∉ liveAll 96))
      · have hskip : Tau kernel asms L g u₂ (skip u₂) := by
          change out kernel asms L g u₂ = .tau (skip u₂)
          rw [out, hf₂, hp₂, Flow.code_94]
          simp only [hguard, decide_eq_false hz]
        refine .inr ⟨by simp [next, hv, bind, Except.bind, hx, hz], ⟨skip u₂, .trap,
          .head hstep (.single hskip), ?_⟩⟩
        have hp₃ : (skip u₂).pc = 95 := by simp [skip, hp₂]
        have hf₃ : (skip u₂).fault = none := hf₂
        rw [out, hf₃, hp₃, Flow.code_95]
        rfl

/-- The relinquishment of the allocation permit, then the CTA barrier. -/
theorem step_relinquish (_hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.tmemRelinquish_0 (facts L g .relinquish))
    (hc : kernel.code[Flow.tmemRelinquish_0]? = some ins)
    (hf : Fires Flow.tmemRelinquish_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .relinquish u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.tcRelinquish _) from trivial) hf
  left; right
  have h97 : At (PTX.next t) 97 (factsAt L g 97) := by
    have hlive : liveAll 96 = liveAll 97 := by decide +kernel
    have h' := At.next h
    simp only [facts, factsAt, Site.pc, Flow.tmemRelinquish_0] at h' ⊢
    rw [hlive] at h'
    exact h'
  exact ⟨.barrier, PTX.next t, by simp [next], .refl,
    ⟨h97.1, h97.2.1, h97.2.2.1, h97.2.2.2.1, h97.2.2.2.2⟩⟩

/-- The CTA barrier, then the thread's role by its warpgroup index. -/
theorem step_barrier (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Flow.bar_0 (facts L g .barrier))
    (hc : kernel.code[Flow.bar_0]? = some ins)
    (hf : Fires Flow.bar_0 (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .barrier u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  left; right
  have h98 : At (PTX.next t) 98 (factsAt L g 97) := At.next h
  have hmk : At (PTX.next t) 98 ((462, b32 (wgOf L g)) :: factsAt L g 97) :=
    ⟨h98.1, h98.2.1, h98.2.2.1, h98.2.2.2.1, by
      have := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf L g) (r := 462) (by table_decide))
      simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, PTX.next] using this,
      h98.2.2.2.2⟩
  have hlt : wgOf L g < 3 := wgOf_lt hpre
  obtain ⟨k, hk⟩ : ∃ k, wgOf L g = k := ⟨_, rfl⟩
  have hklt : k < 3 := by omega
  rw [hk] at hmk
  interval_cases k
  · obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 5 _ = some t2 ∧
        At t2 (entryPc 0) (facts L g (.handoff 0)) := by
      pro_seg hmk hpre
    exact ⟨.handoff 0, t2, by simp [next, hk], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩
  · obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 _ = some t2 ∧
        At t2 (entryPc 1) (facts L g (.handoff 1)) := by
      pro_seg hmk hpre
    exact ⟨.handoff 1, t2, by simp [next, hk], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩
  · obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 5 _ = some t2 ∧
        At t2 (entryPc 2) (facts L g (.handoff 2)) := by
      pro_seg hmk hpre
    exact ⟨.handoff 2, t2, by simp [next, hk], run_rtg hr2,
      ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩⟩

/-- A hand-off state is the role's first event: the prologue machine stops following the thread. -/
theorem step_handoff (_hpre : Pre P L mem0) (wg : Fin 3) {t u : TState} {e : Event}
    {ins : Instr}
    (_h : At t (Site.pc (.handoff wg)) (facts L g (.handoff wg)))
    (_hc : kernel.code[(Site.pc (.handoff wg))]? = some ins)
    (_hf : Fires (Site.pc (.handoff wg)) (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g (.handoff wg) u e :=
  Or.inl (by simp [next])

/-! ### The machine's obligations -/

/-- A concrete state of a site is a concrete state of the code machine. -/
theorem good_code {s : Site} {t : TState} (h : Good L g s t) :
    (code L g).Good (some s) t :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, trivial⟩

/-- The step of a site, in the form the code machine's obligation takes. -/
theorem Step.code {s : Site} {u : TState} {e : Event} (h : Step L g s u e) :
    (((code L g).next s e = some none ∨ ∃ d' t', (code L g).next s e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code L g).Good (some d') t') ∨
      ((code L g).next s e = none ∧
        Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)) := by
  rcases h with (hn | ⟨s', t', hn, hr, hg⟩) | ⟨hn, hd⟩
  · exact .inl (.inl hn)
  · exact .inl (.inr ⟨s', t', hn, hr, good_code hg⟩)
  · exact .inr ⟨hn, hd⟩

/-- **The prologue machine's steps**: every site is an unguarded event instruction and every
continuing event reaches its successor's facts. The elected-lane branch of the first election
needs the descriptor range (`Param1Range`); every other site follows from `Pre` alone. -/
theorem steps_of_param1Range (hpre : Pre P L mem0) (hp1 : Param1Range P) :
    ∀ s : Site, (code L g).StepAt s := by
  intro s
  refine ⟨fun _ => ?_, ?_⟩
  · obtain ⟨ins, hcode, hnil, hg⟩ := site_ok s
    exact ⟨ins, hcode, hnil, by rw [hg]; trivial⟩
  intro t e u ins h _ hc hf
  cases s with
  | shfl0 => exact Step.code (step_shfl0 hpre ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | shfl1 => exact Step.code (step_shfl1 hpre ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | elect0 => exact Step.code (step_elect0 hpre hp1
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | elect1 => exact Step.code (step_elect1 hpre ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | init j => exact Step.code (step_init hpre j ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | fence => exact Step.code (step_fence hpre ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | alloc => exact Step.code (step_alloc hpre ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | allocStore => exact Step.code (step_allocStore hpre h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hc hf)
  | allocRead => exact Step.code (step_allocRead hpre
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | relinquish => exact Step.code (step_relinquish hpre
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | barrier => exact Step.code (step_barrier hpre ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)
  | handoff wg => exact Step.code (step_handoff hpre wg
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf)

/-- **The prologue's steps**, the form `Code.Sound` takes. -/
theorem steps (hpre : Pre P L mem0) (hp1 : Param1Range P) :
    ∀ s : Site, (code L g).StepAt s :=
  steps_of_param1Range hpre hp1

/-- **The prologue machine is sound**: it starts at the first shuffle (`start`) and every event
leads to its successor (`steps_of_param1Range`). -/
theorem sound_of_param1Range (hpre : Pre P L mem0) (hp1 : Param1Range P)
    (hg : g < L.threads) : (code L g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start (g := g) hpre hg
    exact ⟨t, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, trivial⟩
  steps := steps_of_param1Range hpre hp1

/-- **The prologue machine is sound**, the form the role machines use. -/
theorem sound (hpre : Pre P L mem0) (hp1 : Param1Range P) (hg : g < L.threads) :
    (code L g).Sound :=
  sound_of_param1Range hpre hp1 hg

/-- The prologue's steps under `Pre` alone: `Pre.param1Range` supplies the object bound. -/
theorem steps_pre (hpre : Pre P L mem0) : ∀ s : Site, (code L g).StepAt s :=
  steps hpre hpre.param1Range

/-- The prologue's soundness under `Pre` alone. -/
theorem sound_pre (hpre : Pre P L mem0) (hg : g < L.threads) : (code L g).Sound :=
  sound hpre hpre.param1Range hg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
