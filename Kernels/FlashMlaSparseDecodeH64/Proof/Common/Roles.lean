-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Machine
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.Roles
public import Lemmas.Tmem.PairProtocol
public import Tactics.KernelRfl

@[expose] public section

/-! # The roles of the FlashMLA kernel and the thread machine glued from them

Every thread runs the startup (pcs 0–102) and then the warpgroup its exit selects: warpgroup 0
(`wg0`, pc 103), warpgroup 1 (`wg1`, pc 1842) or warpgroup 2 (`dequant`, pc 2606). Warpgroup 1
dispatches once more, on the shuffled warp index, to the MMA warp (`mma`, pc 1853), the TMA warp
(`tma`, pc 2162), the index warp (`index`, pc 2332) or the idle code (`idle`, pc 2587); its head and
the idle code are the `Wg1` role. The regions are `Common/Sites.lean`.

**The glue** (`Lemmas/Flow/Roles.lean`). `thread` is `Code.roleThread` of the startup's fragment
and the three warpgroups' fragments, with the ghost ledger of the classes `Cls`; warpgroup 1's
fragment is `Code.roleLoop` of its head and its four sub-roles. The entries' gates are `sel` and
`subSel`: an entry whose gate fails, or whose fragment the startup does not enter, is a stub that
stops at its first event (`Code.stop`).

**The slots.** Each role has one slot below, a fragment that stops at its
first event: `startupCode` (whose exits `startupEnter` are none, so no thread leaves it),
`wg0Code`, `dequantCode`, `wg1HeadCode` (whose exits `wg1Enter` are none), `mmaCode`, `tmaCode`,
`indexCode` and `idleCode`. A role lane replaces its slot, one at a time:

1. replace the body of its slot by its machine (`<Role>.code P L g`, imported from
   `<Role>/Machine.lean`; the slot's unused `_P` binder becomes `P`), and for the startup and
   the warpgroup 1 head the exit map (`startupEnter`, `wg1Enter`) by the machine's exit states;
2. its entry's gate in `sel` (or `subSel`) is in place: the startup's entries pass when the
   recorded words are the launch's, and warpgroup 0 and 2 are entered with the launch's warp
   word (`warpW L g`, the stub's `_w`); the sub-entries pass on the launch's warp (`subOk`);
3. if its machine needs counts of the thread's events, add a constructor to `Cls` and its case
   to `cls` (a class is never removed);
4. replace its slots in `Common/Table.lean` (`<role>J`, `<role>Ev`) by its reference invariant and
   shape table, and add its hand-off (the concrete state of the previous fragment's exit state is
   one of its first state) to the soundness proof.

Nothing else in this file changes; no file above `Common/` names a slot. -/

/-! # The role regions of the FlashMLA kernel, as data

The kernel's 3,612 instructions split into a startup that every thread runs and the code of six
roles. Each fragment has a region of the code (half-open intervals) and the pcs where control may
leave it (`RoleDecl`); the table is read from the PTX (labels, branches and the warp tests of the
two dispatches):

| fragment | threads | region | exits |
|---|---|---|---|
| startup | all 384 | 0–103 | 103, 1842, 2606 |
| warpgroup 0 (`Wg0`) | warps 0–3 | 103–1841 (loop 103–1146, epilogue 1147–1841) | 3611 |
| warpgroup 1 head (`Wg1`) | warps 4–7 | 1842–1850 | 1850, 2162, 2332, 2587 |
| MMA (`Mma`) | warp 4, elected lane | 1850–2161 | 2162, 2332, 2587, 3611 |
| TMA (`Tma`) | warp 5, elected lane | 2162–2331 | 2332, 2587, 3611 |
| index (`Index`) | warp 7 | 2332–2586 | 2587, 3611 |
| warpgroup 1 idle (`Wg1`) | warp 6, the other lanes of 4 and 5 | 2587–2605 | 3611 |
| warpgroup 2 (`Dequant`) | warps 8–11 | 2606–3610 | 3611 |

The startup ends at the CTA barrier's dispatch on the shuffled warpgroup index, which reaches the
`setmaxnreg` of warpgroup 0 (103), 1 (1842) or 2 (2606). Warpgroup 1 dispatches once more on the
shuffled warp index (1844–1849). A role region contains the dispatch tests that follow its code (a
finished role walks the remaining tests to the common `ret` at 3611); the first instructions of
the roles those tests could reach are its exits, which the role's own facts on the warp index
exclude. The MMA and TMA warps' lanes that lose their election continue in the idle code, so 2587
is an exit of both. `closed` checks every region on the decoded program by evaluation and
`covered` that the regions cover the code.

**Entries are event instructions.** A fragment's first state, and so the pc its dispatch passes
to (`Entry.pc`, `SubEntry.pc` in `Common/Roles.lean`), is the role's first *event* instruction: a
code machine has states only at event instructions, and a stub at an entry fires its event
(`StubSite`). The local prefix before it (warpgroup 1's moves of the election masks at 1850–1852
and 2162–2164, the idle code's parameter loads and tests at 2587–2595) is walked by the step of the
previous fragment's last event. The warpgroups' entries 103, 1842 and 2606 are their `setmaxnreg`;
the MMA and TMA warps' are their elections (1853, 2165); the idle code's is the first of its
events the launch reaches (`idleFirst`, `Lib/Idle.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Sites
open PTX PTX.Flow

def startup : RoleDecl := ⟨[(0, 104), (1842, 1843), (2606, 2607)], [103, 1842, 2606]⟩

def wg0 : RoleDecl := ⟨[(103, 1842), (3611, 3612)], [3611]⟩

def wg1Head : RoleDecl :=
  ⟨[(1842, 1851), (2162, 2163), (2332, 2333), (2587, 2588)], [1850, 2162, 2332, 2587]⟩

def mma : RoleDecl :=
  ⟨[(1850, 2163), (2332, 2333), (2587, 2588), (3611, 3612)], [2162, 2332, 2587, 3611]⟩

def tma : RoleDecl := ⟨[(2162, 2333), (2587, 2588), (3611, 3612)], [2332, 2587, 3611]⟩

def index : RoleDecl := ⟨[(2332, 2588), (3611, 3612)], [2587, 3611]⟩

def wg1Idle : RoleDecl := ⟨[(2587, 2606), (3611, 3612)], [3611]⟩

def dequant : RoleDecl := ⟨[(2606, 3612)], [3611]⟩

/-- All fragments. -/
def all : List RoleDecl := [startup, wg0, wg1Head, mma, tma, index, wg1Idle, dequant]

/-- **Every region is closed up to its exits.** -/
theorem closed : all.all (RoleDecl.closed kernel) = true := by
  kernel_rfl

/-- **The regions cover the code**: every pc of the program lies in a region. -/
theorem covered : (List.range 3612).all (fun pc =>
    all.any (fun d => CodeCheck.inRegion d.region pc)) = true := by
  decide +kernel

/-- The program has 3,612 instructions, the last the `ret` at 3611 every role exits through. -/
theorem code_length : kernel.code.length = 3612 := kernel_code_length

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Sites

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The roles -/

/-- **The roles of the kernel**, one per lane directory. -/
inductive RoleName where
  | startup
  | wg1
  | index
  | tma
  | mma
  | dequant
  | wg0
  deriving DecidableEq, Repr

/-- The roles. -/
def RoleName.all : List RoleName := [.startup, .wg1, .index, .tma, .mma, .dequant, .wg0]

/-- The regions of each role's code (`Common/Sites.lean`). -/
def RoleName.decls : RoleName → List RoleDecl
  | .startup => [Sites.startup]
  | .wg1 => [Sites.wg1Head, Sites.wg1Idle]
  | .index => [Sites.index]
  | .tma => [Sites.tma]
  | .mma => [Sites.mma]
  | .dequant => [Sites.dequant]
  | .wg0 => [Sites.wg0]

/-- The role a thread runs after the startup, by its warp index `w` (`warpOf`) and, in warps 4
and 5, whether the lane won its warp's election: warps 0–3 run warpgroup 0, the elected lane of
warp 4 the MMA code and of warp 5 the TMA code, warp 7 the index code, warps 8–11 warpgroup 2,
and warp 6 and the other lanes of warps 4 and 5 the idle code of warpgroup 1. -/
def roleOfWarp (w : Nat) (elected : Bool) : RoleName :=
  if w < 4 then .wg0
  else if w = 4 then (if elected then .mma else .wg1)
  else if w = 5 then (if elected then .tma else .wg1)
  else if w = 7 then .index
  else if w < 8 then .wg1
  else .dequant

/-- The role of thread `g` after the startup. -/
def roleOf (L : Launch) (g : Nat) (elected : Bool) : RoleName := roleOfWarp (warpOf L g) elected

/-! ### Entries -/

/-- The entries of the startup's dispatch. -/
inductive Entry where
  | wg0
  | wg1
  | dequant
  deriving DecidableEq, Repr

/-- The first pc of an entry: its warpgroup's `setmaxnreg`. -/
def Entry.pc : Entry → Nat
  | .wg0 => 103
  | .wg1 => 1842
  | .dequant => 2606

/-- The entries of warpgroup 1's dispatch. -/
inductive SubEntry where
  | mma
  | tma
  | index
  | idle
  deriving DecidableEq, Repr

/-- The first pc of a sub-entry: the sub-role's first event instruction (the head walks the
local prefix before it). The idle code's and the index warp's depend on the launch
(`idleFirst`, `ixFirst`). -/
def SubEntry.pc (P : Params) (L : Launch) (g : Nat) : SubEntry → Nat
  | .mma => 1853
  | .tma => 2165
  | .index => (ixFirst P L g).1.pc
  | .idle => (idleFirst P L g).pc

/-! ### The slots: one fragment per role (the startup, warpgroup 1's head and idle code, the MMA
and TMA warps, the index warp, and warpgroups 0 and 2 are real) -/

/-- **Slot `Startup`**: the startup's fragment. -/
@[reducible] def startupCode (_P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Startup.code L g

/-- **Slot `Startup`**: the startup's exit states and the entry each passes to. -/
def startupEnter (_P : Params) (L : Launch) (g : Nat) :
    (startupCode _P L g).D → Option Entry :=
  fun d => (Startup.exitOf d).map fun
    | .wg0 => .wg0
    | .wg1 => .wg1
    | .wg2 => .dequant

/-- **Slot `Wg0`**: warpgroup 0's fragment, entered with the warp word `w`: the word the
startup's second shuffle recorded, which the gate `sel` checks to be the launch's (`warpW L g`),
so `frag` passes `warpW L g`: warpgroup 0's control machine (`Wg0/Control/Machine.lean`). -/
@[reducible] def wg0Code (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code kernel Assumptions.all L g :=
  Wg0.Control.code P L g w

/-- **Slot `Dequant`**: warpgroup 2's fragment (`Dequant/Control/Machine.lean`), entered with
the warp word `w` (as `wg0Code`). -/
@[reducible] def dequantCode (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code kernel Assumptions.all L g :=
  Dequant.Control.code P L g w

/-- **Slot `Wg1`**: warpgroup 1's head (the dispatch on the warp index). -/
@[reducible] def wg1HeadCode (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Wg1.code P L g

/-- **Slot `Wg1`**: the head's exit states and the sub-entry each passes to. -/
def wg1Enter (P : Params) (L : Launch) (g : Nat) :
    (wg1HeadCode P L g).D → Option SubEntry :=
  fun d => (Wg1.exitOf d).map fun
    | .mma => .mma
    | .tma => .tma
    | .index => .index
    | .idle => .idle

/-- **Slot `Wg1`**: the idle code. -/
@[reducible] def idleCode (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Wg1.idle P L g

/-- **Slot `Mma`**: the MMA warp's fragment (`Mma/Machine.lean`), from its election at pc 1853:
the head runs the three moves at 1850–1852 before it. -/
@[reducible] def mmaCode (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Mma.code P L g

/-- **Slot `Tma`**: the TMA warp's fragment (`Tma/Machine.lean`), from its election at pc 2165:
the head runs the three moves at 2162–2164 before it. -/
@[reducible] def tmaCode (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Tma.code P L g

/-- **Slot `Index`**: the index warp's fragment (`Index/Machine.lean`), from its first event
`ixFirst`: the head walks the parameter prefix (pcs 2332–2359) before it. -/
@[reducible] def indexCode (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Index.code P L g

/-! ### The glue -/

/-- The sub-roles of warpgroup 1. -/
@[reducible] def subFrag (P : Params) (L : Launch) (g : Nat) :
    SubEntry → Code kernel Assumptions.all L g
  | .mma => mmaCode P L g
  | .tma => tmaCode P L g
  | .index => indexCode P L g
  | .idle => idleCode P L g

/-- The launch's warp for each sub-role: the head's word (the warp index lane 0 sent) is `4` at
the MMA exit, `5` at the TMA exit and `7` for the index code; the idle exit is reached on any
other word of warpgroup 1 (warp 6) or by a lane of warp 4 or 5 that lost its election. -/
def subOk (L : Launch) (g : Nat) : SubEntry → Bool
  | .mma => warpOf L g == 4
  | .tma => warpOf L g == 5
  | .index => warpOf L g == 7
  | .idle => 4 ≤ warpOf L g && warpOf L g < 7

/-- The gates of warpgroup 1's dispatch: the sub-role each exit state enters, when the launch's
warp is the one the head's word selected (`subOk`). In an execution the gate passes: the head's
shuffle returns the launch's warp word (`Common/Recv.lean`). -/
def subSel (P : Params) (L : Launch) (g : Nat) :
    SubEntry → (wg1HeadCode P L g).D → Option SubEntry :=
  fun r _ => if subOk L g r then some r else none

/-- The returns to the head: an MMA or TMA lane that lost its election, at the idle code's first
event (`Mma.Site.leave (idleFirst P L g)`, `Tma.Site.leave …`), enters the idle code through the
head's idle exit. -/
def subBack (P : Params) (L : Launch) (g : Nat) :
    (i : SubEntry) → (subFrag P L g i).D → Option (wg1HeadCode P L g).D
  | .mma => fun d => if d.site = .leave (idleFirst P L g) then some Wg1.Site.idle else none
  | .tma => fun d => if d.site = .leave (idleFirst P L g) then some Wg1.Site.idle else none
  | _ => fun _ => none

/-- **Warpgroup 1**: its head, then the sub-role its exit selects. -/
@[reducible] def wg1Code (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Code.roleLoop (wg1HeadCode P L g) (subFrag P L g) (SubEntry.pc P L g) (wg1Enter P L g)
    (subSel P L g) (subBack P L g)

/-- The fragment of each entry of the startup's dispatch. -/
@[reducible] def frag (P : Params) (L : Launch) (g : Nat) :
    Entry → Code kernel Assumptions.all L g
  | .wg0 => wg0Code P L g (warpW L g)
  | .wg1 => wg1Code P L g
  | .dequant => dequantCode P L g (warpW L g)

/-- **The gates of the startup's dispatch**: an exit state enters its fragment when the two words
the startup's shuffles recorded are the launch's (`wgW`, `warpW`); the fragments are entered with
the launch's warp word. In an execution the gate passes (`Common/Recv.lean`): a shuffle returns
the word its source lane sent. -/
def sel (P : Params) (L : Launch) (g : Nat) :
    Entry → (startupCode P L g).D → Option Entry :=
  fun r d => if d.x1 = wgW L g ∧ d.x2 = warpW L g then some r else none

/-! ### The ghost ledger -/

/-- **The classes of events the thread machine counts**: all events (the position in the
trace), the warp shuffles (the instances of the warp collectives) and undefined behaviour. A role
lane adds the classes its reference invariant counts. -/
inductive Cls where
  | all
  | shfl
  | ub
  /-- The mbarrier initializations (the startup's ledger). -/
  | mbInit
  /-- The events on CTA barrier 0 (the startup's barrier). -/
  | bar0
  /-- The paired Tensor Memory operations (the startup's and warpgroup 0's `RefT`, `TmemAt`). -/
  | tmem
  /-- The MMA warp's classes (`Mma/Cnt.lean`). -/
  | mma (c : Mma.Cnt)
  /-- Warpgroup 2's classes (`Dequant/Cnt.lean`). -/
  | dequant (c : Dequant.Cnt)
  /-- The TMA warp's classes (`Tma/Cnt.lean`). -/
  | tma (c : Tma.Cnt)
  /-- The index warp's classes (`Index/Cnt.lean`). -/
  | index (c : Index.Cnt)
  /-- Warpgroup 0's classes (`Wg0/Cnt.lean`). -/
  | wg0 (c : Wg0.Cnt)
  deriving DecidableEq, Repr

/-- The events of each class. -/
def cls : Cls → Event → Bool
  | .all => fun _ => true
  | .shfl => Execution.isShfl
  | .ub => fun e => match e.kind with | .ub _ => true | _ => false
  | .mbInit => isMbInit
  | .bar0 => isBar0
  | .tmem => Tmem.Pair.isTmemOp
  | .mma c => Mma.cls c
  | .dequant c => Dequant.cls c
  | .tma c => Tma.cls c
  | .index c => Index.cls c
  | .wg0 c => Wg0.cls c

/-- **The thread machine**: the startup, then the role its exit selects (or a stub), with the
ghost ledger. -/
@[reducible] def thread (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Code.roleThread (startupCode P L g) (frag P L g) Entry.pc (startupEnter P L g) (sel P L g) cls

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
