-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Startup.Machine
public import Kernels.InklingRelDecode.Proof2.ProA.Machine
public import Kernels.InklingRelDecode.Proof2.Tail.Machine
public import Kernels.InklingRelDecode.Proof2.Worker.Machine
public import Kernels.InklingRelDecode.Proof.Thread.SmEntryBase
public import Lemmas.Flow.Roles
public import Lemmas.Kernel.CodeCheck
public import Tactics.KernelRfl
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The roles of Inkling and the thread machine glued from them

Every thread runs the startup (`Proof2/Startup`) to the branch on the warp index it received
(pc 19), and then one of two roles, read off the PTX's control flow:

* **the default partition** (`Entry.dp`, pc 27 on): the prologue (pc 27 to 573,
  `Proof2/ProA`), the softmax region (pc 574 to 2330 with its loop, and its exit to pc 2560) and
  the epilogue (pc 2565 to 2852, its return at 2855); three fragments in sequence;
* **the workers** (`Entry.worker`, pc 2337 on): the dispatch loop (pc 2337 to 2343, a byte read
  at pc 2340 and a `brx.idx` on it), whose targets are the loader (pc 2344 to 2421), the MMA
  warp's code (pc 2422 to 2556), the idle role (pc 2333 to 2336), the exit path (pc 2853 to 2855)
  and, for a byte above 3, a pair of barriers (pc 2557 to 2559); every role but the exit path
  returns to the dispatch loop's head.

**Regions as data.** Each fragment has a region of the code (half-open intervals) and the pcs where
control leaves it (`Decl`). `closed` checks, by evaluation of the decoded program, that every
instruction of a region other than its exits continues inside it, and `*_sites` lists a region's
event instructions, which are the fragment's sites (`site_mem`). The regions of the fragments not
yet migrated are declared and checked as well, so the role table is complete.

**Glue.** The startup's exit `enter r` enters role `r` when its gate holds (`Gate`: the received
word is the thread's warp index, which the role's invariant needs), else the stub of `r`. The
default partition's role index carries the base word the startup recorded (`Role.dp tm w`: its
number and the register's value as loaded): a value
the startup returns flows into the role through the index, so the role's first state needs no closed
form of it. Inside the default partition the prologue's exit (pc 574) enters the softmax–epilogue
fragment (`Tail.code`) when the gate on the prologue's words holds (`TailGate`), else a stub. The
workers enter the worker fragment at the dispatch loop's head (`Worker.code`) when their gate
holds (`WGate`). The thread machine counts the events of each class `Cls` (`Code.counted`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

/-! ### Regions and exits -/

/-- A fragment's region of the code and the pcs where control may leave it. -/
structure Decl where
  region : List (Nat × Nat)
  exits : List Nat

def startupDecl : Decl := ⟨[(0, 28), (2331, 2333), (2337, 2338)], [27, 2337]⟩
def proADecl : Decl := ⟨[(27, 575)], [574]⟩
def smDecl : Decl := ⟨[(574, 2331), (2560, 2566)], [2565]⟩
def epiDecl : Decl := ⟨[(2565, 2853), (2855, 2856)], []⟩
def dispatchDecl : Decl :=
  ⟨[(2337, 2345), (2422, 2423), (2333, 2334), (2853, 2854), (2557, 2558)],
    [2344, 2422, 2333, 2853, 2557]⟩
def loaderDecl : Decl := ⟨[(2344, 2422), (2337, 2338)], [2337]⟩
def mmaDecl : Decl := ⟨[(2422, 2557), (2337, 2338)], [2337]⟩
def idleDecl : Decl := ⟨[(2333, 2338)], [2337]⟩
def badRoleDecl : Decl := ⟨[(2557, 2560), (2337, 2338)], [2337]⟩
def workerExitDecl : Decl := ⟨[(2853, 2856)], []⟩

/-- Every region is closed up to its exits. -/
theorem closed : [startupDecl, proADecl, smDecl, epiDecl, dispatchDecl, loaderDecl, mmaDecl,
    idleDecl, badRoleDecl, workerExitDecl].all
    (fun d => CodeCheck.closedFrom d.region d.exits 0 kernel.code) = true := by
  kernel_rfl

/-- The startup's event instructions: its sites and the two roles' first instructions. -/
def startupSites : List Nat := [11, 12, 13, 14, 15, 17, 27, 2337]

theorem startup_sites : CodeCheck.sitesFrom startupDecl.region 0 kernel.code = startupSites := by
  kernel_rfl

theorem Startup.site_mem (s : Startup.Site) : s.pc ∈ startupSites := by
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

/-- The prologue's event instructions: its sites and the softmax region's first instruction. -/
def proASites : List Nat :=
  [27, 34, 37, 41, 130, 134, 135, 138, 139, 142, 143, 146, 147, 150, 151, 154, 155, 158,
    159, 162, 163, 166, 167, 170, 171, 174, 175, 178, 179, 180, 192, 193, 197, 201, 202, 203,
    211, 212, 213, 217, 220, 222, 223, 226, 227, 228, 231, 236, 237, 241, 243, 244, 245, 253,
    254, 255, 259, 262, 264, 265, 268, 269, 270, 273, 278, 279, 283, 285, 286, 287, 295, 296,
    297, 301, 304, 306, 307, 310, 311, 312, 315, 388, 390, 392, 394, 396, 398, 400, 402, 404,
    406, 408, 410, 412, 414, 416, 418, 420, 422, 424, 426, 428, 430, 432, 434, 436, 438, 440,
    442, 444, 446, 448, 450, 452, 454, 456, 458, 460, 462, 464, 466, 468, 470, 472, 474, 476,
    478, 480, 482, 484, 486, 488, 490, 492, 494, 496, 498, 500, 502, 504, 506, 508, 510, 512,
    514, 526, 532, 538, 544, 550, 556, 562, 568, 569, 570, 571, 573, 574]

theorem proA_sites : CodeCheck.sitesFrom proADecl.region 0 kernel.code = proASites := by
  kernel_rfl

theorem ProA.site_mem (s : ProA.Site) : s.pc ∈ proASites := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => fin_cases k <;> decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j => fin_cases b <;> fin_cases j <;> decide
  | _ => decide

/-! ### The glue -/

/-- The prologue's exit: its state `exit` enters the softmax region. -/
def ProA.exitOf (d : ProA.D) : Option Unit :=
  match d.site with
  | .exit => some ()
  | _ => none

/-- The prologue's words the softmax region's first state relies on (the hand-off's gate): the
inherited registers of base word 0, the request's three words, and the base word register. -/
def TailGate (Q : Params) (L : Launch) (g : Nat) (dt : Proof.ProA.Dat) : Prop :=
  dt.pro = Startup.inh L g Q 0 ∧ Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) dt ∧
    dt.w = b32 0

open scoped Classical in
/-- The prologue's exit enters the softmax–epilogue fragment with its data when the gate holds,
else the stub at pc 574. -/
def ProA.selTail (Q : Params) (L : Launch) (g : Nat) (_ : Unit) (d : ProA.D) :
    Option Proof.ProA.Dat :=
  if TailGate Q L g d.dt then some d.dt else none

/-- The softmax region's first state from the prologue's data (`SmEntry.d0`). -/
abbrev tailInit (Q : Params) (L : Launch) (g : Nat) (dt : Proof.ProA.Dat) : Proof.Sm.D :=
  Proof.SmEntry.d0 (Proof.SmEntry.entOf Q L g dt)

/-- The default partition: the prologue with the inherited registers of base word `tm` and the
base word register's value `w`, then the softmax region, the bridge and the epilogue
(`Tail.code`), entered through the gate. -/
@[reducible] def dpCode (Q : Params) (L : Launch) (g tm : Nat) (w : Value) :
    Flow.Code kernel Assumptions.all L g :=
  Code.glue (ProA.code L g (Startup.inh L g Q tm) w)
    (Code.withStubs (fun dt => Tail.code L g (tailInit Q L g dt)) (fun _ : Unit => 574))
    (Code.gatedExit ProA.exitOf (ProA.selTail Q L g))

/-- The migrated roles: the default partition and the workers, each with the base word the
startup recorded. -/
inductive Role where
  | dp (tm : Nat) (w : Value)
  | worker (w : Value)

/-- The fragment of each migrated role. -/
@[reducible] def frag (Q : Params) (L : Launch) (g : Nat) :
    Role → Flow.Code kernel Assumptions.all L g
  | .dp tm w => dpCode Q L g tm w
  | .worker w => Worker.code Q L g w

/-- The startup's exits: the state `enter r` passes to entry `r`. -/
def Startup.enterOf (d : Startup.D) : Option Startup.Entry :=
  match d.site with
  | .enter r => some r
  | _ => none

/-- The startup's words a role relies on: the received word is the thread's warp index, and the
thread is in warps 0 to 3 (the default partition's invariant needs it). -/
def Gate (L : Launch) (g : Nat) (d : Startup.D) : Bool :=
  d.x == BitVec.ofNat 64 (g % L.block / 32) && decide (g % L.block < 128)

/-- The workers' gate: the received word is the thread's warp index, and the thread is in warps 4
and above (the worker machine's invariant needs it). -/
def WGate (L : Launch) (g : Nat) (d : Startup.D) : Bool :=
  d.x == BitVec.ofNat 64 (g % L.block / 32) && decide (4 ≤ g % L.block / 32)

/-- The migrated role an entry enters when its gate holds. -/
def sel (L : Launch) (g : Nat) : Startup.Entry → Startup.D → Option Role
  | .dp, d => if Gate L g d then some (.dp d.tm d.w) else none
  | .worker, d => if WGate L g d then some (.worker d.w) else none

/-! ### The ghost ledger -/

/-- The classes of events the thread machine counts: warp shuffles (the instances of the warp
collectives), all events (the position in the trace), barriers by id (the CTA barrier 0 and the
named barrier 1), mbarrier initializations, arrivals, tensor copies, undefined behaviour, and the
proxy fences of the CTA's shared memory. -/
inductive Cls where
  | shfl
  | all
  | bar (id : Nat)
  | init
  | arrive
  | copy
  | ub
  | fence
  deriving DecidableEq

/-- The events of each class. -/
def cls : Cls → Event → Bool
  | .shfl => Execution.isShfl
  | .all => fun _ => true
  | .bar i => fun e => match e.kind with | .bar j _ _ => j == i | _ => false
  | .init => fun e => match e.kind with | .mbInit _ _ => true | _ => false
  | .arrive => fun e => match e.kind with | .rmw _ _ _ => true | _ => false
  | .copy => fun e => match e.kind with | .tensorIssue _ _ => true | _ => false
  | .ub => fun e => match e.kind with | .ub _ => true | _ => false
  | .fence => fun e => match e.kind with
    | .fenceProxy (.async (some (.shared .cta))) none => true
    | _ => false

/-- **The thread machine**: the startup, then the role its exit selects (or a stub), with the
ghost ledger (`Code.roleThread`). -/
@[reducible] def thread (Q : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g :=
  Code.roleThread (Startup.code Q L g) (frag Q L g) Startup.Entry.pc Startup.enterOf (sel L g) cls

end
end PTX.Kernels.InklingRelDecode.Proof2
