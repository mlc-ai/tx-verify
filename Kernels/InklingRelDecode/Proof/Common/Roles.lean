-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
public import Kernels.InklingRelDecode.Proof.Startup.Machine
public import Kernels.InklingRelDecode.Proof.Loader.Inputs
public import Kernels.InklingRelDecode.Proof.Mma.CollBalance
public import Kernels.InklingRelDecode.Proof.Common.Data
public import Kernels.InklingRelDecode.Proof.Common.Sites
public import Lemmas.Flow.PollRounds
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
inductive Role where
  | prologue (word : Value)
  | dispatch (word : Value) (x : BitVec 64)

def Role.entryPc : Role → Nat
  | .prologue .. => 27
  | .dispatch .. => 2337

inductive Worker where
  | loader (round : Nat)
  | mma (round : Nat)

def workerEntry (d : Dispatch.D) : Option Worker :=
  match d.site with
  | .loaderEntry => some (.loader d.round)
  | .mmaEntry => some (.mma d.round)
  | _ => none

def startRegs (Q : Params) (L : Launch) (g : Nat) (w : Value) (x : BitVec 64) :=
  Startup.valueOf Q L g ⟨.enter .worker, 0, x, w⟩

def dispatchRegs (Q : Params) (L : Launch) (g : Nat) (w : Value) (x : BitVec 64) :=
  Dispatch.valueOf L g x (startRegs Q L g w x)

@[reducible] def workerFrag (Q : Params) (L : Launch) (g : Nat) (w : Value) (x : BitVec 64) :
    Worker → Flow.Code kernel Assumptions.all L g
  | .loader _ => Loader.code L g w (Loader.inputs Q L g (dispatchRegs Q L g w x))
  | .mma _ => Mma.code L g (dispatchRegs Q L g w x) w

def workerBack (Q : Params) (L : Launch) (g : Nat) (w : Value) (x : BitVec 64) :
    (i : Worker) → (workerFrag Q L g w x i).D → Option Dispatch.D
  | .loader n, d => if d.site = .dispatch then some ⟨.head, n + 1⟩ else none
  | .mma n, d => if d.site = .dispatch then some ⟨.head, n + 1⟩ else none

@[reducible] def workerCode (Q : Params) (L : Launch) (g : Nat) (w : Value) (x : BitVec 64) :=
  Code.loopGlue (Dispatch.code L g (startRegs Q L g w x) x 0) (workerFrag Q L g w x)
    workerEntry (workerBack Q L g w x)

@[reducible] def frag (Q : Params) (L : Launch) (g : Nat) (r : Role) :
    Flow.Code kernel Assumptions.all L g :=
  match r with
  | .dispatch word x =>
    workerCode Q L g word x
  | .prologue word => dataCode Q L g word

def Startup.enterOf (d : Startup.D) : Option Startup.Entry :=
  match d.site with
  | .enter r => some r
  | _ => none

def sel (_ : Launch) (_ : Nat) : Startup.Entry → Startup.D → Option Role
  | .dp, d => some (.prologue d.w)
  | .worker, d => some (.dispatch d.w d.x)

/-- The classes of events the thread machine counts: warp shuffles (the instances of the warp
collectives), all events (the position in the trace), barriers by id (the CTA barrier 0 and the
named barrier 1), mbarrier initializations, arrivals, tensor copies, undefined behaviour, and the
proxy fences of the CTA's shared memory, the warp collectives and the Mma broadcasts that
received no 7. -/
inductive Cls where
  | atPc (pc : Nat)
  | poll (pc : Nat)
  | shfl
  | elect
  | voteAt (pc lane : Nat)
  | arrivalTo (object : Loc)
  | issueTo (object : Loc)
  | winner (lane : Nat)
  | all
  | bar (id : Nat)
  | init
  | arrive
  | coll
  | skip
  | copy
  | ub
  | fence
  deriving DecidableEq

/-- The events of each class. -/
def cls : Cls → Event → Bool
  | .atPc pc => fun event => event.pc == pc
  | .poll pc => okPollAt pc
  | .elect => fun e => match e.kind with | .elect .. => true | _ => false
  | .voteAt p l => fun e => e.pc == p && match e.kind with
    | .elect _ _ lead => lead == l
    | _ => false
  | .arrivalTo l => arrivesOn l
  | .issueTo l => issuesTo l
  | .winner l => fun e => match e.kind with | .elect _ _ lead => lead == l | _ => false
  | .shfl => Execution.isShfl
  | .all => fun _ => true
  | .bar i => fun e => match e.kind with | .bar j _ _ => j == i | _ => false
  | .coll => Sched.isWarpColl
  | .skip => Mma.skipEv
  | .init => fun e => match e.kind with | .mbInit _ _ => true | _ => false
  | .arrive => fun e => match e.kind with | .arrive .. => true | _ => false
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

end PTX.Kernels.InklingRelDecode.Proof
