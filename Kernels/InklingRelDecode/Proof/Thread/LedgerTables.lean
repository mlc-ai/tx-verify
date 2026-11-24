-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompAll
public import Kernels.InklingRelDecode.Proof.Thread.WCompAll

@[expose] public section

/-!
# The register requests and barrier-1 events of a thread, as a table of its abstract states

A thread's register requests (`setmaxnreg`) and its barrier-1 events (`barrier.sync 1`) are
separated by the same barriers in every run, and what the ledger of `RegSyncOf.lean` needs is
the count of each before a state. The count is a function of the state's site (and, in the
workers' dispatch loop, of the number of rounds): a state `s` has a phase `ph s = (r, b)`, the
requests and barrier-1 events of the thread before it in the first round, and `req s`, `b1 s`:
the request and the barrier-1 event the state's own instruction is (if any).

* default partition: `(0,0)` through the first `setmaxnreg.inc` (the prologue's first site),
  `(1,0)` in the prologue up to its `barrier.sync 1` (ordinal 0), `(1,1)` at the softmax region's
  `setmaxnreg.inc` (request 1), `(2,1)` at its first `barrier.sync 1` (ordinal 1), `(2,2)` in the
  rest of the region and the epilogue up to `barrier.sync 1` (ordinal 2), `(2,3)` at the
  epilogue's `setmaxnreg.inc` (request 2), `(3,3)` at the dispatch table's store and the last
  `barrier.sync 1` (ordinal 3), `(3,4)` after it;
* worker: `(0,0)` up to the dispatch loop's head, `(1,0)` at its `barrier.sync 1`, `(1,1)` at the
  load of the role byte and the role's first site (`setmaxnreg.dec`), `(2,1)` up to the role's
  first barrier, `(2,2)` in the role's body, `(2,3)` at the role's tail `setmaxnreg.inc`. A
  round of the loop adds `(3,3)`.

`Static` checks each table against the program text. The tables are defined by the sites'
constructors; nothing here names a pc in event form.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The register request of the instruction at `pc`: direction and count. -/
def reqAt (pc : Nat) : Option (Bool × Nat) :=
  match kernel.code[pc]? with
  | some ins =>
    match ins.op with
    | .setMaxReg i n => some (i, n)
    | _ => none
  | none => none

/-- Whether the instruction at `pc` is `barrier.sync 1` (or `bar.sync 1`). -/
def barAt (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ins =>
    match ins.op with
    | .barSync (.imm 1) _ => true
    | _ => false
  | none => false

/-! ### The default partition -/

def dstartReq : DStart.Site → Option (Bool × Nat)
  | .toProA => some (true, 256)
  | _ => none

def proReq : ProA.Site → Option (Bool × Nat)
  | .sMax => some (true, 256)
  | _ => none

def proB1 : ProA.Site → Bool
  | .bar18 => true
  | _ => false

def smReq : Sm.Site → Option (Bool × Nat)
  | .setMaxReg => some (true, 256)
  | _ => none

def smB1 : Sm.Site → Bool
  | .bar0 => true
  | _ => false

def epiReq : Epi.Site → Option (Bool × Nat)
  | .setMaxInc => some (true, 256)
  | _ => none

def epiB1 : Epi.Site → Bool
  | .bar1 | .bar2 => true
  | _ => false

theorem dstart_static (s : DStart.Site) : reqAt s.pc = dstartReq s ∧ barAt s.pc = false := by
  cases s <;> decide +kernel

theorem pro_static (s : ProA.Site) : reqAt s.pc = proReq s ∧ barAt s.pc = proB1 s := by
  cases s <;> decide +kernel

theorem sm_static (s : Sm.Site) : reqAt s.pc = smReq s ∧ barAt s.pc = smB1 s := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

theorem epi_static (s : Epi.Site) : reqAt s.pc = epiReq s ∧ barAt s.pc = epiB1 s := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

/-! ### The workers -/

def wReq : Worker.Site → Option (Bool × Nat)
  | .loop => some (true, 256)
  | .toIdle | .toLoader | .toMma => some (false, 24)
  | _ => none

def wB1 : Worker.Site → Bool
  | .bar2 | .bad0 | .bad1 => true
  | _ => false

def idleReq : Worker.Idle.Site → Option (Bool × Nat)
  | .dec => some (false, 24)
  | .inc => some (true, 256)
  | _ => none

def idleB1 : Worker.Idle.Site → Bool
  | .bar0 | .bar1 => true
  | _ => false

def loaderReq : Loader.Site → Option (Bool × Nat)
  | .setMaxDec => some (false, 24)
  | .setMaxInc => some (true, 256)
  | _ => none

def loaderB1 : Loader.Site → Bool
  | .bar0 | .bar1 => true
  | _ => false

def mmaReq : Mma.Site → Option (Bool × Nat)
  | .setMaxReg => some (false, 24)
  | .setMaxRegInc => some (true, 256)
  | _ => none

def mmaB1 : Mma.Site → Bool
  | .bar0 | .bar1 => true
  | _ => false

theorem worker_static (s : Worker.Site) : reqAt s.pc = wReq s ∧ barAt s.pc = wB1 s := by
  cases s <;> decide +kernel

theorem idle_static (s : Worker.Idle.Site) : reqAt s.pc = idleReq s ∧ barAt s.pc = idleB1 s := by
  cases s <;> decide +kernel

theorem loader_static (s : Loader.Site) : reqAt s.pc = loaderReq s ∧ barAt s.pc = loaderB1 s := by
  cases s <;> decide +kernel

theorem mma_static (s : Mma.Site) : reqAt s.pc = mmaReq s ∧ barAt s.pc = mmaB1 s := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

theorem exit_static (s : WComp.ExitSite) : reqAt s.pc = none ∧ barAt s.pc = false := by
  cases s <;> decide +kernel

/-! ### The phases -/

/-- One if the instruction is a register request, else zero. -/
def rInc (o : Option (Bool × Nat)) : Nat := if o.isSome then 1 else 0

/-- One if the instruction is `barrier.sync 1`, else zero. -/
def bInc (b : Bool) : Nat := if b then 1 else 0

/-- The phase `(requests, barrier-1 events)` of a default-partition state in its first (and only)
round. -/
def dPh : DComp.St → Nat × Nat
  | .dstart _ => (0, 0)
  | .pro d =>
    match d.site with
    | .sMax => (0, 0)
    | _ => (1, 0)
  | .sm d =>
    match d.site with
    | .setMaxReg => (1, 1)
    | .bar0 => (2, 1)
    | _ => (2, 2)
  | .epi d =>
    match d.site with
    | .setMaxInc => (2, 3)
    | .stTab | .bar2 => (3, 3)
    | .bar3 | .dealloc | .exit => (3, 4)
    | _ => (2, 2)

def dReq : DComp.St → Option (Bool × Nat)
  | .dstart d => dstartReq d.site
  | .pro d => proReq d.site
  | .sm d => smReq d.site
  | .epi d => epiReq d.site

def dB1 : DComp.St → Bool
  | .dstart _ => false
  | .pro d => proB1 d.site
  | .sm d => smB1 d.site
  | .epi d => epiB1 d.site

theorem d_static (s : DComp.St) : reqAt (DComp.pc s) = dReq s ∧ barAt (DComp.pc s) = dB1 s := by
  cases s with
  | dstart d => exact dstart_static d.site
  | pro d => exact pro_static d.site
  | sm d => exact sm_static d.site
  | epi d => exact epi_static d.site

/-- The phase of a worker state within one round of the dispatch loop (the loop's head is
`(0,0)`; a role's tail leaves `(3,3)`, the next round's `(0,0)` plus one round). The bad sites
`bad0`, `bad1` (a role byte above 3) have the counts of their first round (one request, one and
two barrier-1 events); the loop head they return to has made one request and three barrier-1
events, which is no phase of the table (a round of the table has three requests), so the
invariants built on the table exclude the bad sites (`wTo`). -/
def wPh : WComp.WSt → Nat × Nat
  | .worker w =>
    match w.site with
    | .bar2 => (1, 0)
    | .ldRole | .toIdle | .toLoader | .toMma | .toExit | .bad0 => (1, 1)
    | .bad1 => (1, 2)
    | _ => (0, 0)
  | .idle d =>
    match d.site with
    | .dec => (1, 1)
    | .bar0 => (2, 1)
    | .bar1 => (2, 2)
    | .inc => (2, 3)
  | .loader d _ =>
    match d.site with
    | .setMaxDec => (1, 1)
    | .ld0 | .ld1 | .bar0 => (2, 1)
    | .setMaxInc => (2, 3)
    | _ => (2, 2)
  | .mma d _ =>
    match d.site with
    | .setMaxReg => (1, 1)
    | .ldNum | .bar0 => (2, 1)
    | .setMaxRegInc => (2, 3)
    | _ => (2, 2)
  | .exit _ => (1, 1)

def wReqS : WComp.WSt → Option (Bool × Nat)
  | .worker w => wReq w.site
  | .idle d => idleReq d.site
  | .loader d _ => loaderReq d.site
  | .mma d _ => mmaReq d.site
  | .exit _ => none

def wB1S : WComp.WSt → Bool
  | .worker w => wB1 w.site
  | .idle d => idleB1 d.site
  | .loader d _ => loaderB1 d.site
  | .mma d _ => mmaB1 d.site
  | .exit _ => false

theorem w_static (s : WComp.WSt) :
    reqAt (WComp.pc s) = wReqS s ∧ barAt (WComp.pc s) = wB1S s := by
  cases s with
  | worker w => exact worker_static w.site
  | idle d => exact idle_static d.site
  | loader d _ => exact loader_static d.site
  | mma d _ => exact mma_static d.site
  | exit x => exact exit_static x.site

end
end PTX.Kernels.InklingRelDecode.Proof.Ledger
