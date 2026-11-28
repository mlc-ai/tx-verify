-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Base
public import Lemmas.Flow.Roles

@[expose] public section

/-! # The startup of every thread as a site machine

Every thread of the CTA runs the same code from its first instruction to the branch on the warp
index (pc 19). The ABI prefix (pc 0 to 10: parameter words, `%tid.x`, `%p3 = tid < 32`, the shared
base) has no event. Then:

* pc 11: `@%p3 tcgen05.alloc.cta_group::1 [global_smem], 512` (warp 0; lane 0 also stores the
  allocated address, the instruction's second sub-step);
* pc 12: `bar.sync 0`; pc 13: `ld.shared.b32 %r2, [global_smem]` (the Tensor Memory base word);
  pc 14: `bar.sync 0`; pc 15: `@%p3 tcgen05.relinquish_alloc_permit`;
* pc 17: `shfl.sync.idx.b32 %r4, %r3, 0, 31, -1` (the warp index from lane 0), then
  `setp.lt.u32 %p4, %r4, 4` and `@!%p4 bra` (pc 18, 19).

On `%p4` the thread runs the parameter loads of pc 20 to 26 and reaches pc 27 (`enter .dp`, the
default partition's first event, `setmaxnreg.inc`); otherwise it runs pc 2331, 2332 and reaches
pc 2337 (`enter .worker`, the worker dispatch loop's head).

The machine follows every value an event returns (plan rule M1): the base word is recorded as
the number `tm` when it is a 32-bit word (`word32`), the received word as `x` when it
is a 32-bit word; the base word register holds the value the load returned whatever its kind
(`w`; a word of another kind, four bytes stored whole as a float or a pointer, records `tm = 0`),
and the roles are entered with it. Bytes that rebuild to no value are a death (`none`: Core's load
faults). So no state of the startup stops on what the load returned, and the threads are
followed through it with no source of the base word (`Common/Staged/Early.lean`). A
received word of another kind stops the machine (`some none`). The branch is the code's
comparison on `x`. The states `enter r` are the fragment's exits; the glue
(`Proof/Common/Roles.lean`) replaces each by its role's first state.

The register table is the common start's (`Startup.table`, which mirrors the code), with
`%r2` the recorded word, `%r4` the received word and `%r5 = num_splits << 7` (pc 2331); the
registers the parameter loads of pc 20 to 26 write are the prologue's first values
(`exitValue`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

/-- The roles the branch on the warp index reaches. -/
inductive Entry where
  /-- The default partition (warps 0 to 3): `setmaxnreg.inc` at pc 27. -/
  | dp
  /-- The workers (warps 4 to 7): the dispatch loop's head at pc 2337. -/
  | worker
  deriving DecidableEq

def Entry.pc : Entry → Nat
  | .dp => 27
  | .worker => 2337

inductive Site where
  | alloc
  | allocWr
  | bar0
  | ld0
  | bar1
  | relinq
  | shfl
  | enter (r : Entry)
  deriving DecidableEq

def Site.pc : Site → Nat
  | .alloc => 11
  | .allocWr => 11
  | .bar0 => 12
  | .ld0 => 13
  | .bar1 => 14
  | .relinq => 15
  | .shfl => 17
  | .enter r => r.pc

/-- The allocation's address store is its instruction's second sub-step. -/
def Site.sub : Site → Nat
  | .allocWr => 1
  | _ => 0

/-- A state: the site, the base word's number (`tm`, 0 for a value that is no 32-bit word), the
word the shuffle returned (`x`) and the base word register's value as the load returned it
(`w`). -/
structure D where
  site : Site
  tm : Nat := 0
  x : BitVec 64 := 0
  w : Value := b32 0

/-- The role the branch on the received word reaches (`setp.lt.u32 %p4, %r4, 4`). -/
def entryOf (x : BitVec 64) : Entry := if Arith32.scmpi .lt .u x 4 then .dp else .worker

/-- The successor after event `e`. -/
def succ (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .alloc => some (some (if laneOf L g = 0 then { d with site := .allocWr }
      else { d with site := .bar0 }))
  | .allocWr => some (some { d with site := .bar0 })
  | .bar0 => some (some { d with site := .ld0 })
  | .ld0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some n => some (some { d with site := .bar1, tm := n, w := v })
        | none => some (some { d with site := .bar1, tm := 0, w := v })
      | .error _ => none
    | _ => none
  | .bar1 => some (some (if g % L.block < 32 then { d with site := .relinq }
      else { d with site := .shfl }))
  | .relinq => some (some { d with site := .shfl })
  | .shfl =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match v with
      | .bits 32 x => some (some { d with site := .enter (entryOf x), x := x })
      | _ => some none
    | _ => none
  | .enter _ => none

/-- The registers the startup computes, as functions of the recorded words. -/
def values (Q : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (465, .bits 32 d.x) ::
    (466, .bits 32 (Arith32.shl (BitVec.ofNat 64 (Q.splits % 2 ^ 32)) 7)) ::
    Startup.table L g Q d.w

/-- The value of register `r` at state `d`: the table's, else the prologue's first value. -/
def valueOf (Q : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values Q L g d).lookup r).getD
    (exitValue L Q r)

/-- The registers a site's facts name: those live at its pc. -/
def Site.live (s : Site) : List Nat := Flow.live s.pc

abbrev facts (Q : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom d.site.live (valueOf Q L g d)

/-- The states of the allocation and the relinquish are states of warp 0. -/
def Inv (L : Launch) (g : Nat) (d : D) : Prop :=
  (d.site = .alloc ∨ d.site = .allocWr ∨ d.site = .relinq) → g % L.block < 32

/-- The first state: the allocation on warp 0, the first barrier on the other warps. -/
def init (L : Launch) (g : Nat) : D :=
  if g % L.block < 32 then ⟨.alloc, 0, 0, b32 0⟩ else ⟨.bar0, 0, 0, b32 0⟩

/-- The startup as a code machine. -/
@[reducible] def code (Q : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := init L g
  pc := (·.site.pc)
  facts := facts Q L g
  sub := (·.site.sub)
  inv := Inv L g
  next := succ L g

end
end PTX.Kernels.InklingRelDecode.Proof.Startup
