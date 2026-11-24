-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerStart
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec

@[expose] public section

/-! # The default partition's common start (pc 0 to 27) as abstract states

Every thread of the CTA runs the same code from its first instruction to the `@!%p4 bra` of
pc 19: the loads of the parameter words the roles use (pc 0 to 7), `%tid.x` and the test
`%p3 = (tid < 32)` (pc 8, 9), the shared base (pc 10), and then

* pc 11: `@%p3 tcgen05.alloc.cta_group::1 [global_smem], 512`;
* pc 12: `bar.sync 0`;
* pc 13: `ld.shared.b32 %r2, [global_smem]` (the Tensor Memory base word);
* pc 14: `bar.sync 0`;
* pc 15: `@%p3 tcgen05.relinquish_alloc_permit.cta_group::1`;
* pc 16: `shr.u32 %r3, %r1, 5` (the warp index of the thread);
* pc 17: `shfl.sync.idx.b32 %r4, %r3, 0, 31, -1` (the warp index from lane 0);
* pc 18, 19: `setp.lt.u32 %p4, %r4, 4` and `@!%p4 bra` (to the worker path, pc 2331).

A thread of warps 0 to 3 (`tid < 128`) falls through the branch (`%p4` holds) and runs the seven
`ld.param` of pc 20 to 26 and, at pc 27, `setmaxnreg.inc 256`, the first site of the prologue
machine `ProA.code`. The machine of this file follows such a thread from its first event to that
`setmaxnreg.inc`, and its last site `toProA` is `ProA`'s first (`ProA.D.start`): the step of the
shuffle runs the local code of pc 18 to 26 through `ProA.entry`.

Which threads execute the guarded instructions: `%p3` is `tid < 32`, so the `tcgen05.alloc`
(pc 11) and the `tcgen05.relinquish_alloc_permit` (pc 15) are executed by the threads of warp 0
and skipped (their events are none) by warps 1 to 3. The first event of a thread of warp 0 is
the allocation (`alloc`); on lane 0 it is followed by the store of the allocated address to
`global_smem` (`allocWr`, the second sub-step of the same instruction), on the other lanes the
thread goes on to the barrier. The first event of a thread of warps 1 to 3 is the barrier
(`bar0`). `Inv.lane0` records that `alloc`, `allocWr` and `relinq` are states of warp 0 only.

A state is a site and the Tensor Memory base word (`w`, `b32 0` before the load of pc 13 and the
word read after, whatever value it is). The machine follows every loaded word; the prologue stops
at its proxy fence `fnc0` on a word that is not good (`ProA.wGood`). Where the machine does not
follow the code, the abstract successor is `some none`, and the protocol layer owns the fact that
it does not happen: the shuffle returns something other than the warp index. A load whose bytes
rebuild to no value faults the thread, so its successor is `none` and the state is dead. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The warp index of a thread of the CTA. -/
abbrev warpOf (L : Launch) (g : Nat) : Nat := g % L.block / 32

/-! ### The sites -/

/-- The event instructions of the common start. -/
inductive Site where
  /-- `tcgen05.alloc` (first sub-step: the allocation request), warp 0. -/
  | alloc
  /-- The second sub-step of `tcgen05.alloc` (lane 0 stores the allocated address), warp 0. -/
  | allocWr
  /-- The first `bar.sync 0` (pc 12). -/
  | bar0
  /-- The load of the Tensor Memory base word (pc 13). -/
  | ld0
  /-- The second `bar.sync 0` (pc 14). -/
  | bar1
  /-- `tcgen05.relinquish_alloc_permit` (pc 15), warp 0. -/
  | relinq
  /-- The broadcast of the warp index (pc 17). -/
  | shfl
  /-- `setmaxnreg.inc 256` (pc 27): the first site of the prologue machine. -/
  | toProA
  deriving DecidableEq

def Site.pc : Site → Nat
  | .alloc => Flow.tmemAlloc_0
  | .allocWr => Flow.tmemAlloc_0
  | .bar0 => Flow.bar_0
  | .ld0 => Flow.load_0
  | .bar1 => Flow.bar_1
  | .relinq => Flow.tmemRelinquish_0
  | .shfl => Flow.shfl_0
  | .toProA => Flow.setMaxReg_0

/-- The sub-step of the site: the allocation's address store is its instruction's second one. -/
def Site.sub : Site → Nat
  | .allocWr => 1
  | _ => 0

/-! ### The states -/

/-- A state: the next event, and the Tensor Memory base word the load returned (`b32 0`
before). -/
structure D where
  site : Site
  w : Value

/-- The inherited registers the prologue `ProA` reads, as the launch gives them: the parameter
words (`Pre.param*`), `%p3` and `%rd1` (the registers the common code carries), the Tensor Memory
base word `tm`. -/
def inh (L : Launch) (g : Nat) (Q : Params) (tm : Nat) : ProA.Inh where
  rest := fun r =>
    if r = 3 then .pred (decide (g % L.block < 32))
    else if r = 1949 then .ptr 64 true (.param (param "1")) 0 else b32 0
  tm := tm
  w67 := Q.strideBt % 2 ^ 32
  w68 := Q.pageRows % 2 ^ 32
  w69 := Q.headRows % 2 ^ 32
  w70 := Q.headCols % 2 ^ 32
  w71 := Q.splits % 2 ^ 32
  btB := Q.btBase
  x15 := (L.params (param "15")).getD 0
  x16 := BitVec.ofNat 64 Q.strideQ
  x17 := BitVec.ofNat 64 Q.strideRel
  x0 := BitVec.ofNat 64 Q.qBase
  x6 := BitVec.ofNat 64 Q.relBase
  x8 := BitVec.ofNat 64 Q.seqBase
  x9 := BitVec.ofNat 64 Q.cuBase
  x25 := BitVec.ofNat 64 Q.nTok
  x10 := BitVec.ofNat 64 Q.oBase
  x11 := BitVec.ofNat 64 Q.lseBase

/-- The registers the common code defines or inherits at pc 11 to 17 and their values: `%p3`
(`tid < 32`), `%r1` (`%tid.x`), `%r2` (the Tensor Memory base word), `%r3` and `%r4` (the warp
index), `%r67 … %r71` (the parameter words), `%r73` (the shared base) and `%rd1`, `%rd72`. -/
def table (L : Launch) (g : Nat) (Q : Params) (w : Value) : List (Nat × Value) :=
  [(3, .pred (decide (g % L.block < 32))), (462, b32 (g % L.block)), (463, w),
   (464, b32 (warpOf L g)), (465, b32 (warpOf L g)), (528, b32 (Q.strideBt % 2 ^ 32)),
   (529, b32 (Q.pageRows % 2 ^ 32)), (530, b32 (Q.headRows % 2 ^ 32)),
   (531, b32 (Q.headCols % 2 ^ 32)), (532, b32 (Q.splits % 2 ^ 32)),
   (534, .bits 32 (Loader.baseW L)), (1949, .ptr 64 true (.param (param "1")) 0),
   (2020, b64 Q.btBase)]

/-- The value of register `r`: the table's, else the prologue's (`ProA.valueOf` of its first
state), which values the registers the seven `ld.param` of pc 20 to 26 write: they are live at
pc 27, not before. -/
def valueOf (L : Launch) (g : Nat) (Q : Params) (w : Value) (r : Nat) : Value :=
  ((table L g Q w).lookup r).getD (ProA.valueOf L g (ProA.Dat.start (inh L g Q (ProA.shW w)) w) r)

/-- The registers live at `pc` with their values. -/
def factsAt (L : Launch) (g : Nat) (Q : Params) (w : Value) (pc : Nat) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g Q w)

abbrev facts (L : Launch) (g : Nat) (Q : Params) (d : D) : List (Nat × Value) :=
  factsAt L g Q d.w d.site.pc

/-! ### The invariant -/

/-- The invariant of the states: the thread is in the default partition, the inherited
registers satisfy `ProA.ArgsOk`, and `alloc`, `allocWr` and `relinq` are states of warp 0 (the
threads for which `%p3` holds). -/
structure Inv (L : Launch) (g : Nat) (Q : Params) (d : D) : Prop where
  args : ProA.ArgsOk L g (inh L g Q (ProA.shW d.w))
  lane0 : (d.site = .alloc ∨ d.site = .allocWr ∨ d.site = .relinq) → g % L.block < 32

/-! ### The abstract successor -/

/-- The abstract successor after event `e`. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .alloc => some (some (if laneOf L g = 0 then ⟨.allocWr, d.w⟩ else ⟨.bar0, d.w⟩))
  | .allocWr => some (some ⟨.bar0, d.w⟩)
  | .bar0 => some (some ⟨.ld0, d.w⟩)
  | .ld0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => some (some ⟨.bar1, v⟩)
      | .error _ => none
    | _ => none
  | .bar1 => some (some (if g % L.block < 32 then ⟨.relinq, d.w⟩ else ⟨.shfl, d.w⟩))
  | .relinq => some (some ⟨.shfl, d.w⟩)
  | .shfl =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match recv with
      | .bits wd v =>
        some (if wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g) then some ⟨.toProA, d.w⟩ else none)
      | _ => some none
    | _ => none
  | .toProA => some none

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
