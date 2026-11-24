-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerBase

@[expose] public section

/-! # The workers' prologue and dispatch as abstract states

A thread of warps 4 to 7 of a CTA (the CTA has 256 threads) runs the code every thread runs up to
`@!%p4 bra` (pc 0 to 19), then the worker path: `setmaxnreg.inc 256`, the named barrier 1, the
read of its role byte from `global_smem + 213332 + warp`, and the `brx.idx` that sends it to its
role. A role ends by returning to the dispatch loop's first instruction (pc 2337), so the loop
(pc 2337 to 2343) is the worker's own, and the roles' entries (pc 2333, 2344, 2422, 2853) are
where this machine ends.

The machine follows the thread from its first event. The first event is the `bar.sync 0` at
pc 12: the `tcgen05.alloc` before it (pc 11) is guarded by `%p3 = (tid < 32)`, false for these
threads, so it is skipped, as is the `tcgen05.relinquish_alloc_permit` at pc 15 (the events of
the instructions before pc 12 are none). The sites are

* `bar0`, `ld0`, `bar1`: `bar.sync 0`, `ld.shared.b32 %r2, [global_smem]` (the Tensor Memory base
  word), `bar.sync 0`;
* `shfl`: `shfl.sync.idx.b32 %r4, %r3, 0, 31, -1` (the warp index from lane 0). After it the
  local code (`setp.lt.u32 %p4, %r4, 4`, `@!%p4 bra`, `shl.b32 %r5, %r71, 7`, `bra.uni`) goes to
  the loop;
* `loop`, `bar2`, `ldRole`: `setmaxnreg.inc 256` (pc 2337, the loop's head), `barrier.sync 1`
  (pc 2338) and `ld.shared.b8 %r74, [%r75 + 213332]` (pc 2340, `%r75 = %r73 + %r4`). After the
  load the local code is `setp.gt.u32 %p5, %r74, 3`, `@%p5 bra` and `brx.idx %r74` (pc 2341 to
  2343);
* `toIdle`, `toLoader`, `toMma`, `toExit`: the entries of the idle role (pc 2333, index 2), the
  loader (pc 2344, index 0), the MMA warp (pc 2422, index 1) and the exit (pc 2853, index 3).
  The machine ends there (`next = some none`); `WorkerIdle.lean` follows the idle role and
  returns to `loop`, `WorkerHandoff.lean` gives the loader's and the MMA warp's first facts.

A state is the next event with the inherited registers `P` (`Loader.Pro`: the loader's view of
the registers that the prologue and the dispatch leave). The registers of a state are valued by
`own` (`%p3`, `%r3`, `%r4`, `%r73`: what the worker's code computes), `roleAddr` (`%r75`, which
only the load of the role byte reads) and else `Pro.val L g P` (the strides and counts, the
block-table base, the thread index, `%rd1`, and `%r2`, the Tensor Memory base word, which the
load at pc 13 writes into `P` by `setTm`). `Rest` says when `Pro.val L g P` agrees with `own`:
the registers a role hands back are the worker's when it holds.

The machine follows every value of the role byte. A byte whose low 32 bits are below 4 goes to
the role's entry; any other byte makes `@%p5 bra` (pc 2342) jump to two `barrier.sync 1`
(pc 2557, 2558: `bad0`, `bad1`) and back to the loop's head, so the dispatch never leaves the code
(`dispatch`). The machine still leaves the code at

* the shuffle, when it returns something other than the warp index (a shuffle from lane 0 of a
  warp-uniform operand returns that operand: the execution layer's);
* the role entries `toIdle`, `toLoader`, `toMma`, `toExit`, where the roles' machines take over.

A load whose bytes rebuild to no value faults the thread, so its successor is `none` and the
state is dead (`Machine.Dead`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The warp index of a thread of the CTA. -/
def warpOf (L : Launch) (g : Nat) : Nat := g % L.block / 32

/-! ### The event instructions of the worker -/

/-- The event instructions of the worker's path, and the entries of the roles it dispatches to. -/
inductive Site where
  | bar0
  | ld0
  | bar1
  | shfl
  /-- `setmaxnreg.inc 256` at the dispatch loop's head. -/
  | loop
  | bar2
  /-- The load of the role byte. -/
  | ldRole
  | toIdle
  | toLoader
  | toMma
  | toExit
  /-- The first of the two barriers of the branch taken for a role byte above 3
  (`@%p5 bra`, pc 2342), which the table of the `brx.idx` does not index. -/
  | bad0
  /-- The second of those barriers; the branch after it goes back to the loop's head. -/
  | bad1
  deriving DecidableEq

def Site.pc : Site → Nat
  | .bar0 => Flow.bar_0
  | .ld0 => Flow.load_0
  | .bar1 => Flow.bar_1
  | .shfl => Flow.shfl_0
  | .loop => Flow.setMaxReg_4
  | .bar2 => Flow.bar_27
  | .ldRole => Flow.load_203
  | .toIdle => Flow.setMaxReg_2
  | .toLoader => Flow.setMaxReg_5
  | .toMma => Flow.setMaxReg_7
  | .toExit => Flow.bar_37
  | .bad0 => Flow.bar_32
  | .bad1 => Flow.bar_33

/-- The site of role-table index `i`: the table of the `brx.idx` is the loader, the MMA warp, the
idle role and the exit. Another index leaves the table. -/
def roleSite : Nat → Option Site
  | 0 => some .toLoader
  | 1 => some .toMma
  | 2 => some .toIdle
  | 3 => some .toExit
  | _ => none

/-! ### The states -/

/-- A worker state: the next event and the inherited registers. -/
structure D where
  site : Site
  P : Pro

/-- The first state of the worker, from the inherited registers `P`. -/
def D.start (P : Pro) : D := ⟨.bar0, P⟩

/-- The inherited registers after the load of the Tensor Memory base word `v` into `%r2`. -/
def setTm (P : Pro) (v : Value) : Pro := { P with rest := Function.update P.rest 463 v }

/-- The value of `%r75 = %r73 + %r4` (`add.s32`, the shared base plus the warp index), the
address the role byte is read at. -/
def roleAddr (L : Launch) (g : Nat) : Value :=
  .bits 32 (Loader.addW (Loader.baseW L) (BitVec.ofNat 64 (warpOf L g)))

/-- The registers the worker's own code writes or whose value the launch fixes, with their
values (a thread of warp `w`): `%p3 = (tid < 32)`, the warp index in `%r3` (`shr.u32 %r1, 5`) and
`%r4` (the shuffle's result), and the shared base in `%r73` (`mov.b32`, the address of
`global_smem`). -/
def own (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(3, .pred (decide (g % L.block < 32))), (464, b32 (warpOf L g)), (465, b32 (warpOf L g)),
   (534, .bits 32 (Loader.baseW L))]

/-- The value of register `r` at state `d`: `%r75` the address of the role byte, the registers
of `own`, else the inherited ones (`Pro.val`). -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  if r = 536 then roleAddr L g else ((own L g).lookup r).getD (Pro.val L g d.P r)

/-- The registers live at `pc`, with their values in state `d`. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- The register that marks the dispatch loop's later rounds. It is not a register of the
program, so it changes no register fact (`facts_bumpPro`); it only tells the abstract state of the
loop's head in the second round from the first, which the progress layer's virtual time needs (the
head is otherwise the same state in both rounds, and a time that is a function of the state alone
cannot rise around the loop). -/
def roundReg : Nat := 1000000

/-- The inherited registers after a role has returned to the dispatch loop's head: the round
marker is set. -/
def bumpPro (P : Pro) : Pro := { P with rest := Function.update P.rest roundReg (b32 1) }

/-- The loop's head is in a later round: its inherited registers carry the round marker. -/
def late (P : Pro) : Prop := P.rest roundReg = b32 1

theorem late_bumpPro (P : Pro) : late (bumpPro P) := by
  simp [late, bumpPro]

/-- The registers live at the loop's head do not include the round marker. -/
theorem live_loop_ne : ∀ r ∈ Flow.live Flow.setMaxReg_4, r ≠ roundReg := by
  decide +kernel

theorem valueOf_bumpPro {L : Launch} {g : Nat} (P : Pro) (s : Site) {r : Nat}
    (h : r ≠ roundReg) : valueOf L g ⟨s, bumpPro P⟩ r = valueOf L g ⟨s, P⟩ r := by
  have ht : Pro.table L g (bumpPro P) = Pro.table L g P := rfl
  have hv : Pro.val L g (bumpPro P) r = Pro.val L g P r := by
    simp only [Pro.val, ht]
    simp [bumpPro, Function.update_of_ne h]
  simp only [valueOf, hv]

/-- **The round marker changes no register fact at the loop's head.** -/
theorem facts_bumpPro_loop {L : Launch} {g : Nat} (P : Pro) :
    facts L g ⟨.loop, bumpPro P⟩ = facts L g ⟨.loop, P⟩ := by
  simp only [facts, factsAt, Site.pc, Flow.factsFrom]
  refine List.map_congr_left fun r hr => ?_
  rw [valueOf_bumpPro P _ (live_loop_ne r hr)]

/-- What the inherited registers `P` hold for the loader's operands, from the launch: the
block-table base is aligned to the 4 bytes of a block-table word (`Pre.btAlign`), `%rd1` is
the address of the parameter `param_1`, the tensor map (`startPro`), and the column stride of a
KV head (`%r70`, `head_cols`) is a multiple of 8 (`Pre.headColsAlign`), so the copies' box
columns are 16-byte aligned. The worker's code writes none of them, so every state of the worker
and of its roles keeps them. -/
structure Pins (P : Pro) : Prop where
  bt : P.bt % 4 = 0
  rd1 : P.rest 1949 = .ptr 64 true (.param (param "1")) 0
  w70 : P.w70 % 8 = 0

theorem Pins.setTm {P : Pro} (h : Pins P) (v : Value) : Pins (setTm P v) :=
  ⟨h.bt, by
    show Function.update P.rest 463 v 1949 = _
    rw [Function.update_of_ne (show (1949 : Nat) ≠ 463 by decide), h.rd1], h.w70⟩

theorem Pins.bumpPro {P : Pro} (h : Pins P) : Pins (bumpPro P) :=
  ⟨h.bt, by
    show Function.update P.rest roundReg (b32 1) 1949 = _
    rw [Function.update_of_ne (show (1949 : Nat) ≠ roundReg by decide), h.rd1], h.w70⟩

/-- What the inherited registers `P` hold for the registers of `own`: a role that returns to the
dispatch loop with its registers `Pro.val L g P` returns the worker's registers when `Rest`
holds (`WorkerHandoff.lean`); and the launch's facts `Pins`. -/
structure Rest (L : Launch) (g : Nat) (P : Pro) : Prop where
  p3 : P.rest 3 = .pred (decide (g % L.block < 32))
  r3 : P.rest 464 = b32 (warpOf L g)
  r4 : P.rest 465 = b32 (warpOf L g)
  base : P.rest 534 = .bits 32 (Loader.baseW L)
  pins : Pins P

/-- The invariant of the worker's states: the thread is in warp 4 or above (the warps that
branch to the worker path at pc 19), its index in the CTA is below 256 (`.reqntid 256`), and its
inherited registers satisfy `Pins`. -/
structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  warp : 4 ≤ warpOf L g
  tid : g % L.block < 256
  pins : Pins d.P

/-! ### The abstract successor -/

/-- The successor after the load of the role byte, from its bytes: the site of the role the
extended byte indexes (the code compares and indexes its low 32 bits), or, for an index above 3,
the barriers of the branch the code takes (`bad0`, which returns to the dispatch loop), or `none`
(a fault) if the bytes do not rebuild or cannot be extended. The machine never leaves the code at
this load. -/
def dispatch (P : Pro) (bs : List (Option Byte)) : Option (Option D) :=
  match rebuild 3 bs with
  | .error _ => none
  | .ok v =>
    match extendLoaded (MemExt.zero 32) 8 v with
    | .error _ => none
    | .ok (.bits 32 x) =>
      some (some ⟨(roleSite (truncBits 32 x).toNat).getD .bad0, P⟩)
    | .ok _ => none

/-- The abstract successor after event `e`. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .bar0 => some (some ⟨.ld0, d.P⟩)
  | .ld0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => some (some ⟨.bar1, setTm d.P v⟩)
      | .error _ => none
    | _ => none
  | .bar1 => some (some ⟨.shfl, d.P⟩)
  | .shfl =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match recv with
      | .bits wd v =>
        some (if wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g) then some ⟨.loop, d.P⟩ else none)
      | _ => some none
    | _ => none
  | .loop => some (some ⟨.bar2, d.P⟩)
  | .bar2 => some (some ⟨.ldRole, d.P⟩)
  | .ldRole =>
    match e.kind with
    | .rd _ bs => dispatch d.P bs
    | _ => none
  | .bad0 => some (some ⟨.bad1, d.P⟩)
  | .bad1 => some (some ⟨.loop, d.P⟩)
  | .toIdle | .toLoader | .toMma | .toExit => some none

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
