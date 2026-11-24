-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.BulkGroup
public import Core.Async.CopyForm
public import Core.Isa.Int
public import Core.Isa.Float
public import Core.Isa.Move
public import Core.Isa.Cvt
public import Core.Isa.Misc
public import Core.Isa.Mem
public import Core.Isa.Warp
public import Core.Isa.Matrix
public import Core.Isa.Tc
public import Core.Isa.Fence

@[expose] public section

/-!
# Instructions

The typed program the model executes. `Core/Source/Decode.lean` produces it from the
parsed PTX source, inside Lean.
-/

namespace PTX

/-! ## PROG-INSTR-FORMS — the supported instruction forms
Statement: A decoded instruction is a family constructor (integer, floating, move, conversion,
  memory access, address, warp collective, warp-level matrix instruction, `createpolicy`,
  `nanosleep` and `pmevent`), one of the kept constructors
  of the barrier, mbarrier, fence, copy, cluster launch control, `setmaxnreg` and
  `tcgen05` forms, a control-flow constructor, or `Op.unmodeled` for a recognized instruction
  without a representation this round. A kernel is a list of instructions in source order; each
  has an optional guard, branch targets are instruction indices, and registers are numbered by
  declaration order.

Defs: ClcDim, ClcQuery, ClusterOp, ClusterOp.aligned, TensorMode,
  TensorMode.coordinates, TcShape, TcShape.lanes, TcShape.regs,
  TcShape.countOk, TcShape.singleAccess, Op, Op.aligned, Instr, PtrSpace, PtrDecl, Kernel

Source:
- §9.7 (instruction descriptions)
- §9.3 (predicated execution)

Direction: scope

Effect: An instruction the grammar does not recognize, or whose family layer rejects it, fails
  decoding, so no theorem is about a kernel that uses it. `Op.unmodeled` keeps the recognized
  instruction (`Isa.Raw`); no rule gives it semantics (THREAD-LOCAL, THREAD-RUN). Branch targets are
  instruction indices; a guard is a predicate register, possibly negated. A register is a number,
  its index in the kernel's declared-register order (PROG-DECODE); `Kernel.regNames` keeps the
  source names for printing, and no rule reads them.
-/

/-- Coordinate selected by a scalar CLC query. -/
inductive ClcDim where
  | x | y | z
  deriving DecidableEq, Repr

inductive ClcQuery where
  | isCanceled
  | first (dim : ClcDim)
  deriving DecidableEq, Repr

/-- Cluster barrier qualifiers are retained for synchronization and alignment checks. -/
inductive ClusterOp where
  | arrive (release aligned : Bool)
  | wait (aligned : Bool)
  deriving DecidableEq, Repr

def ClusterOp.aligned : ClusterOp → Bool
  | .arrive _ aligned | .wait aligned => aligned

/-- The `.load_mode` qualifier of a 2D-or-more tensor copy: `.tile` (the default), or four
arbitrary rows of a 2D tensor — `.tile::gather4` for loads, `.tile::scatter4` for stores. -/
inductive TensorMode where
  | tile | fourRows
  deriving DecidableEq, Repr

/-- The coordinate count of a tensor copy over a map of `outer + 1` dimensions. -/
@[simp] def TensorMode.coordinates : TensorMode → Nat → Nat
  | .tile, outer => outer + 1
  | .fourRows, _ => 5

/-- The access shape of `tcgen05.ld` and `tcgen05.st` (§9.7.18.8.3, §9.7.18.8.4: ".shape1 = {
.16x64b, .16x128b, .16x256b, .32x32b }", ".shape2 = { .16x32bx2 }"). `.16x32bx2` carries its
`immHalfSplitoff` operand. `packed16 s` is shape `s` with `.pack::16b` (`tcgen05.ld`) or
`.unpack::16b` (`tcgen05.st`): each register of `s` is two 16-bit halves in two adjacent columns
(THREAD-TC-PACK16). -/
inductive TcShape where
  | s32x32b
  | s16x64b
  | s16x128b
  | s16x256b
  | s16x32bx2 (halfSplit : Nat)
  | packed16 (s : TcShape)
  deriving DecidableEq, Repr

/-- The Tensor Memory lanes one access of the shape covers: 32 for `.32x32b` (§9.7.18.2.3.1.1: "A
warp executing tcgen05{.ld,.st}.32x32b will access 32 lanes of the Tensor Memory."), 16 for the
others (§9.7.18.2.3.1.2 to .5, for example "A warp executing tcgen05{.ld,.st}.16x64b will access
16 lanes of the Tensor Memory."). -/
def TcShape.lanes : TcShape → Nat
  | .s32x32b => 32
  | .packed16 s => s.lanes
  | _ => 16

/-- The registers of one repetition (`.x1`) of the shape: the `.x1` row of Tables 59 and 61. -/
def TcShape.regs : TcShape → Nat
  | .s16x128b => 2
  | .s16x256b => 4
  | .packed16 s => s.regs
  | _ => 1

/-- One of the shapes with a single access and no packing: `.32x32b`, `.16x64b`, `.16x128b`,
`.16x256b`. -/
def TcShape.singleAccess : TcShape → Bool
  | .s32x32b | .s16x64b | .s16x128b | .s16x256b => true
  | .s16x32bx2 _ | .packed16 _ => false

/-- Tables 59 and 61: a vector of `n` registers is `.num` repetitions of the shape, `.num` a
power of two from 1 to 128, and holds at most 128 registers (the entries marked NA). -/
def TcShape.countOk (s : TcShape) (n : Nat) : Bool :=
  decide (n ≤ 128) && [1, 2, 4, 8, 16, 32, 64, 128].any fun num => n == s.regs * num

/-- The supported instruction forms with their decoded qualifiers and operands: local arithmetic,
moves and branches, memory accesses, barriers, mbarrier and bulk-copy operations, tensor copies,
cluster launch control and `tcgen05`. -/
inductive Op where
  /-- Prefetch a tensormap through a generic or explicit parameter-space address. -/
  | prefetchTensorMap (generic : Bool) (width : Nat) (src : Opnd)
  /-- `cp.async.bulk.prefetch.tensor.<n>d.L2.global{.tile, .tile::gather4}{.L2::cache_hint}
  [map, coords]{, cachePolicy}`: an L2 prefetch of tensor data. -/
  | prefetchTensor (map : Opnd) (coords : List Opnd) (mode : TensorMode) (cachePolicy : Option Opnd)
  | setMaxReg (increase : Bool) (count : Nat)
  /-- An integer, bit, logic, comparison or selection instruction (PROG-ISA-INT). -/
  | int (i : IntInstr)
  /-- A register move, pack or unpack (PROG-ISA-MOVE). -/
  | move (m : MoveInstr)
  /-- A conversion (PROG-ISA-CVT). -/
  | cvt (c : CvtInstr)
  /-- A load, store, atomic or reduction (PROG-ISA-MEM). -/
  | mem (a : MemAccess)
  /-- An address conversion or query (PROG-ISA-MEM). -/
  | addr (c : AddrInstr)
  /-- A warp collective (PROG-ISA-WARP). -/
  | warp (w : WarpInstr)
  /-- A warp-level matrix instruction (PROG-ISA-MATRIX). -/
  | matrix (m : MatrixInstr)
  /-- `createpolicy`, `nanosleep` or `pmevent` (PROG-ISA-MISC). -/
  | misc (m : MiscInstr)
  /-- A floating-point, half-precision or mixed-precision instruction (PROG-ISA-FLOAT). -/
  | float (f : FloatInstr)
  /-- `bar.sync a` / `barrier.sync{.aligned} a` without a thread count: the whole CTA.
  `aligned` is set for `bar.sync` and `barrier.sync.aligned` (§9.7.15.1: `bar.sync` is
  `barrier.sync.aligned`). -/
  | barSync (barrier : Opnd) (aligned : Bool)
  /-- `bar.sync a, b` / `barrier.sync{.aligned} a, b` with an explicit thread count `b`. -/
  | barSyncN (barrier count : Opnd) (aligned : Bool)
  /-- `bar.arrive a, b` / `barrier.arrive{.aligned} a, b`: arrival at barrier `a` with thread count
  `b`, without waiting for the other participating warps (§9.7.15.1: `bar.arrive` is
  `barrier.arrive.aligned`). -/
  | barArrive (barrier count : Opnd) (aligned : Bool)
  | cluster (op : ClusterOp)
  /-- `bra{.uni} target`; `uni` records the `.uni` qualifier (§9.7.14.3: the branch is
  non-divergent). -/
  | bra (target : Nat) (uni : Bool)
  /-- `brx.idx{.uni} index, tlist`: a branch to entry `index` of the `.branchtargets` table. -/
  | brx (index : Opnd) (targets : List Nat) (uni : Bool)
  /-- `ret`. -/
  | ret
  /-- `exit`. -/
  | exit
  /-- `trap`. -/
  | trap
  /-- `cp.async.bulk.tensor.<n>d` global-to-shared load: `.tile` with `n` coordinates (inner
  first), or `.2d.tile::gather4` with `{x, y0, y1, y2, y3}`; `multicast` is `.multicast::cluster`'s
  ctaMask operand and its width in bits (16 or 32); `cachePolicy` is the 64-bit operand of
  `.L2::cache_hint`. -/
  | cpTensor (clusterAddress groupTwo : Bool) (dst : Nat) (dstOff : Int)
      (map : Opnd) (coords : List Opnd) (mbar : Nat) (mbarOff : Int)
      (multicast : Option (Nat × Opnd)) (mode : TensorMode) (cachePolicy : Option Opnd := none)
  /-- `n`-D shared-to-global store: `.tile` with `n` coordinates, or `.2d.tile::scatter4` with
  `{x, y0, y1, y2, y3}`; cache policy is an optional 64-bit hint. With `reduce`,
  `cp.reduce.async.bulk.tensor.<n>d.global.shared::cta.<redOp>{.tile}.bulk_group`: each element
  is reduced into the tensor instead of stored. -/
  | cpTensorStore (map : Opnd) (coords : List Opnd) (src : Nat) (srcOff : Int)
      (cachePolicy : Option Opnd) (mode : TensorMode) (reduce : Option AtomOp)
  | bulkCommit
  | bulkWait (mode : BulkGroup.WaitMode) (remaining : Nat)
  | clcTryCancel (multicast : Bool) (dst : Nat) (dstOff : Int) (mbar : Nat) (mbarOff : Int)
  | clcQuery (query : ClcQuery) (dst : Nat) (response : Opnd)
  /-- `mbarrier.init.shared::cta.b64 [base + offset], count`. -/
  | mbarInit (base : Nat) (offset : Int) (count : Opnd)
  /-- `mbarrier.inval.shared::cta.b64 [base + offset]`. -/
  | mbarInval (base : Nat) (offset : Int)
  /-- A thread fence (also `membar`) or a proxy fence (PROG-ISA-FENCE). -/
  | fence (f : FenceInstr)
  /-- Restricted release of this thread's preceding local mbarrier initialization. -/
  | fenceMbarInit
  /-- `mbarrier.arrive{.sem}{.scope}{.expect_tx}.shared{::cta,::cluster}.b64 state, [base + offset]`
  with optional count and transaction operands: `count` arrivals after expecting `tx` bytes.
  `cluster` selects a `shared::cluster` address. `state` is the destination register, `none`
  for the sink `_`. Defaults are the PTX defaults. -/
  | mbarArrive (base : Nat) (offset : Int) (tx : Opnd) (count : Opnd := .imm 1)
      (cluster : Bool := false) (release : Bool := true) (scope : MbarScope := .cta)
      (state : Option Nat := none)
  /-- `cp.async.bulk{.sem.scope}.dst.src.completion{...} [dstMem], [srcMem], size, ...` in any
  direction, and `cp.reduce.async.bulk` (`BulkCopy`). -/
  | cpBulk (c : BulkCopy)
  /-- `st.async` and `red.async` (`AsyncStore`). -/
  | asyncStore (s : AsyncStore)
  /-- `cp.async.{ca,cg}.shared{::cta}.global [dst], [src], cp-size{, src-size | ignore-src}{,
  cache_policy}` with `cp-size` 4, 8 or 16; the cache operator and prefetch-size hints are
  dropped. -/
  | cpAsync (dst : Nat) (dstOff : Int) (src : Nat) (srcOff : Int) (size : Nat)
      (source : CpAsyncSource) (cachePolicy : Option Opnd)
  /-- `cp.async.commit_group`. -/
  | cpAsyncCommit
  /-- `cp.async.wait_group N` (`all` false) or `cp.async.wait_all` (`all` true, `remaining` 0). -/
  | cpAsyncWait (all : Bool) (remaining : Nat)
  /-- `cp.async.mbarrier.arrive{.noinc}{.shared{::cta}}.b64 [base + offset]`; `generic` when no
  state space is written. -/
  | cpAsyncArrive (noinc : Bool) (base : Nat) (offset : Int) (generic : Bool := false)
  /-- `cp.async.bulk.prefetch.L2.global{.L2::cache_hint, .L2::evict_last} [src], size{,
  cachePolicy}`. -/
  | prefetchBulk (src : Nat) (srcOff : Int) (size : Opnd) (cachePolicy : Option Opnd)
  /-- `mbarrier.try_wait.parity{.sem}{.scope}.shared{::cta}.b64 p, [base + offset], parity{, hint}`.
  The suspend-time hint is dropped. Defaults are the PTX defaults (`.acquire.cta`). -/
  | mbarWait (dst : Nat) (base : Nat) (offset : Int) (parity : Opnd)
      (acquire : Bool := true) (scope : MbarScope := .cta)
  /-- `tcgen05.alloc.cta_group::{1,2}.sync.aligned.shared::cta.b32 [base + offset], n`. -/
  | tcAlloc (group : CtaGroup) (base : Nat) (offset : Int) (n : Opnd)
  /-- `tcgen05.dealloc.cta_group::{1,2}.sync.aligned.b32 taddr, n`. -/
  | tcDealloc (group : CtaGroup) (taddr n : Opnd)
  /-- `tcgen05.relinquish_alloc_permit.cta_group::{1,2}.sync.aligned`. -/
  | tcRelinquish (group : CtaGroup)
  /-- `tcgen05.mma` in every form of the instruction table (PROG-ISA-TC-MMA). -/
  | tcMma (m : TcMmaInstr)
  /--
  `tcgen05.commit.cta_group::{1,2}.mbarrier::arrive::one.shared::cluster{.multicast::cluster}.b64
  [base + offset]{, mask}`. -/
  | tcCommit (group : CtaGroup) (base : Nat) (offset : Int) (mask : Option Opnd)
  /-- `tcgen05.fence::before_thread_sync`. -/
  | tcFenceBefore
  /-- `tcgen05.fence::after_thread_sync`. -/
  | tcFenceAfter
  /-- `tcgen05.ld.sync.aligned.<shape>.x<num>.b32 {d0, ...}, [taddr]{, immHalfSplitoff}`. The
  shape is last and defaults to `.32x32b`, so a program written before shapes existed keeps its
  text. With `red`, `tcgen05.ld.red` (PROG-ISA-TC-LD-RED). -/
  | tcLd (dsts : List Nat) (taddr : Nat) (shape : TcShape := .s32x32b)
      (red : Option TcLdRed := none)
  /-- `tcgen05.wait::ld.sync.aligned`. -/
  | tcWaitLd
  /-- `tcgen05.st.sync.aligned.<shape>.x<num>.b32 [taddr], {immHalfSplitoff,} {s0, ...}`; the
  shape as for `tcLd`. -/
  | tcSt (taddr : Nat) (srcs : List Opnd) (shape : TcShape := .s32x32b)
  /-- `tcgen05.wait::st.sync.aligned`. -/
  | tcWaitSt
  /-- `tcgen05.cp.cta_group::{1,2}.<shape>{.<multicast>}{.b8x16.<src_fmt>} [taddr], s-desc`
  (PROG-ISA-TC-CP); `fmt` is the decompression, none when not written. -/
  | tcCp (group : CtaGroup) (shape : TcCpShape) (taddr : Nat) (sdesc : Opnd)
      (fmt : Option TcCpFmt := none)
  /-- `tcgen05.shift.cta_group::{1,2}.down [taddr]` (§9.7.18.9.3). -/
  | tcShift (group : CtaGroup) (taddr : Nat)
  /-- An instruction recognized by the grammar that has no family representation this round
  (PROG-DECODE); no rule gives it semantics. -/
  | unmodeled (r : Isa.Raw)
  deriving Repr

/-- One instruction of a kernel: an optional guard predicate and the operation. -/
structure Instr where
  /-- `some (p, negated)`: execute only when predicate `p` is true (or false if negated). -/
  guard : Option (Nat × Bool) := none
  op : Op
  deriving Repr

/-- The state space a `.ptr` kernel parameter points into (§5.1.6.3:
`.space = { .const, .global, .local, .shared }`). -/
inductive PtrSpace where
  | const | global | «local» | shared
  deriving DecidableEq, Repr

/-- The `.ptr` attribute of a pointer kernel parameter (§5.1.6.3): the state space of the
memory pointed to (`none`: a generic address) and its alignment (4 bytes when not written). -/
structure PtrDecl where
  space : Option PtrSpace
  align : Nat
  deriving DecidableEq, Repr

/-- A decoded kernel: parameters, static shared memory size, parameter objects, launch
constraints, register names and the instruction list, whose indices are the source positions. -/
structure Kernel where
  name : String
  /-- Parameter names and their widths in bits. -/
  params : List (String × Nat)
  /-- Bytes of statically declared `.shared` memory per CTA. -/
  sharedBytes : Nat := 0
  /-- By-value array parameters, separate from scalar parameter values. -/
  paramObjects : List ParamObjectDecl := []
  /-- The `.ptr` attributes of pointer parameters that constrain a launch (a state space or an
alignment above 1), by parameter name. -/
  ptrParams : List (String × PtrDecl) := []
  /-- `.maxntid` bound on the CTA size (the product of its extents), if declared. -/
  maxThreads : Option Nat := none
  /-- `.reqntid` CTA shape `(nx, ny, nz)`, if declared; an extent not written is 1. -/
  reqThreads : Option (Nat × Nat × Nat) := none
  /-- `.minperctamemory` size in bytes, if declared (§11.5.10); the `%perctamemory` registers
  decode only when it is. -/
  minPerCtaMemory : Option Nat := none
  /-- The source name of each register, by id; for diagnostics only. -/
  regNames : List String := []
  code : List Instr
  deriving Repr

/-! ## PROG-INSTR-EVENTS — which instructions perform events
Statement: An instruction that accesses memory, synchronizes with other threads, issues an
  asynchronous operation, ends the thread or has another effect outside the thread's registers
  performs an event, and so does an instruction that reads a special register whose value changes
  while the thread runs. Every other instruction only reads and writes the thread's own registers
  and source position.

Defs: Opnd.varying?, Op.varyingSregs, Op.isLocal, Op.isLocal_of_varyingSregs

Source:
- §10.4: "Note that %warpid returns the location of a thread at the moment when read, but its value
    may change during execution"
- §8.2 (memory operations)
- §9.7.15.1 (bar)
- §9.7.15.3 (barrier.cluster)
- §9.7.10.6 (shfl.sync)
- §9.7.15.10 (vote.sync)
- §9.7.14.6 (ret)
- §9.7.15.16 (mbarrier)
- §9.7.10.28.4.1 (cp.async.bulk)
- §9.7.10.28.3 (cp.async and its groups)
- §9.7.10.28.4.3 (cp.async.bulk.prefetch)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.10.28.5.5 (cp.async.bulk.prefetch.tensor)
- §9.7.18 (tcgen05)

Direction: equal

Effect: Exactly these instructions perform an event (`Op.isLocal` is false): `setmaxnreg`, every
  memory access (`Op.mem`: `ld`, `st`, `atom`, `red`) except `ld.param`, every warp collective
  (`Op.warp`: `shfl.sync`, `vote.sync`, `match.sync`, `redux.sync`, `activemask`, `elect.sync`,
  `bar.warp.sync`), every warp-level matrix instruction (`Op.matrix`: `ldmatrix`, `stmatrix`,
  `movmatrix`, `mma`, `mma.sp`), `barrier{.cta}` (`sync` with and without a thread count, `arrive`),
  `barrier.cluster`, `ret`, `exit`, `trap`, every fence (`Op.fence`: thread fences, `membar` and
  proxy fences), the mbarrier-initialization fence, the mbarrier instructions (`init`, `inval`,
  arrive, wait), the copies (`cp.async`, `cp.async.bulk`, `cp.reduce.async.bulk` and the tensor
  loads and stores), `st.async`, `red.async`, bulk-group and `cp.async`-group commit and wait,
  `cp.async.mbarrier.arrive`, the data prefetches (`cp.async.bulk.prefetch` and
  `cp.async.bulk.prefetch.tensor`), the cluster launch control `try_cancel` and response query,
  every `tcgen05` instruction (alloc, dealloc, relinquish, mma in every form, commit, both fences,
  ld, st, their waits, cp), and an `Op.unmodeled` instruction whose entry has the effect class
  `event` (PROG-ISA-ENTRY: an address operand or memory ordering). An integer, move or conversion
  instruction with a source operand that reads `%warpid`, `%smid`, `%clock`, `%clock_hi`, `%clock64`
  or a `%globaltimer` register (`Op.varyingSregs`) performs the read event of THREAD-SREG.
  `ld.param` reads the launch's parameters (THREAD-MOVE) and is local. Every other instruction,
  including the tensormap prefetch and the cache instructions `prefetch`, `prefetchu` and
  `applypriority` (`Op.addr`, THREAD-PREFETCH), only reads and writes this thread's registers and
  `pc`, so an instruction marked local never touches memory or another thread.
-/

/-- The special register an operand reads, when its value changes while the thread runs
(THREAD-SREG). -/
def Opnd.varying? : Opnd → Option SReg
  | .sreg s => if s.varying then some s else none
  | _ => none

/-- The source operands of an integer, move or conversion instruction that read a special register
whose value changes while the thread runs, in operand order; none for every other instruction. -/
def Op.varyingSregs : Op → List SReg
  | .int i => i.srcs.filterMap Opnd.varying?
  | .move m => m.srcs.filterMap Opnd.varying?
  | .cvt c => c.srcs.filterMap Opnd.varying?
  | _ => []

/-- The instruction only reads and writes the thread's registers and source position, and
performs no event. -/
def Op.isLocal : Op → Bool
  | .mem a => a.kind == .load && a.space == some .param
  | op@(.int _) | op@(.move _) | op@(.cvt _) => op.varyingSregs.isEmpty
  | .setMaxReg .. | .warp .. | .matrix .. | .barSync .. | .barSyncN .. | .barArrive .. | .cluster ..
  | .ret
  | .exit | .trap
  | .cpTensorStore .. | .bulkCommit | .bulkWait .. | .cpTensor .. | .prefetchTensor ..
  | .clcTryCancel .. | .clcQuery .. | .mbarArrive .. | .mbarWait .. | .mbarInit .. | .mbarInval ..
  | .fence .. | .fenceMbarInit | .cpBulk .. | .cpAsync .. | .cpAsyncCommit
  | .cpAsyncWait .. | .cpAsyncArrive .. | .prefetchBulk .. | .asyncStore .. => false
  | .tcAlloc .. | .tcDealloc .. | .tcMma .. | .tcCommit .. | .tcFenceBefore
  | .tcFenceAfter
  | .tcLd .. | .tcWaitLd | .tcSt .. | .tcWaitSt | .tcCp .. | .tcShift .. | .tcRelinquish .. =>
    false
  | .unmodeled r => r.entry.effect == .local_
  | _ => true

/-- An integer, move or conversion instruction that reads no changing special register is local,
as before THREAD-SREG's read event. -/
theorem Op.isLocal_of_varyingSregs {op : Op} (h : op.varyingSregs = [])
    (hop : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c) : op.isLocal = true := by
  rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;> simp [Op.isLocal, h]

/-! ## PROG-INSTR-RULE — the rule of every instruction
Statement: An instruction of a family has the rule that the family's `rule` function names
  (PROG-RULE-ID). `bra` and `brx.idx` have THREAD-BRANCH, a tensormap prefetch
  THREAD-TENSORMAP-PREFETCH, a CTA barrier THREAD-BAR, a cluster barrier
  OBJ-CLUSTER-BARRIER-SYNC, `setmaxnreg` THREAD-SETMAXNREG, a tensor load THREAD-TENSOR-ISSUE, a
  tensor-data or linear prefetch
  THREAD-TENSOR-PREFETCH, a tensor store or reduction and the bulk-group commit and wait
  THREAD-TENSOR-STORE, the cluster launch control instructions THREAD-CLC-QUERY, the mbarrier
  instructions, the mbarrier-initialization fence, `cp.async.bulk` and `cp.reduce.async.bulk`
  THREAD-TMA, `st.async` and `red.async` THREAD-ASYNC-STORE, the thread and
  proxy fences THREAD-FENCE, `cp.async`, its group commit and wait
  and `cp.async.mbarrier.arrive` THREAD-CP-ASYNC, `tcgen05.commit` THREAD-TC-COMMIT,
  `tcgen05.mma` the rule `TcMmaInstr.rule` names (PROG-ISA-TC-MMA), every other `tcgen05`
  instruction THREAD-TC, and `ret`, `exit` and `trap` THREAD-RUN. `Op.unmodeled` has no rule.

Defs: Op.rule

Source:
- none (dispatch)

Direction: representation

Applies: Every decoded instruction

Premises: None.

Effect: `execLocal` dispatches through it (THREAD-LOCAL), and `eventTmpl` equals the template of the
  rule it names, or `ub noRule` without one (`eventTmpl_rule`, THREAD-RUN). The instruction tables
  of the documentation take each instruction's status from it.
-/

/-- The contract entry whose rule gives the instruction its semantics, or none when the model has
no rule for it. -/
def Op.rule : Op → Option RuleId
  | .int i => i.rule
  | .float f => f.rule
  | .move m => m.rule
  | .cvt c => c.rule
  | .mem a => a.rule
  | .addr c => c.rule
  | .warp w => w.rule
  | .matrix m => m.rule
  | .misc m => m.rule
  | .bra .. | .brx .. => some .threadBranch
  | .prefetchTensorMap .. => some .threadTensorMapPrefetch
  | .barSync .. | .barSyncN .. | .barArrive .. => some .threadBar
  | .cluster .. => some .clusterBarrier
  | .setMaxReg .. => some .threadSetMaxNReg
  | .cpTensor .. => some .threadTensorIssue
  | .prefetchTensor .. | .prefetchBulk .. => some .threadTensorPrefetch
  | .cpTensorStore .. | .bulkCommit | .bulkWait .. => some .threadTensorStore
  | .clcTryCancel .. | .clcQuery .. => some .threadClc
  | .fence f => f.rule
  | .mbarInit .. | .mbarInval .. | .fenceMbarInit | .mbarArrive .. | .mbarWait ..
  | .cpBulk .. => some .threadTma
  | .cpAsync .. | .cpAsyncCommit | .cpAsyncWait .. | .cpAsyncArrive .. => some .threadCpAsync
  | .asyncStore .. => some .threadAsyncStore
  | .tcCommit .. => some .threadTcCommit
  | .tcMma m => m.rule
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcFenceBefore
  | .tcFenceAfter | .tcLd .. | .tcWaitLd | .tcSt .. | .tcWaitSt | .tcCp .. | .tcShift .. =>
    some .threadTc
  | .ret | .exit | .trap => some .threadRun
  | .unmodeled _ => none

/-- The instruction carries `.aligned`: all threads of the warp execute it together. -/
def Op.aligned : Op → Bool
  | .barSync _ aligned | .barSyncN _ _ aligned | .barArrive _ _ aligned => aligned
  | .cluster op => op.aligned
  | .setMaxReg .. | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcLd .. | .tcWaitLd
  | .tcSt .. | .tcWaitSt | .matrix .. => true
  | _ => false

end PTX
