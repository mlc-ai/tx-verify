-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Types
public import Core.Async.Tensor.TensorMemory
public import Core.Async.Tensor.TensorStoreMemory
public import Core.Async.AsyncCopy
public import Core.Tc.TcMmaResultLayout
public import Core.Tc.TcCopy

@[expose] public section

/-!
# Event queries and execution growth

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## MEM-EXECUTION-QUERIES — reading an execution
Statement: The event at a position of an execution is found by thread and trace index. The remaining
  queries are projections that say which kind of event it is, such as a read, a write, a barrier
  arrival, an mbarrier operation or a `tcgen05` instruction, and what it names. They add no
  constraint.

Defs: wbyte, Execution.get, Execution.Reads, Execution.NcReads, Execution.Writes, Execution.Rmw,
  Execution.Access, Execution.access_iff_of_not_rmw,
  Execution.IsBarrier, Execution.IsBarArrival, Execution.isBar, Execution.isShfl,
  Execution.MbInit, Execution.MbInval, Execution.Arrive, Execution.Copy, Execution.BulkPrefetch,
  Execution.Copy.unique, Execution.AsyncArrive, Execution.IsProxyFence, Execution.ThreadFence,
  Execution.AcquireWait, Execution.UsesMbar, Execution.UsesMbar.of_init,
  Execution.UsesMbar.of_inval, Execution.UsesMbar.of_tensor, Execution.UsesMbar.of_clc,
  Execution.UsesMbar.of_old,
  Execution.MmaIssue, Execution.MmaCell, Execution.MmaReadCell, Execution.MmaACell,
  Execution.MmaAccess, Execution.Commit, Execution.FenceBefore, Execution.FenceAfter, Execution.TLd,
  Execution.WaitLd, Execution.TSt, Execution.CpIssue, Execution.ShiftIssue, Execution.TcAsync,
  Execution.ClcIssue, Execution.TensorIssue, Execution.TensorStoreIssue,
  Execution.TensorPrefetchIssue

Source:
- none (projections)

Direction: representation

Effect: These queries say which event is at a position and what it reads or writes. `Access`
  collects the reads and writes that are memory operations of the consistency model (§8.1), an
  atomic read-modify-write (`Rmw`) as both; `nc` reads are separate (`NcReads`). `wbyte a bs l` is
  the byte a write of `bs` to `a` stores at `l`. A linear copy's write is an independent effect
  keyed by its issuing instruction (MEM-FOOTPRINT); mbarrier events are named by what they do to
  the object at `m`; `tcgen05` events by their instruction. `UsesMbar` lists every event that names
  an mbarrier operand, the initialization included.
-/

/-- Byte `l` as written by a write of `bs` to `a`. -/
def wbyte (a : Acc) (bs : List Byte) (l : Loc) : Option Byte := bs[l.addr - a.loc.addr]?

namespace Execution

variable (X : Execution)

/-- The event at position `e` of the execution: thread `e.1`, trace index `e.2`. -/
def get (e : EvId) : Option Event := (X.tr e.1)[e.2]?

def TensorIssue (i : EvId) (mapAddress : Nat) (s : TensorCopy.Spec) : Prop :=
  ∃ pc, X.get i = some ⟨pc, .tensorIssue mapAddress s⟩

def TensorStoreIssue (i : EvId) (mapAddress : Nat) (s : TensorStore.Spec) : Prop :=
  ∃ pc, X.get i = some ⟨pc, .tensorStore mapAddress s⟩

def TensorPrefetchIssue (i : EvId) (mapAddress : Nat) (s : TensorPrefetch.Spec) : Prop :=
  ∃ pc, X.get i = some ⟨pc, .tensorPrefetch mapAddress s⟩

/-- `e` is a weak generic-proxy read of footprint `a` that returned the bytes `bs`. -/
def Reads (e : EvId) (a : Acc) (bs : List (Option Byte)) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .rd a bs⟩

/-- `e` is an `ld.global.nc` read of footprint `a` that returned the bytes `bs`. -/
def NcReads (e : EvId) (a : Acc) (bs : List (Option Byte)) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .nc a bs⟩

/-- `e` is a weak generic-proxy write of the bytes `bs` to footprint `a`. -/
def Writes (e : EvId) (a : Acc) (bs : List Byte) : Prop := ∃ pc, X.get e = some ⟨pc, .wr a bs⟩

/-- `e` is an atomic read-modify-write of footprint `a` that read the bytes `old` and wrote the
bytes `new` (`none`: it has no result, THREAD-ATOMIC). -/
def Rmw (e : EvId) (a : Acc) (old : List (Option Byte)) (new : Option (List Byte)) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .rmw a old new⟩

/-- A memory operation of the consistency model (`nc` reads are not): footprint `a`;
`w` says whether it writes. An atomic read-modify-write both reads and writes. -/
def Access (e : EvId) (a : Acc) (w : Bool) : Prop :=
  (∃ bs, X.Reads e a bs ∧ w = false) ∨ (∃ bs, X.Writes e a bs ∧ w = true) ∨
    ∃ old new, X.Rmw e a old new

/-- An event that is not an atomic read-modify-write is the access it was before THREAD-ATOMIC:
a read or a write. -/
theorem access_iff_of_not_rmw {X : Execution} {e : EvId} {a : Acc} {w : Bool}
    (hn : ∀ pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) :
    X.Access e a w ↔ (∃ bs, X.Reads e a bs ∧ w = false) ∨ (∃ bs, X.Writes e a bs ∧ w = true) := by
  refine ⟨fun h => ?_, fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  rcases h with h | h | ⟨o, n, pc, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hn pc a o n)

/-- `bar.sync` arrival with its actual count operand, including partial-CTA barriers. -/
def IsBarrier (e : EvId) (id : Nat) (count : Option Nat) (pc : Nat) : Prop :=
  X.get e = some ⟨pc, .bar id count .sync⟩

/-- Arrival of either form, `bar.sync` or `bar.arrive`. -/
def IsBarArrival (e : EvId) (id : Nat) (count : Option Nat) (pc : Nat) : Prop :=
  ∃ mode, X.get e = some ⟨pc, .bar id count mode⟩

/-- A barrier arrival of either form. -/
def isBar : Event → Bool
  | ⟨_, .bar ..⟩ => true
  | _ => false

def isShfl : Event → Bool
  | ⟨_, .shfl ..⟩ => true
  | _ => false

/-- `e` initializes the mbarrier object at `m` with arrival count `c`. -/
def MbInit (e : EvId) (m : Loc) (c : Nat) : Prop := ∃ pc, X.get e = some ⟨pc, .mbInit m c⟩

/-- `e` invalidates the mbarrier object at `m`. -/
def MbInval (e : EvId) (m : Loc) : Prop := ∃ pc, X.get e = some ⟨pc, .mbInval m⟩

/-- `e` performs `count` arrivals on `m` after expecting `tx` bytes, with the given semantics. -/
def Arrive (e : EvId) (m : Loc) (tx count : Nat) (release : Bool) (scope : MbarScope) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .arrive m tx count release scope⟩

/-- `e` issues the linear copy `s` (`cp.async` or `cp.async.bulk`). -/
def Copy (e : EvId) (s : AsyncCopy.Spec) : Prop := ∃ pc, X.get e = some ⟨pc, .copy s⟩

/-- An instruction instance issues at most one linear operation. -/
theorem Copy.unique {X : Execution} {e : EvId} {s s' : AsyncCopy.Spec} (h : X.Copy e s)
    (h' : X.Copy e s') : s = s' := by
  obtain ⟨pc, h⟩ := h
  obtain ⟨pc', h'⟩ := h'
  rw [h] at h'
  cases h'
  rfl

/-- `e` is a `cp.async.bulk.prefetch` of the global range `a`. -/
def BulkPrefetch (e : EvId) (a : Acc) : Prop := ∃ pc, X.get e = some ⟨pc, .bulkPrefetch a⟩

/-- `e` is a `cp.async.mbarrier.arrive` on the mbarrier object at `m`, with `.noinc` when
`noinc`. -/
def AsyncArrive (e : EvId) (m : Loc) (noinc : Bool) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .asyncArrive m noinc⟩

/-- `e` is a proxy fence of kind `k` with scope `scope` (`none` for a form without a scope). -/
def IsProxyFence (e : EvId) (k : ProxyFence) (scope : Option MbarScope) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .fenceProxy k scope⟩

/-- `e` is a thread fence with semantics `sem` and scope `scope`. -/
def ThreadFence (e : EvId) (sem : FenceSem) (scope : MbarScope) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .fence sem scope⟩

/-- `e` is a successful acquire parity wait on `m` at some scope; phase matching is in the
object log. A relaxed wait does not acquire. -/
def AcquireWait (e : EvId) (m : Loc) : Prop :=
  ∃ pc parity scope, X.get e = some ⟨pc, .wait m parity true true scope⟩

/-- `e` is a `tcgen05.commit` with specification `s`, which names its mbarrier and the cluster
ranks that receive a completion notification. -/
def Commit (e : EvId) (s : TcCommit.Spec) : Prop := ∃ pc, X.get e = some ⟨pc, .tc (.commit s)⟩

/-- An MMA issue fixes addresses and operation parameters, but no future read values.
Destination, accumulation and lane masks are preserved. -/
def MmaIssue (e : EvId) (d : Nat) (s : TcMma.OperandSpec)
    (accumulate : Bool) (mask : List Nat) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .tc (.mma d s accumulate mask)⟩

/-- Potential TMEM writes exist at issue, with physical CTA/lane/column identity.
Only unmasked result elements contribute; this is not an assertion of completion. -/
def MmaCell (i : EvId) (cell : TcMma.Cell) : Prop :=
  ∃ d s accum mask row col, X.MmaIssue i d s accum mask ∧
    TcMma.writeCell s d mask row col = some cell

/-- Potential old-D reads when accumulation is enabled. Output lane masks suppress
writes; they are not taken as a guarantee that an old-D read is suppressed. -/
def MmaReadCell (i : EvId) (cell : TcMma.Cell) : Prop :=
  ∃ d s mask row col, X.MmaIssue i d s true mask ∧
    TcMma.resultCell s d row col = some cell

/-- Tensor Memory cells of an A operand read from Tensor Memory. -/
def MmaACell (i : EvId) (cell : TcMma.Cell) : Prop :=
  ∃ d s accum mask index b, X.MmaIssue i d s accum mask ∧ TcMma.aCell s index = some (cell, b)

/-- Physical TMEM access footprint, including masked accumulator reads and A reads. -/
def MmaAccess (i : EvId) (cell : TcMma.Cell) : Prop :=
  X.MmaCell i cell ∨ X.MmaReadCell i cell ∨ X.MmaACell i cell

/-- `e` is a `tcgen05.fence::before_thread_sync`. -/
def FenceBefore (e : EvId) : Prop := ∃ pc, X.get e = some ⟨pc, .tc .fenceBefore⟩

/-- `e` is a `tcgen05.fence::after_thread_sync`. -/
def FenceAfter (e : EvId) : Prop := ∃ pc, X.get e = some ⟨pc, .tc .fenceAfter⟩

/-- `e` is a `tcgen05.ld` of access shape `shape` from Tensor Memory address `a` that returns
the values `vals`. -/
def TLd (e : EvId) (a : Nat) (vals : List Value) (shape : TcShape) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .tc (.ld a vals shape)⟩

/-- `e` is a `tcgen05.wait::ld`. -/
def WaitLd (e : EvId) : Prop := ∃ pc, X.get e = some ⟨pc, .tc .waitLd⟩

/-- `e` is a `tcgen05.st` of access shape `shape` that stores the values `vals` to Tensor Memory
address `a`. -/
def TSt (e : EvId) (a : Nat) (vals : List Value) (shape : TcShape) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .tc (.st a vals shape)⟩

/-- `e` issues the `tcgen05.cp` `c` (THREAD-TC-CP-CELLS). Its source reads and its completion are
asynchronous stages. -/
def CpIssue (e : EvId) (c : TcCopy.Spec) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .tc (.cp c)⟩

/-- `e` issues the `tcgen05.shift` `s` (THREAD-TC-SHIFT-CELLS). Its Tensor Memory reads and writes
and its completion are asynchronous. -/
def ShiftIssue (e : EvId) (s : TcShift.Spec) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .tc (.shift s)⟩

/-- An asynchronous tcgen05 operation whose completion `tcgen05.commit` tracks: an MMA, a copy
or a shift (§9.7.18.6.2.1.1). -/
def TcAsync (e : EvId) : Prop :=
  (∃ d s accum mask, X.MmaIssue e d s accum mask) ∨ (∃ c, X.CpIssue e c) ∨
    ∃ s, X.ShiftIssue e s

def ClcIssue (i : EvId) (s : Clc.Spec) (targets : List Nat) : Prop :=
  ∃ pc, X.get i = some ⟨pc, .clcIssue s targets⟩

/-- `e` names the mbarrier object at `m` as an operand: an arrive, a linear copy with mbarrier
completion, a `cp.async.mbarrier.arrive`, a target of a `tcgen05.commit`, a poll, an
invalidation, a tensor load, the mbarrier of a target CTA of a cluster launch control request, or
an initialization. -/
def UsesMbar (e : EvId) (m : Loc) : Prop :=
  (∃ tx count release scope, X.Arrive e m tx count release scope) ∨
    (∃ s, X.Copy e s ∧ s.completion = .mbarrier m) ∨ (∃ noinc, X.AsyncArrive e m noinc) ∨
    (∃ s rank, X.Commit e s ∧ TcCommit.target s rank = some m) ∨
    (∃ pc q ok acquire scope, X.get e = some ⟨pc, .wait m q ok acquire scope⟩) ∨
    X.MbInval e m ∨ (∃ address s, X.TensorIssue e address s ∧ s.mbar = m) ∨
    (∃ s targets c, X.ClcIssue e s targets ∧ c ∈ targets ∧ m = { s.mbar with cta := c }) ∨
    ∃ count, X.MbInit e m count

/-- An initialization names its mbarrier (`UsesMbar`, last disjunct). -/
theorem UsesMbar.of_init {X : Execution} {e : EvId} {m : Loc} {count : Nat}
    (h : X.MbInit e m count) : X.UsesMbar e m :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨count, h⟩)))))))

/-- An invalidation names its mbarrier (`UsesMbar`; it was the last disjunct before the tensor
load, CLC and initialization disjuncts were added). -/
theorem UsesMbar.of_inval {X : Execution} {e : EvId} {m : Loc} (h : X.MbInval e m) :
    X.UsesMbar e m :=
  .inr (.inr (.inr (.inr (.inr (.inl h)))))

/-- A tensor load names its mbarrier (`UsesMbar`). -/
theorem UsesMbar.of_tensor {X : Execution} {e : EvId} {address : Nat} {s : TensorCopy.Spec}
    (h : X.TensorIssue e address s) : X.UsesMbar e s.mbar :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨address, s, h, rfl⟩))))))

/-- A cluster launch control request names the mbarrier of each target CTA (`UsesMbar`). -/
theorem UsesMbar.of_clc {X : Execution} {e : EvId} {s : Clc.Spec} {targets : List Nat} {c : Nat}
    (h : X.ClcIssue e s targets) (hc : c ∈ targets) :
    X.UsesMbar e { s.mbar with cta := c } :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨s, targets, c, h, hc, rfl⟩)))))))

/-- The old `UsesMbar` (without tensor loads, CLC targets and initializations) is part of the
new one: its first five disjuncts keep their positions and its last is `UsesMbar.of_inval`. -/
theorem UsesMbar.of_old {X : Execution} {e : EvId} {m : Loc}
    (h : (∃ tx count release scope, X.Arrive e m tx count release scope) ∨
      (∃ s, X.Copy e s ∧ s.completion = .mbarrier m) ∨ (∃ noinc, X.AsyncArrive e m noinc) ∨
      (∃ s rank, X.Commit e s ∧ TcCommit.target s rank = some m) ∨
      (∃ pc q ok acquire scope, X.get e = some ⟨pc, .wait m q ok acquire scope⟩) ∨
      X.MbInval e m) : X.UsesMbar e m := by
  rcases h with h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact UsesMbar.of_inval h

/-! ## MEM-FOOTPRINT — thread and asynchronous memory accesses
Statement: Every thread access and every stage of an asynchronous operation has a footprint and a
  direction. The footprint of a stage is fixed by its issuing instruction when the instruction
  executes, even while the stage is pending, and the effect records say which stages have happened.
  These queries assert no ordering and no read values.

Defs: Execution.MmaFootprint, Execution.MmaRead, Execution.MemReads, Execution.MemWrites,
  Execution.memReads_thread_iff_of_not_rmw, Execution.memWrites_thread_iff_of_not_rmw,
  Execution.memWrites_write_copy_of_whole, Execution.asyncFootprint_write_copy_of_whole,
  Execution.AsyncFootprint, Execution.Intent, Execution.MemTouches, Execution.AsyncPresent,
  Execution.RefPresent

Source:
- §9.7.10.28.1 (independent async execution)
- §9.7.18.6.5 (MMA operands use the async proxy)
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.15.16.18 (the arrive-on of cp.async.mbarrier.arrive is asynchronous)

Direction: representation

Applies: Ordinary accesses and the stages of linear and tensor copies, tensor stores and
  reductions, tensor and linear prefetch reads, CLC responses, the represented MMA operands,
  tcgen05.cp sources and the arrive-on of cp.async.mbarrier.arrive

Premises: Actual instruction events determine all footprints; effect records determine which reads
  and writes have happened.

Effect: Unified memory queries; no ordering or read values are asserted here. A thread's atomic
  read-modify-write is one event that is both a read and a write of its footprint (`Rmw`): its read
  is in `MemReads` and its write, when the operation has a result, in `MemWrites`, both under the
  event's own reference. The footprint of an asynchronous stage is given by its issuing instruction
  and slot (`AsyncFootprint`), and its direction is that of its part (`Part.writes`). A reduction
  also reads each destination byte it writes, as its own read (`.old`) with a read intent at the
  write's footprint. Whether a stage is present is read from the storage of its slot's kind
  (`AsyncPresent`). The safety checks see the footprint of a pending stage before its completion, so
  an early consumer cannot evade checking by omitting the pending write. A tensor prefetch's read
  (`.read (.prefetch ..)`) has the footprint of a tensor load's source read of the same selection
  (`TensorTransfer.sourceLoc`) and is never present, so it returns no value and has no completion. A
  linear prefetch's read (`.read .copy` of a `cp.async.bulk.prefetch`) has the footprint of its
  global range and is never present either (`issuedBy` gives it no copy specification, so its
  effects stay empty) (EXT-PREFETCH-PENDING, THREAD-TENSOR-PREFETCH).
-/

/-- The footprint exists at issue, independently of the operand observation. A
`tcgen05.cp` reads its source as an A operand, CTA by CTA: byte `k * sourceBytes + j` is byte `j`
of the `k`-th CTA of the copy. -/
def MmaFootprint (i : EvId) (isB : Bool) (index : Nat) (l : Loc) : Prop :=
  (∃ d s accum mask, X.MmaIssue i d s accum mask ∧
    s.byteLoc (if isB then .b else .a) index = some l) ∨
  (∃ c k cta, X.CpIssue i c ∧ isB = false ∧ c.ctas[k]? = some cta ∧
    index / c.shape.sourceBytes = k ∧
    TcCopy.byteLoc c.shape c.src cta (index % c.shape.sourceBytes) = some l)

/-- A byte observed by the MMA, with no implicit launch-memory source. -/
def MmaRead (i : EvId) (isB : Bool) (index : Nat) (l : Loc) (b : Option Byte) : Prop :=
  X.MmaFootprint i isB index l ∧ ∃ operands,
    X.async.mmaOperands i = some operands ∧
    (if isB then operands.b else operands.a)[index]? = some b

/-- Actual read effects: a thread's read or the read of its atomic read-modify-write, one byte per
non-contiguous MMA operand location, and the reads of copies, tensor stores and loads. -/
def MemReads : AsyncCopy.Ref → Acc → List (Option Byte) → Prop
  | .async i (.mmaRead isB index), a, bs =>
    ∃ b, X.MmaRead i isB index a.loc b ∧ a.size = 1 ∧ bs = [b]
  | .async i (.read (.store x y k)), a, bs =>
    ∃ o addr b, X.tensorStores i = some o ∧ X.TensorStoreIssue i addr o.spec ∧
      TensorStore.readLoc o.spec x y k = some a.loc ∧
      TensorStore.readByte o x y k = some b ∧ a.size = 1 ∧ bs = [some b]
  | .async i (.old (.store x y k)), a, bs =>
    ∃ o addr b, X.tensorStores i = some o ∧ X.TensorStoreIssue i addr o.spec ∧
      o.spec.reduce.isSome ∧ TensorStore.writeLoc o.spec x y k = some a.loc ∧
      TensorStore.oldByte o x y k = some b ∧ a.size = 1 ∧ bs = [some b]
  | .async i (.read (.load x y k)), a, bs =>
    ∃ o addr b, X.tensor i = some o ∧ X.TensorIssue i addr o.spec ∧
      TensorCopy.readLoc o.spec x y k = some a.loc ∧
      TensorCopy.readByte o x y k = some b ∧ a.size = 1 ∧ bs = [some b]
  | .thread e, a, bs => X.Reads e a bs ∨ ∃ new, X.Rmw e a bs new
  | .async i (.read .copy), a, bs =>
    ∃ s raw, X.Copy i s ∧ s.src = a ∧ (X.async.copies i).readBytes = some raw ∧
      bs = raw.map some
  | .async i (.old (.elem j)), a, bs =>
    ∃ s r raw, X.Copy i s ∧ s.writes = .reduce r ∧ s.elems[j]? = some a ∧
      (X.async.copies i).elemOld j = some raw ∧ bs = raw.map some
  | _, _, _ => False

/-- The bytes that a write puts at an access: a thread's store or the write of its atomic
read-modify-write, or a write stage of an
asynchronous operation that has happened (a tile byte of a tensor store or tensor load, the CLC
response at a target CTA, or the destination range of a linear copy). -/
def MemWrites : AsyncCopy.Ref → Acc → List Byte → Prop
  | .async i (.write (.store x y k)), a, bs =>
    ∃ o addr b, X.tensorStores i = some o ∧ X.TensorStoreIssue i addr o.spec ∧
      TensorStore.writeLoc o.spec x y k = some a.loc ∧
      TensorStore.writeByte o x y k = some b ∧ a.size = 1 ∧ bs = [b] ∧
      a.acquire = false ∧ a.release = false ∧ a.scope = .cta ∧ a.elem = 0
  | .async i (.write (.load x y k)), a, bs =>
    ∃ o addr b, X.tensor i = some o ∧ X.TensorIssue i addr o.spec ∧
      TensorCopy.writeLoc o.spec x y k = some a.loc ∧
      TensorCopy.writeByte o x y k = some b ∧ a.size = 1 ∧ bs = [b] ∧
      a.acquire = false ∧ a.release = false ∧ a.scope = .cta ∧ a.elem = 0
  | .async i (.write (.cta c)), a, bs =>
    ∃ s targets, X.ClcIssue i s targets ∧ c ∈ targets ∧ Clc.ResponseWrite s (X.clc i) c a bs
  | .thread e, a, bs => X.Writes e a bs ∨ ∃ old, X.Rmw e a old (some bs)
  | .async i (.write .copy), a, bs => ∃ s,
    X.Copy i s ∧ s.writes = .whole ∧ s.dst = a ∧ (X.async.copies i).writeBytes = some bs
  | .async i (.write (.elem j)), a, bs => ∃ s,
    X.Copy i s ∧ s.elems[j]? = some a ∧ (X.async.copies i).elemWrites j = some bs
  | _, _, _ => False

/-- The write stage of a linear operation that writes its destination whole (every operation of
the forms before element-wise writes) writes as before: the destination with the recorded bytes. -/
theorem memWrites_write_copy_of_whole {X : Execution} {i : EvId} {s : AsyncCopy.Spec} {a : Acc}
    {bs : List Byte} (hc : X.Copy i s) (hw : s.writes = .whole) :
    X.MemWrites (.async i (.write .copy)) a bs ↔
      s.dst = a ∧ (X.async.copies i).writeBytes = some bs := by
  constructor
  · rintro ⟨s', hc', -, hd, hb⟩
    cases Copy.unique hc hc'
    exact ⟨hd, hb⟩
  · rintro ⟨hd, hb⟩
    exact ⟨s, hc, hw, hd, hb⟩

/-- A thread event that is not an atomic read-modify-write reads as it did before THREAD-ATOMIC:
its `MemReads` are its `Reads`. -/
theorem memReads_thread_iff_of_not_rmw {X : Execution} {e : EvId} {a : Acc}
    {bs : List (Option Byte)} (hn : ∀ pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) :
    X.MemReads (.thread e) a bs ↔ X.Reads e a bs :=
  ⟨fun h => h.elim id fun ⟨n, pc, h⟩ => absurd h (hn pc a bs n), Or.inl⟩

/-- A thread event that is not an atomic read-modify-write writes as it did before THREAD-ATOMIC:
its `MemWrites` are its `Writes`. -/
theorem memWrites_thread_iff_of_not_rmw {X : Execution} {e : EvId} {a : Acc} {bs : List Byte}
    (hn : ∀ pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) :
    X.MemWrites (.thread e) a bs ↔ X.Writes e a bs :=
  ⟨fun h => h.elim id fun ⟨o, pc, h⟩ => absurd h (hn pc a o (some bs)), Or.inl⟩

/-- The footprint of an asynchronous stage, fixed by its issuing instruction: an MMA operand
byte, a tile byte of a tensor load or store (a reduction's old-value read at the write's
footprint), the in-bounds global source byte of a tensor prefetch, the 16-byte CLC response at one
target CTA, a linear copy's source or destination range, or a linear prefetch's range. It exists
at issue, even when the stage is still pending. -/
def AsyncFootprint (i : EvId) : AsyncCopy.Part → Acc → Prop
  | .mmaRead isB index, a => a.size = 1 ∧ X.MmaFootprint i isB index a.loc
  | .read (.store x y k), a =>
    ∃ s addr, X.TensorStoreIssue i addr s ∧ TensorStore.readLoc s x y k = some a.loc ∧ a.size = 1
  | .write (.store x y k), a =>
    ∃ s addr, X.TensorStoreIssue i addr s ∧ TensorStore.writeLoc s x y k = some a.loc ∧ a.size = 1
  | .old (.store x y k), a =>
    ∃ s addr, X.TensorStoreIssue i addr s ∧ s.reduce.isSome ∧
      TensorStore.writeLoc s x y k = some a.loc ∧ a.size = 1
  | .read (.load x y k), a =>
    ∃ s addr, X.TensorIssue i addr s ∧ TensorCopy.readLoc s x y k = some a.loc ∧ a.size = 1
  | .write (.load x y k), a =>
    ∃ s addr, X.TensorIssue i addr s ∧ TensorCopy.writeLoc s x y k = some a.loc ∧ a.size = 1
  | .read (.prefetch x y k), a =>
    ∃ s addr, X.TensorPrefetchIssue i addr s ∧
      TensorTransfer.sourceLoc s.descriptor s.origin s.rows x y k = some a.loc ∧ a.size = 1
  | .write (.cta c), a =>
    ∃ s targets, X.ClcIssue i s targets ∧ c ∈ targets ∧
      a = { loc := { s.response with cta := c }, size := 16 }
  | .read .copy, a => (∃ s, X.Copy i s ∧ s.src = a) ∨ X.BulkPrefetch i a
  | .write .copy, a => ∃ s, X.Copy i s ∧ s.writes = .whole ∧ s.dst = a
  | .write (.elem j), a => ∃ s, X.Copy i s ∧ s.elems[j]? = some a
  | .old (.elem j), a => ∃ s r, X.Copy i s ∧ s.writes = .reduce r ∧ s.elems[j]? = some a
  | _, _ => False

/-- The footprint of the write stage of a whole linear operation is its destination, as before. -/
theorem asyncFootprint_write_copy_of_whole {X : Execution} {i : EvId} {s : AsyncCopy.Spec}
    {a : Acc} (hc : X.Copy i s) (hw : s.writes = .whole) :
    X.AsyncFootprint i (.write .copy) a ↔ s.dst = a := by
  constructor
  · rintro ⟨s', hc', -, hd⟩
    cases Copy.unique hc hc'
    exact hd
  · intro hd
    exact ⟨s, hc, hw, hd⟩

/-- Memory operations with their footprint and direction, pending or performed; an
asynchronous stage writes exactly when it is a write. -/
def Intent : AsyncCopy.Ref → Acc → Bool → Prop
  | .thread e, a, w => X.Access e a w
  | .async i p, a, w => w = p.writes ∧ X.AsyncFootprint i p a

def MemTouches (e : AsyncCopy.Ref) (a : Acc) : Prop :=
  (∃ w, X.Intent e a w) ∨ ∃ i bs, e = .thread i ∧ X.NcReads i a bs

/-- The stage has occurred, read from the storage of its issuing instruction's kind. -/
def AsyncPresent (i : EvId) : AsyncCopy.Part → Prop
  | .tcNotify rank => rank ∈ X.tcNotified i
  | .mmaRead isB index => ∃ l b, X.MmaRead i isB index l b
  | .read (.store x y k) => ∃ o, X.tensorStores i = some o ∧ (TensorStore.readByte o x y k).isSome
  | .write (.store x y k) => ∃ o, X.tensorStores i = some o ∧ (TensorStore.writeByte o x y k).isSome
  | .old (.store x y k) => ∃ o, X.tensorStores i = some o ∧ (TensorStore.oldByte o x y k).isSome
  | .readsDone => ∃ o, X.tensorStores i = some o ∧ o.effects.readsDone = true
  | .fullDone => ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true
  | .read (.load x y k) => ∃ o, X.tensor i = some o ∧ (TensorCopy.readByte o x y k).isSome
  | .write (.load x y k) => ∃ o slot value, X.tensor i = some o ∧
      TensorTransfer.slotAt o.spec.descriptor x y k = some slot ∧ o.effects.write slot = some value
  | .notify .load =>
    ∃ observation, X.tensor i = some observation ∧ observation.effects.notified = true
  | .resolve => (X.clc i).resolved.isSome
  | .write (.cta c) => c ∈ (X.clc i).written
  | .notify (.cta c) => c ∈ (X.clc i).notified
  | .read .copy => (X.async.copies i).readBytes.isSome
  | .write .copy => (X.async.copies i).writeBytes.isSome
  | .notify .copy => (X.async.copies i).notified
  | .write (.elem j) => ((X.async.copies i).elemWrites j).isSome
  | .old (.elem j) => ((X.async.copies i).elemOld j).isSome
  | .mmaDone => X.async.mmaDone i
  | .arriveOn => X.async.arrived i
  | _ => False

def RefPresent : AsyncCopy.Ref → Prop
  | .thread e => ∃ ev, X.get e = some ev
  | .async i p => X.AsyncPresent i p


end Execution

/-! ## PROG-CTA-WARP — CTAs, warps and lanes
Statement: Two threads are in the same CTA when their CTA indices agree. A warp is 32 consecutive
  threads of a CTA, and a warpgroup is four consecutive warps of a CTA whose first warp rank is a
  multiple of 4.

Defs: SameCta, SameWarp, SameWarpgroup, laneOf

Source:
- §10.1–§10.7 (thread and CTA ids)
- §2.2.1 (threads within a warp are sequentially numbered; a warp typically has 32 threads)
- §9.7.17.1 (warp-rank is the linear thread index divided by 32)
- §9.7.17.1: "A warpgroup is a set of four contiguous warps such that the warp-rank of the first
    warp is a multiple of 4."
- EXT-WARP

Direction: reading

### EXT-WARP — warps

Statement: The model takes a warp to be 32 consecutive threads of a CTA by linear thread index
  `%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x * %ntid.y`, the index §9.7.17.1 divides by 32 to
  obtain the warp rank (PROG-LAUNCH: thread `g` has linear thread index `g % block`). The PTX ISA
  numbers the threads of a warp sequentially and says a warp typically has 32 threads.

Evidence: PTX ISA §2.2.1 ("Threads within a warp are sequentially numbered. The warp size is a
  machine-dependent constant. Typically, a warp has 32 threads"), §4.5.1 (WARP_SZ is 32 for all
  target architectures to date), §9.7.17.1 ("warp-rank of a warp is defined as: (%tid.x + %tid.y *
  %ntid.x + %tid.z * %ntid.x * %ntid.y) / 32"). The static partition into consecutive groups is a
  reading of these sentences; the CUDA C++ Programming Guide (SIMT architecture) agrees.

Direction: reading

Effect: If it does not hold, the lanes the model groups into one warp collective (`shfl.sync`,
  `bar.warp.sync`, `elect.sync`, `tcgen05` warp instructions, `setmaxnreg`), the source lanes of
  shuffles, the uniformity checks, the warp counts of barriers and the values of `%laneid` and the
  lane masks (THREAD-SREG) refer to the wrong threads, and the values and synchronization the model
  derives from them are not the hardware's. Disclosed by every kernel whose statement names
  `Op.warp`, `Op.setMaxReg`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive`, `Op.bra (uni := true)`,
  `Op.tcAlloc`, `Op.tcDealloc`, `Op.tcRelinquish`, `Op.tcLd`, `Op.tcSt`, `Op.tcWaitLd`,
  `Op.tcWaitSt`, `SRegName.laneid`, `SRegName.lanemaskEq`, `SRegName.lanemaskLe`,
  `SRegName.lanemaskLt`, `SRegName.lanemaskGe` or `SRegName.lanemaskGt`: BlockSum, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm.
-/

/-- Threads `g` and `h` of the launch belong to the same CTA. -/
def SameCta (g h : Nat) : Prop := g < L.threads ∧ h < L.threads ∧ g / L.block = h / L.block

/-- Warps are 32 consecutive threads of a CTA (WARP reading: CUDA C++ Programming Guide,
SIMT Architecture). -/
def SameWarp (g h : Nat) : Prop := SameCta L g h ∧ g % L.block / 32 = h % L.block / 32

/-- A warpgroup is four contiguous warps whose first warp-rank is a multiple of 4 (§9.7.17.1). -/
def SameWarpgroup (g h : Nat) : Prop := SameCta L g h ∧ g % L.block / 32 / 4 = h % L.block / 32 / 4

/-- The lane of thread `g` within its warp. -/
def laneOf (g : Nat) : Nat := g % L.block % 32

/-! ## DEP-TC-COLLECTIVE — warp-collective tcgen05 instances
Statement: The `tcgen05` instructions that every lane of a warp executes together (allocation
  management, `ld`, `st` and the waits) are numbered within each thread, so the lanes of one
  collective instance share an ordinal.

Defs: isTcColl, Execution.TcK

Source:
- §9.7.18.7.1
- §9.7.18.8.3
- §9.7.18.8.5 (.sync.aligned: all threads of the warp execute the same instruction)

Direction: reading

Applies: Allocation management of either cta_group, tcgen05.ld, tcgen05.st and tcgen05.wait::{ld,st}

Premises: None.

Effect: Projection used by the warp-collective blocking, agreement and allocation rules.
-/

/-- The `tcgen05` instructions every lane of a warp executes together (`.sync.aligned`). -/
def isTcColl : Event → Bool
  | ⟨_, .tc (.resource ..)⟩ | ⟨_, .tc (.ld ..)⟩ | ⟨_, .tc .waitLd⟩
  | ⟨_, .tc (.st ..)⟩ | ⟨_, .tc .waitSt⟩ => true
  | _ => false

/-- `e` is its thread's `k`-th warp-collective `tcgen05` event (counting from 0). -/
def Execution.TcK (X : Execution) (e : EvId) (k : Nat) : Prop :=
  (∃ ev, X.get e = some ev ∧ isTcColl ev = true) ∧ ((X.tr e.1).take e.2).countP isTcColl = k

/-! ## CORRECT-GROW — the size and growth of an execution
Statement: The size of an execution counts the thread events (failed `try_wait`s excluded), the
  stages of asynchronous operations that have happened, and the allocator records and pairings. One
  execution extends another when it keeps all observations of the first: thread prefixes, read
  sources, asynchronous effects and object histories.

Defs: Event.counts, Execution.elemSize, Execution.elemSize_eq_zero, Execution.asyncSize,
  Execution.threadSize, Execution.pairSize, Execution.size,
  Execution.le

Source:
- none (definitions of the statement)

Direction: representation

Effect: The size is the number of thread events and independent async stages (including each tensor
  byte read/write, notification and output completion), plus allocator records and pairings of
  Tensor Memory operations. It does not count failed `try_wait`s. Extension preserves thread
  prefixes, actual read sources, async effects and object-history prefixes (`List.IsPrefix`:
  recorded operations, replies and phase identities are preserved), so no progress is obtained by
  rewriting an earlier observation. Together with `RfWf` at both endpoints, this also preserves any
  initial-byte choice already observed by a W0 read (`initial_choice_preserved`); unobserved choices
  are immaterial to the prefix and may be resolved by a later extension.
-/

namespace Execution

variable (X : Execution)

/-- Whether an event counts toward the size of an execution: a failed `try_wait` does
not, since a thread may poll any number of times. -/
def _root_.PTX.Event.counts : Event → Bool
  | ⟨_, .wait _ _ false _ _⟩ => false
  | _ => true

/-- The element stages of the linear operation issued by `i` that have occurred: its element
writes and its reduction elements' old-value reads. -/
def elemSize (i : EvId) : Nat :=
  match X.get i with
  | some ⟨_, .copy s⟩ =>
    (List.range s.elems.length).countP (fun j => ((X.async.copies i).elemWrites j).isSome) +
      (List.range s.elems.length).countP (fun j => ((X.async.copies i).elemOld j).isSome)
  | _ => 0

/-- Without recorded element stages, `elemSize` is zero. -/
theorem elemSize_eq_zero {X : Execution} {i : EvId}
    (h : ∀ j, (X.async.copies i).elemWrites j = none ∧ (X.async.copies i).elemOld j = none) :
    X.elemSize i = 0 := by
  unfold elemSize
  split <;> simp [h]

/-- Each independent stage contributes to progress once. -/
def asyncSize (i : EvId) : Nat :=
  (if (X.async.copies i).readBytes.isSome then 1 else 0) +
  (if (X.async.copies i).writeBytes.isSome then 1 else 0) +
  (if (X.async.copies i).notified then 1 else 0) +
  (if X.async.mmaStarted i then 1 else 0) +
  (if X.async.mmaDone i then 1 else 0) +
  (if X.async.arrived i then 1 else 0) +
  (if (X.clc i).resolved.isSome then 1 else 0) +
  (X.clc i).written.card + (X.clc i).notified.card +
  ((X.tensor i).map fun observation => observation.effects.size).getD 0 +
  ((X.tensorStores i).map fun observation => observation.effects.size).getD 0 +
  (X.tcNotified i).card + X.elemSize i

/-- Count thread events and independent asynchronous stages; failed polls do not count. -/
def threadSize (L : Launch) : Nat :=
  ((List.range L.threads).map fun g => (X.tr g).countP Event.counts +
    ((List.range (X.tr g).length).map fun i => X.asyncSize (g, i)).sum).sum

/-- Each allocator record and each pairing contributes one completion stage. -/
def pairSize (L : Launch) : Nat :=
  ((List.range L.grid).map fun cta => (X.tmemHistory cta).length).sum + X.tmemPairing.length

/-- The counted size of an execution: its thread events and asynchronous stages, plus its
Tensor Memory allocator records and pairings. Failed `try_wait` events do not count. -/
def size (L : Launch) : Nat := X.threadSize L + X.pairSize L

/-- Preserve all observations, including async reads, completion records and object history. -/
def le (X Y : Execution) : Prop :=
  (∀ g, X.tr g <+: Y.tr g) ∧
  (∀ e k, (∃ a bs, X.MemReads e a bs) → Y.rf e k = X.rf e k) ∧
  AsyncCopy.Extends X.async Y.async ∧
  (∀ m, List.IsPrefix (X.objects m) (Y.objects m)) ∧
  (∀ c, X.barriers c <+: Y.barriers c) ∧
  (∀ c, X.clusters c <+: Y.clusters c) ∧
  (∀ i, Clc.Extends (X.clc i) (Y.clc i)) ∧ Clc.StateExtends X.clcState Y.clcState ∧
  TensorCopy.SnapshotExtends X.tensor Y.tensor ∧
  TensorStore.SnapshotExtends X.tensorStores Y.tensorStores ∧
  ((∀ cta, X.tmemHistory cta <+: Y.tmemHistory cta) ∧ X.tmemPairing <+: Y.tmemPairing) ∧
  (∀ i pc group dst action, X.get i = some ⟨pc, .tc (.resource group dst action)⟩ →
    Y.tmemPairBlocks i = X.tmemPairBlocks i) ∧
  (∀ i, X.tcNotified i ⊆ Y.tcNotified i)

end Execution

end

end PTX
