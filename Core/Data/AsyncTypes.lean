-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Value
public import Core.MBarrier.MBarrierHistory

@[expose] public section

namespace PTX

/-! ## THREAD-INSTANCE-ID — instruction instance identities
Statement: An executed instruction is named by its thread and its position in that thread's trace.
  The effects of an asynchronous operation have their own `Ref` identities and occupy no trace
  position.

Defs: EvId

Source:
- §8.9.1 (program order)

Direction: representation
-/
/-- The identity of an instruction instance: the thread's index in the grid and the position of the
instruction's event in that thread's trace. -/
abbrev EvId := Nat × Nat

namespace AsyncCopy
noncomputable section

/-! ## DEP-ASYNC-STAGES — independent effects of asynchronous operations
Statement: Each asynchronous operation (a bulk or tensor copy, a tensor store or reduction, a tensor
  prefetch, a cluster launch control request, an MMA or a commit) is split into independent stages
  such as a read of its source, a write of its destination, a completion notification or an operand
  read. A stage is named by the issuing instruction instance and the part, and an execution records
  the outcome of each stage separately from the thread traces.

Defs: AsyncCopy.Slot, AsyncCopy.Target, AsyncCopy.Part, AsyncCopy.Part.target,
  AsyncCopy.Part.writes, AsyncCopy.Ref, AsyncCopy.Completion, AsyncCopy.Reduction,
  AsyncCopy.WriteMode, AsyncCopy.Spec, AsyncCopy.Spec.elemWidth, AsyncCopy.Spec.elemOffsets,
  AsyncCopy.Spec.elems, AsyncCopy.Effects,
  AsyncCopy.MmaOperands,
  AsyncCopy.Snapshot, AsyncCopy.Snapshot.mmaStarted, AsyncCopy.present, AsyncCopy.nonempty,
  AsyncCopy.threadRefCoe, AsyncCopy.Ref.issuer

Source:
- §9.7.10.28.1 (asynchronous operations)
- §9.7.10.28 (bulk and tensor copies: read the source, write the destination, then signal
    completion)
- §9.7.10.28.3.1 (cp.async)
- §9.7.10.28.4.1 (cp.async.bulk)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.15.18 (clusterlaunchcontrol.try_cancel)
- §9.7.18.10.10.1
- §9.7.18.12.1 (tcgen05.mma, tcgen05.commit)

Direction: representation

Applies: The stages of linear copies (`cp.async` and `cp.async.bulk`), tensor copies, tensor stores
  and reductions, tensor and linear prefetch reads, CLC requests, MMAs, commits and the arrive-on of
  `cp.async.mbarrier.arrive`

Premises: The issuing instruction identifies the operation, its footprint and its mbarrier.

Effect: Independent asynchronous observations stored per kind in Execution. The part of a stage is a
  read, a write or a reduction's old-value read of one footprint slot, a notification to one target,
  a bulk store's read or full completion, a CLC resolution, a commit's arrive-on, the arrive-on of
  `cp.async.mbarrier.arrive`, an MMA operand byte read or the MMA completion. The slot depends on
  the kind of the issuing instruction: it is the whole linear range of a copy, one tile byte of a
  tensor load or store, one selected byte of a tensor prefetch, or the response at one target CTA of
  a CLC request. Stages occupy no positions in a thread trace. A linear operation (`Spec`: a copy, a
  linear reduction, `st.async` or `red.async`) names its source and destination footprints and its
  completion mechanism (`Completion`): the complete-tx on an mbarrier, the bulk async-group of the
  issuing thread, the non-bulk async-group of `cp.async`, which `cp.async.mbarrier.arrive` may also
  track, or none the thread can observe. The source of a `cp.async` may be shorter than its
  destination: the remaining destination bytes are zeros (DEP-LINEAR-COPY-EFFECTS). The source of
  `st.async` and `red.async` is the bytes of its register operands (`data`), with an empty `src`.
  The operation writes its destination as one write, or element by element (`WriteMode`): each byte
  whose mask bit is set for `.cp_mask`, each element of the type for a reduction, which also reads
  the element's old bytes. An element-wise operation has a stage `.write (.elem j)` per element and
  `.old (.elem j)` per reduction element, and its stage `.write .copy` has no footprint: it is
  present when every element has been written, which is the completion of the operation. The spec
  also records the proxy (`generic`) and the scope of a strong destination access (`scope`).

Review: Byte arrays record per-byte read outcomes. They are not an atomic memory snapshot. Their
  sources are recorded separately, and memory consistency decides which sources are permitted. A
  source need not be launch memory.
-/

/-- A slot of the footprint of an asynchronous memory stage, by issuing instruction. -/
inductive Slot where
  /-- The whole range of a linear bulk copy. -/
  | copy
  /-- One tile byte of a tensor load. -/
  | load (x y byte : Nat)
  /-- One tile byte of a tensor store or reduction. -/
  | store (x y byte : Nat)
  /-- The response of a CLC request at one target CTA. -/
  | cta (c : Nat)
  /-- One selected byte of a tensor prefetch. -/
  | prefetch (x y byte : Nat)
  /-- Element `j` of a linear operation that writes its destination element by element: a byte
  of a masked copy or an element of a linear reduction (`Spec.elems`). -/
  | elem (j : Nat)
  deriving DecidableEq, Repr

/-- The mbarrier complete-tx notification of an operation: a copy's, a tensor load's, or a
CLC response's at one target CTA. -/
inductive Target where
  | copy | load | cta (c : Nat)
  deriving DecidableEq, Repr

/-- One independent stage of an asynchronous operation: a read, a write or an old-value read of one
footprint slot, a notification to one target, a bulk store's read or full completion, a cluster
launch control resolution, a commit arrive-on, an MMA operand read or the MMA completion. -/
inductive Part where
  | read (s : Slot) | write (s : Slot)
  /-- A reduction's read of the old destination byte it reduces. -/
  | old (s : Slot)
  | notify (t : Target)
  /-- A bulk store's source reads have completed. -/
  | readsDone
  /-- A bulk store's writes have completed. -/
  | fullDone
  /-- A CLC request has been arbitrated. -/
  | resolve
  | tcNotify (rank : Fin 16)
  | mmaRead (isB : Bool) (byte : Nat) | mmaDone
  /-- The arrive-on of a `cp.async.mbarrier.arrive`. -/
  | arriveOn
  deriving DecidableEq, Repr

/-- The notification that signals the completion of a stage: the copy's, the tensor load's, or
the CLC response's at the CTA it writes. -/
def Part.target : Part → Option Target
  | .read .copy | .write .copy | .notify .copy | .write (.elem _) | .old (.elem _) => some .copy
  | .read (.load ..) | .write (.load ..) | .notify .load => some .load
  | .write (.cta c) | .notify (.cta c) => some (.cta c)
  | _ => none

/-- The stage writes memory. -/
def Part.writes : Part → Bool
  | .write _ => true
  | _ => false

/-- A reference to an operation that can be a source or a target of ordering: a thread's
instruction instance, or one stage (`Part`) of an asynchronous operation issued by one. -/
inductive Ref where
  | thread (event : EvId)
  | async (issuer : EvId) (part : Part)
  deriving DecidableEq, Repr

instance threadRefCoe : Coe EvId Ref := ⟨Ref.thread⟩

def Ref.issuer : Ref → EvId
  | .thread e | .async e _ => e

/-- The completion mechanism of a linear copy: the complete-tx on mbarrier `m`
(`.mbarrier::complete_tx::bytes`), the bulk async-group of the issuing thread (`.bulk_group`), or
the non-bulk async-group of `cp.async` (`cp.async.commit_group`, `cp.async.mbarrier.arrive`). -/
inductive Completion where
  | mbarrier (m : Loc)
  | bulkGroup
  | asyncGroup
  /-- No completion mechanism the issuing thread can observe (`st.async` and `red.async` with
  `.release`): the operation only has to be performed before the execution is complete. -/
  | unobserved
  deriving DecidableEq, Repr

/-- The element-wise reduction of a linear reduction (`cp.reduce.async.bulk`, `red.async`): the
operation and the element type. -/
structure Reduction where
  op : AtomOp
  type : DType
  deriving DecidableEq, Repr

/-- How a linear operation writes its destination: as one write (`whole`: copies and `st.async`),
byte by byte where bit `k % 16` of `mask` is set (`masked`: `.cp_mask`), or element by element with
an atomic read-modify-write each (`reduce`). -/
inductive WriteMode where
  | whole
  | masked (mask : Nat)
  | reduce (r : Reduction)
  deriving DecidableEq, Repr

/-- The footprints of a linear copy: the source, the destination and the completion mechanism.
The source of a `cp.async` may be shorter than its destination (`src-size`, `ignore-src`). -/
structure Spec where
  src : Acc
  dst : Acc
  completion : Completion
  /-- How the destination is written. -/
  writes : WriteMode := .whole
  /-- The bytes of a register source (`st.async`, `red.async`); `none`: the source is the memory
  range `src`. A register source has an empty `src`. -/
  data : Option (List Byte) := none
  /-- The operation is performed in the generic proxy (`cp.async`, `st.async`, `red.async`); every
  other linear operation uses the async proxy. -/
  generic : Bool := false
  /-- The scope of a strong destination access (`.relaxed` or `.release` element reductions and
  `st.async.release`); `none`: weak. -/
  scope : Option MbarScope := none
  deriving DecidableEq

/-- The byte size of one destination element: the element type of a reduction, one byte
otherwise. -/
def Spec.elemWidth (s : Spec) : Nat :=
  match s.writes with
  | .reduce r => r.type.width / 8
  | _ => 1

/-- The destination offsets of the elements of an element-wise operation: the bytes whose mask bit
is set for a masked copy, every element for a reduction, none for a whole write. -/
def Spec.elemOffsets (s : Spec) : List Nat :=
  match s.writes with
  | .whole => []
  | .masked m => (List.range s.dst.size).filter fun k => m.testBit (k % 16)
  | .reduce r => (List.range (s.dst.size / (r.type.width / 8))).map (· * (r.type.width / 8))

/-- The destination footprints of the elements (`Slot.elem`). -/
def Spec.elems (s : Spec) : List Acc :=
  s.elemOffsets.map fun k => { s.dst with loc := s.dst.loc.at k, size := s.elemWidth }

/-- The recorded outcome of the stages of one linear copy: the bytes its read returned, the bytes
its write stored, and whether its mbarrier completion notification arrived. -/
structure Effects where
  readBytes : Option (List Byte) := none
  writeBytes : Option (List Byte) := none
  notified : Bool := false
  /-- The bytes written by each element of an element-wise operation. -/
  elemWrites : Nat → Option (List Byte) := fun _ => none
  /-- The old bytes read by each element of a reduction. -/
  elemOld : Nat → Option (List Byte) := fun _ => none

/-- Values returned by independent MMA operand reads. They are absent at issue. -/
structure MmaOperands where
  a : List (Option Byte)
  b : List (Option Byte)

/-- The independent asynchronous observations of an execution, keyed by the issuing instruction:
linear copy effects, the operand bytes that MMAs read, the MMA completions, and the arrive-on
operations of `cp.async.mbarrier.arrive`. -/
structure Snapshot where
  copies : EvId → Effects := fun _ => {}
  /-- Actual MMA operand reads, recorded independently of the issuing source event. -/
  mmaOperands : EvId → Option MmaOperands := fun _ => none
  /-- The MMA's Tensor Memory writes have completed. -/
  mmaDone : EvId → Bool := fun _ => false
  /-- The arrive-on of a `cp.async.mbarrier.arrive` has been performed. -/
  arrived : EvId → Bool := fun _ => false

/-- Operand execution has started exactly when its read outcomes have been recorded. -/
def Snapshot.mmaStarted (X : Snapshot) (i : EvId) : Bool := (X.mmaOperands i).isSome

def present (e : Effects) : Part → Prop
  | .read .copy => e.readBytes.isSome
  | .write .copy => e.writeBytes.isSome
  | .notify .copy => e.notified
  | .write (.elem j) => (e.elemWrites j).isSome
  | .old (.elem j) => (e.elemOld j).isSome
  | _ => False

def nonempty (e : Effects) : Prop := ∃ p, present e p


end
end AsyncCopy
end PTX
