-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access
public import Core.Data.Events

@[expose] public section

namespace PTX.TensorStore
noncomputable section

/-! ## DEP-REDUCTION-VALUES — reduced values of tensor reduction elements
Statement: A tensor or linear reduction writes `op(old, src)` for each performed element, where
  `old` is the destination element it read and `src` the source element, and an element for which
  no integer rule or floating-point assumption gives a value makes the execution unsafe. Each
  element is one atomic read-modify-write of MEM-ATOMICITY.

Defs: TensorDescriptor.Format.dtype, TensorStore.reduceValue, TensorStore.elementBytes,
  TensorStore.Reduced, TensorStore.ReduceReads, TensorStore.ReduceValues, TensorStore.ReduceNoRule,
  TensorStore.ReduceUnique, TensorStore.ReduceAcyclic, TensorStore.copyReduceValue,
  TensorStore.CopyReduceValues, TensorStore.CopyReduceNoRule, TensorStore.copyReduceValues_of_none,
  TensorStore.not_copyReduceNoRule_of_none, TensorStore.ReduceOk

Source:
- §9.7.10.28.5.4: "Each element of the tensor data in the .dst state space is reduced inline with
    the corresponding element from the tensor data in the .src state space."
- §9.7.10.28.5.4: "The following table describes the valid combinations of .redOp and element type:
    .redOp Element type .add .u32 , .s32 , .u64 , .f32 , .f16 , .bf16 .min , .max .u32 , .s32 , .u64
    , .s64 , .f16 , .bf16 .inc , .dec .u32 .and , .or , .xor .b32 , .b64"
- §9.7.10.28.5.4: "Each reduction operation performed by cp.reduce.async.bulk.tensor has
    individually .relaxed.gpu memory ordering semantics and are element-wise atomic."
- §9.7.10.28.4.2: "Each data element in the destination array is reduced inline with the
    corresponding data element in the source array with the reduction operation specified by the
    modifier .redOp ."
- §9.7.10.28.4.2: "The .inc and .dec operations return a result in the range [0..x] where x is the
    value at the source state space."
- §9.7.15.7: "red.async is a non-blocking instruction which initiates an asynchronous reduction
    operation specified by .op , with the operand b and the value at the destination memory location
    specified by operand a ."
- THREAD-ATOMIC-OP
- EXT-TMA-REDUCE-OP
- EXT-TMA-REDUCE-ATOMIC
- MEM-ATOMICITY

Direction: reading

Applies: Every performed element of a `cp.reduce.async.bulk.tensor` reduction, and of a linear
  reduction (`cp.reduce.async.bulk`, `red.async`)

Premises: The element's global bytes were written together, each with its shared source byte and its
  old destination byte (DEP-TENSOR-STORE-EFFECTS), or the linear element was written with its old
  bytes (DEP-LINEAR-COPY-EFFECTS); each old byte is a read with a reads-from source under
  MEM-READS-FROM and MEM-READ-AXIOMS.

Effect: Execution constraint in Consistent.reduce; atomicity is Consistent.atomic (MEM-ATOMICITY).
  The element value is the value of THREAD-ATOMIC-OP for the element's operation and type
  (`Format.dtype`): integer operations read the bit patterns of the old and source elements and are
  exact at the element width, with the operations of EXT-TMA-REDUCE-OP, and floating-point
  operations take their value from an assumption's `rmwRule` (ASM-INTERFACE, ASM-IDEAL). An element
  has no arithmetic rule when no floating-point rule gives a value or when its old or source bytes
  are not a value of the element type, and the reduction is then unsafe (`ReduceNoRule`,
  ERR-REDUCTION-NO-RULE). A reduction element is one read-modify-write. Its read of old byte `k`
  is the asynchronous read `.old (.store x y k)` at the footprint of the write
  `.write (.store x y k)` (MEM-FOOTPRINT), so the old value has a reads-from source like any
  read, and visibility, completion and the axioms apply to it as to the write; like the writes,
  the reads precede the reduction's full completion (DEP-ASYNC-STAGE-ORDER). The element footprint
  is that of ERR-DATA-RACE (`OpFootprint`): its first global byte and the element size. The
  reductions of one element are atomic with respect to each other by MEM-ATOMICITY (`RmwId.tensor`):
  `ReduceUnique` and `ReduceAcyclic` state its two conclusions for them, and
  `Consistent.reduceUnique` and `Consistent.reduceAcyclic` derive them. An element `j` of a linear
  reduction (`cp.reduce.async.bulk`, `red.async`) is the element of the reduction's type at
  destination offset `j` times its size. Its source element is the bytes at the same offset of the
  bytes read from `srcMem` (`cp.reduce.async.bulk`) or of the register operand (`red.async`), and
  its value is THREAD-ATOMIC-OP's for the reduction's operation and type on the rebuilt old and
  source elements (`copyReduceValue`): the `atom` operations of the same name, as EXT-TMA-REDUCE-OP
  reads them for tensor reductions (§9.7.10.28.4.2 names the operations without restating them; its
  sentence on `.inc` and `.dec` is the `atom` formula's range). A floating operation takes its value
  from an assumption's `rmwRule`, and an element without a value is unsafe (`CopyReduceNoRule`,
  ERR-REDUCTION-NO-RULE). The element is one atomic operation of MEM-ATOMICITY (`RmwId.copy`).

Review: A pending element can always be performed by a consistent extension once its old bytes
  have sources that the ordinary read rules allow and that no performed reduction of the element
  already read (`consistent_storeReduce`,
  Lemmas/TensorStore/TensorStoreCompleteConsistentReduce.lean).

### EXT-TMA-REDUCE-OP — the operations of a tensor reduction

Statement: The operations of a tensor reduction are those of the `atom` instruction of the same
  name, with the destination element as the memory operand `r` and the source element as `s`: inc
  and dec are `(r >= s) ? 0 : r+1` and `(r==0 || r > s) ? s : r-1`, integer add is modulo `2^w` at
  the element width, min and max compare as signed integers for `.s32`/`.s64` maps and as unsigned
  ones for the other integer maps, and `.and`/`.or`/`.xor` (`.b32`/`.b64`) are bitwise.

Why it is not spec text: §9.7.10.28.5.4 names each `.redOp` and its element types but does not
  restate the operations. The model reads them as the `atom` operations of the same name
  (§9.7.15.5, THREAD-ATOMIC-OP).

Evidence: The B200 probe of EXT-TMA-REDUCE observed `old ⊕ src` with these operations for every
  integer operation on u32 and s32 maps, including wrap-around. Floating values follow the
  model's convention for floating arithmetic: the Core has no default rule, and an explicit
  assumption supplies one (`Assumption.rmwRule`, ASM-IDEAL). Where no rule gives a value the
  element is a `noRule` fault (ERR-FAULT-REASON), the convention of every instruction and of MMA
  (ERR-TC-MMA).

Direction: reading

Effect: The element values of a tensor reduction are those of these operations; if the hardware
  operations differ, the proven results differ. Disclosed by every kernel whose statement names
  `Op.cpTensorStore (reduce ≠ none)`: none.

### EXT-TMA-REDUCE-ATOMIC — a tensor reduction element is one atomic operation

Statement: Each element reduction of `cp.reduce.async.bulk.tensor` is one atomic read-modify-write
  of §8.10.3 at the element footprint, whose read and write are the old-value reads and the writes
  of the element's bytes, and its scope is `.gpu`.

Why it is not spec text: §9.7.10.28.5.4 calls the reductions "element-wise atomic" with
  ".relaxed.gpu memory ordering semantics" and does not name the operations that make up an
  element. The model reads an element as one atomic operation of MEM-ATOMICITY (`RmwId.tensor`): its
  read of the old value of byte `k` is `.old (.store x y k)`, its write of byte `k` is
  `.write (.store x y k)`, and its footprint is the element.

Direction: reading

Effect: Two reductions of one element are then morally strong (ERR-DATA-RACE: strong, `.gpu` scope,
  async proxy, complete overlap), so MEM-ATOMICITY gives that no two of them read a byte from the
  same write and that reads-from among them has no cycle (`ReduceUnique`, `ReduceAcyclic`). These
  make the reductions of one element a single reads-from chain per byte, the same chain for every
  byte of the element (two different chains would contain a cycle), and CORRECT-FINAL orders their
  writes by it (`CoStep`), so the final element is the result of the last reduction. Executions in
  which two reductions of one element read a byte from the same write, or read from each other
  cyclically, are removed from `Consistent`. If an element were not one atomic operation on
  hardware (for example if its bytes were reduced separately), such executions may occur.
  Disclosed by every kernel whose statement names `Op.cpTensorStore (reduce ≠ none)`: none.
-/

/-- The instruction type of a tensor map's element format: `.u` and `.s` integers and floating
types of the same width. -/
def _root_.PTX.TensorDescriptor.Format.dtype : TensorDescriptor.Format → DType
  | .u8 => .int .u 8
  | .u16 => .int .u 16
  | .u32 => .int .u 32
  | .s32 => .int .s 32
  | .u64 => .int .u 64
  | .s64 => .int .s 64
  | .f16 => .float .f16
  | .bf16 => .float .bf16
  | .f32 => .float .f32
  | .f64 => .float .f64

/-- The reduced element from the old destination bytes and the source bytes: the value of
THREAD-ATOMIC-OP for the element's operation and type. -/
def reduceValue (A : List Assumption) (op : AtomOp) (fmt : TensorDescriptor.Format)
    (old src : List (Option Byte)) : Exec Value := do
  let a ← rebuild 3 old
  let b ← rebuild 3 src
  rmwValue A op fmt.dtype a [b]

/-- The bytes of element `(x, y)` in one of an observation's byte views. -/
def elementBytes (view : Observation → Nat → Nat → Nat → Option Byte) (o : Observation)
    (x y : Nat) : List (Option Byte) :=
  (List.range o.spec.descriptor.format.bytes).map (view o x y)

/-- Element `(x, y)` of the reduction issued by `i` has been performed; `fp` is its footprint. -/
def Reduced (X : Execution) (i : EvId) (x y : Nat) (fp : Acc) : Prop :=
  ∃ o red loc, X.tensorStores i = some o ∧ o.spec.reduce = some red ∧
    writeLoc o.spec x y 0 = some loc ∧ fp = { loc := loc, size := o.spec.descriptor.format.bytes } ∧
    (writeByte o x y 0).isSome

/-- Reduction element `q` read a byte of its old value from reduction element `p`, both
performed at footprint `fp`. Elements are `(issue, x, y)`. -/
def ReduceReads (X : Execution) (fp : Acc) (p q : EvId × Nat × Nat) : Prop :=
  Reduced X p.1 p.2.1 p.2.2 fp ∧ Reduced X q.1 q.2.1 q.2.2 fp ∧
    ∃ k k', k < fp.size ∧ X.rf (.async q.1 (.old (.store q.2.1 q.2.2 k))) 0 =
      some (.async p.1 (.write (.store p.2.1 p.2.2 k')))

/-- The value written by each performed reduction element is the result of `reduceValue` on its old
and source bytes, when that gives a value. -/
def ReduceValues (A : List Assumption) (X : Execution) : Prop :=
  ∀ i o red x y v, X.tensorStores i = some o → o.spec.reduce = some red →
    (writeByte o x y 0).isSome →
    reduceValue A red o.spec.descriptor.format (elementBytes oldByte o x y)
      (elementBytes readByte o x y) = .ok v →
    ∀ k < o.spec.descriptor.format.bytes, writeByte o x y k = some (v.byteAt k)

/-- A performed reduction element has no arithmetic rule: `reduceValue` gives no value. -/
def ReduceNoRule (A : List Assumption) (X : Execution) : Prop :=
  ∃ i o red x y, X.tensorStores i = some o ∧ o.spec.reduce = some red ∧
    (writeByte o x y 0).isSome ∧
    ∀ v, reduceValue A red o.spec.descriptor.format (elementBytes oldByte o x y)
      (elementBytes readByte o x y) ≠ .ok v

/-- Two performed reduction elements at one footprint never read the same byte of their old values
from the same write. A consequence of MEM-ATOMICITY (`Consistent.reduceUnique`). -/
def ReduceUnique (X : Execution) : Prop :=
  ∀ fp (p q : EvId × Nat × Nat) k, Reduced X p.1 p.2.1 p.2.2 fp → Reduced X q.1 q.2.1 q.2.2 fp →
    p ≠ q → k < fp.size →
    X.rf (.async p.1 (.old (.store p.2.1 p.2.2 k))) 0 ≠
      X.rf (.async q.1 (.old (.store q.2.1 q.2.2 k))) 0

/-- Reads among the performed reduction elements of one footprint have no cycle. A consequence of
MEM-ATOMICITY (`Consistent.reduceAcyclic`). -/
def ReduceAcyclic (X : Execution) : Prop :=
  ∀ fp p, ¬ Relation.TransGen (ReduceReads X fp) p p

/-- The value of element `j` of the linear reduction `s` (`cp.reduce.async.bulk`, `red.async`) with
effects `e`, once its source bytes and its old bytes are known: the value of THREAD-ATOMIC-OP for
the reduction's operation and type on the old element and the source element. -/
def copyReduceValue (A : List Assumption) (s : AsyncCopy.Spec) (r : AsyncCopy.Reduction)
    (e : AsyncCopy.Effects) (j : Nat) : Option (Exec Value) := do
  let src ← AsyncCopy.sourceBytes s e
  let k ← s.elemOffsets[j]?
  let old ← e.elemOld j
  pure do
    let a ← rebuild 3 (old.map some)
    let b ← rebuild 3 (((src.drop k).take s.elemWidth).map some)
    rmwValue A r.op r.type a [b]

/-- Each performed element of a linear reduction writes the bytes of `copyReduceValue`, when that
gives a value. -/
def CopyReduceValues (A : List Assumption) (X : Execution) : Prop :=
  ∀ i s r j v, X.Copy i s → s.writes = .reduce r → ((X.async.copies i).elemWrites j).isSome →
    copyReduceValue A s r (X.async.copies i) j = some (.ok v) →
    (X.async.copies i).elemWrites j = some ((List.range s.elemWidth).map v.byteAt)

/-- A performed element of a linear reduction has no arithmetic rule: `copyReduceValue` gives no
value. -/
def CopyReduceNoRule (A : List Assumption) (X : Execution) : Prop :=
  ∃ i s r j, X.Copy i s ∧ s.writes = .reduce r ∧ ((X.async.copies i).elemWrites j).isSome ∧
    ∀ v, copyReduceValue A s r (X.async.copies i) j ≠ some (.ok v)

/-- Without linear reductions (every execution of the forms before them), the linear part of the
reduction rule holds. -/
theorem copyReduceValues_of_none {A : List Assumption} {X : Execution}
    (h : ∀ i s, X.Copy i s → ∀ r, s.writes ≠ .reduce r) : CopyReduceValues A X :=
  fun i s r _ _ hc hr => absurd hr (h i s hc r)

/-- Without linear reductions, no linear reduction element lacks a rule. -/
theorem not_copyReduceNoRule_of_none {A : List Assumption} {X : Execution}
    (h : ∀ i s, X.Copy i s → ∀ r, s.writes ≠ .reduce r) : ¬ CopyReduceNoRule A X :=
  fun ⟨i, s, r, _, hc, hr, _⟩ => h i s hc r hr

/-- The reductions of the execution `X`, tensor and linear, write the reduced values. Their
atomicity is MEM-ATOMICITY. -/
structure ReduceOk (A : List Assumption) (X : Execution) : Prop where
  values : ReduceValues A X
  copies : CopyReduceValues A X

end
end PTX.TensorStore
