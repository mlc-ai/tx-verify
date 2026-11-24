-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.AsyncTypes

@[expose] public section

namespace PTX.AsyncCopy
noncomputable section

/-! ## DEP-LINEAR-COPY-EFFECTS — effects and completion of a linear copy
Statement: A linear copy writes the bytes it read, followed by zeros up to the size of its
  destination when its source is shorter (only a `cp.async` with `src-size` or `ignore-src`), and
  `st.async` writes the bytes of its register operands. A masked copy writes each byte whose mask
  bit is set with its source byte, and a reduction writes each element together with a read of its
  old value. Only an operation completed through an mbarrier has a completion notification; it
  requires the whole write, and it adds the destination byte count to that mbarrier, once.

Defs: AsyncCopy.zeroByte, AsyncCopy.sourceBytes, AsyncCopy.ElemsOk, AsyncCopy.CopyOk,
  AsyncCopy.WellFormed, AsyncCopy.Notification, AsyncCopy.copyOk_iff_of_size_eq

Source:
- §9.7.10.28.4.1 (copying size bytes): "The complete-tx operation, with completeCount argument equal
    to amount of data copied in bytes, will be performed on the mbarrier object specified by the
    operand mbar ."
- §9.7.10.28.4.1: "The i-th bit in the 16-bit wide byteMask operand specifies whether the i-th byte
    of each 16-byte wide chunk of source data is copied to the destination. If the bit is set, the
    byte is copied."
- §9.7.10.28.3.1: "Operand src-size represents the size of the data in bytes to be copied from src
    to dst and must be less than or equal to cp-size . In such case, remaining bytes in destination
    dst are filled with zeros."
- §9.7.10.28.3.1: "If the source data is ignored then zeros will be copied to destination dst ."
- §9.7.10.28.4.2: "Each data element in the destination array is reduced inline with the
    corresponding data element in the source array with the reduction operation specified by the
    modifier .redOp ."
- §9.7.10.12 (st.async): "initiates an asynchronous store operation that stores the value specified
    by source operand b to the destination memory location specified by operand a"
- §9.7.10.12 (st.async): "upon completion of the asynchronous operation, a complete-tx operation
    will be performed on the mbarrier object specified by the operand mbar , with completeCount
    argument equal to the amount of data stored in bytes."
- §9.7.15.7 (red.async)
- §9.7.10.28.1 (asynchronous execution)

Direction: reading

Applies: Linear operations (`cp.async`, `cp.async.bulk`, `cp.reduce.async.bulk`, `st.async`,
  `red.async`), with source values left open

Premises: A copy effect is present for an issued instruction instance.

Effect: Per-operation validity; the stage order of the copy is `StageOrder` (DEP-ASYNC-STAGE-ORDER).
  A write may be present while its completion notification is still absent. Effects of distinct
  copies may be observed in any relative order. A completed copy contributes exactly its own byte
  count to exactly its own mbarrier, once. The notification has release.cluster semantics, applied
  by the object/visibility rules; the issuer's earlier generic accesses are not added to these
  edges. A copy completed through an async-group has no notification; its completion is the presence
  of its write (DEP-BULK-WAIT). The zero bytes of a `cp.async` are the bytes of a zero 8-bit value
  (`zeroByte`). An element-wise operation (`.cp_mask` copy or reduction) records each element's
  write, and each reduction element's old-value read, separately (`ElemsOk`); its `.write .copy`
  stage is present only when every element has been written, and it then records no bytes. The
  value a reduction element writes is DEP-REDUCTION-VALUES's (`CopyReduceValues`). A register source
  has no read stage.
-/

/-- The byte a `cp.async` writes where its source is ignored or shorter than `cp-size`: a zero
byte. -/
def zeroByte : Byte := (Value.bits 8 0).byteAt 0

/-- The bytes the operation `s` writes from, once they are known: its register bytes, or the bytes
its read returned followed by zero bytes up to the destination's size. -/
def sourceBytes (s : Spec) (e : Effects) : Option (List Byte) :=
  match s.data with
  | some d => some d
  | none => e.readBytes.map fun rs => rs ++ List.replicate (s.dst.size - s.src.size) zeroByte

/-- The element effects `e` of the operation `s` are valid: an element write belongs to an
element, has the element's size and needs the source bytes; a masked byte is its source byte; a
reduction element writes together with its old-value read, and only a reduction element reads an
old value. -/
def ElemsOk (s : Spec) (e : Effects) : Prop :=
  (∀ j bs, e.elemWrites j = some bs → j < s.elems.length ∧ bs.length = s.elemWidth ∧
    (∃ src, sourceBytes s e = some src ∧
      ∀ m, s.writes = .masked m → ∃ k, s.elemOffsets[j]? = some k ∧ bs = (src.drop k).take 1) ∧
    ∀ r, s.writes = .reduce r → ∃ old, e.elemOld j = some old) ∧
  ∀ j bs, e.elemOld j = some bs → (∃ r, s.writes = .reduce r) ∧ bs.length = s.elemWidth ∧
    (e.elemWrites j).isSome

/-- The effects `e` of the linear operation `s` are valid: the source is at most as large as the
destination, only a memory source is read and the bytes read have its size, a whole write writes
the source bytes (`sourceBytes`), the write stage of an element-wise operation is present only after
every element is written and records no bytes, a completion notification belongs to an mbarrier
completion and implies that the write stage is present, and the element effects are valid. -/
def CopyOk (s : Spec) (e : Effects) : Prop :=
  s.src.size ≤ s.dst.size ∧
  (∀ bs, e.readBytes = some bs → s.data = none ∧ bs.length = s.src.size) ∧
  (∀ bs, e.writeBytes = some bs → match s.writes with
    | .whole => sourceBytes s e = some bs
    | _ => (∀ j < s.elems.length, (e.elemWrites j).isSome) ∧ bs = []) ∧
  (e.notified = true → (∃ m, s.completion = .mbarrier m) ∧ ∃ bs, e.writeBytes = some bs) ∧
  ElemsOk s e

/-- For a whole copy from memory whose source and destination have the same size and that
completes through an mbarrier (every `cp.async.bulk` copy of the earlier forms), `CopyOk` is the
earlier condition with the element condition added: equal sizes, read bytes of that size, written
bytes equal to the bytes read, and a notification only after the write. -/
theorem copyOk_iff_of_size_eq {s : Spec} {e : Effects} {m : Loc}
    (hs : s.src.size = s.dst.size) (hm : s.completion = .mbarrier m) (hw : s.writes = .whole)
    (hd : s.data = none) :
    CopyOk s e ↔ (s.src.size = s.dst.size ∧
      (∀ bs, e.readBytes = some bs → bs.length = s.src.size) ∧
      (∀ bs, e.writeBytes = some bs → e.readBytes = some bs) ∧
      (e.notified = true → ∃ bs, e.writeBytes = some bs)) ∧ ElemsOk s e := by
  simp only [CopyOk, sourceBytes, hs, hw, hd, Nat.sub_self, List.replicate_zero, List.append_nil,
    le_refl, true_and, hm, Completion.mbarrier.injEq, exists_eq', Option.map_eq_some_iff,
    exists_eq_right, and_assoc]

/-- `issued` is derived from instruction events, rather than freely chosen by a kernel
proof. Every nonempty record must belong to such an instruction instance. -/
def WellFormed (issued : EvId → Option Spec) (X : Snapshot) : Prop :=
  ∀ i, nonempty (X.copies i) → ∃ s, issued i = some s ∧ CopyOk s (X.copies i)

/-- One actual completion notification; issue or destination write alone do not signal. -/
def Notification (issued : EvId → Option Spec) (X : Snapshot) (i : EvId)
    (m : Loc) (bytes : Nat) : Prop :=
  ∃ s, issued i = some s ∧ (X.copies i).notified = true ∧ s.completion = .mbarrier m ∧
    bytes = s.dst.size

/-! ## CORRECT-ASYNC-GROW — extension preserves asynchronous observations
Statement: When an execution grows, every read, write and completion notification of an
  asynchronous copy, every element write and old-value read of an element-wise operation, every
  operand record and completion of an MMA, and every arrive-on of a `cp.async.mbarrier.arrive`, that
  is already present stays present with the same value.

Defs: AsyncCopy.Extends

Source:
- none (representation of execution growth)

Direction: representation

Applies: Two finite-prefix observations of the same asynchronous operations

Premises: Read/write effects or notifications already occurred.

Effect: Extension relation; new effects may occur independently of thread-trace extension.
  `Execution.le` preserves reads-from choices separately.
-/

/-- The snapshot `Y` extends `X`: every copy read, write and notification, every MMA operand
record and completion, and every `cp.async.mbarrier.arrive` arrive-on present in `X` is present
with the same value in `Y`. -/
def Extends (X Y : Snapshot) : Prop :=
  (∀ i bs, (X.copies i).readBytes = some bs → (Y.copies i).readBytes = some bs) ∧
  (∀ i bs, (X.copies i).writeBytes = some bs → (Y.copies i).writeBytes = some bs) ∧
  (∀ i, (X.copies i).notified = true → (Y.copies i).notified = true) ∧
  (∀ i operands, X.mmaOperands i = some operands → Y.mmaOperands i = some operands) ∧
  (∀ i, X.mmaDone i = true → Y.mmaDone i = true) ∧
  (∀ i, X.arrived i = true → Y.arrived i = true) ∧
  (∀ i j bs, (X.copies i).elemWrites j = some bs → (Y.copies i).elemWrites j = some bs) ∧
  (∀ i j bs, (X.copies i).elemOld j = some bs → (Y.copies i).elemOld j = some bs)

end
end PTX.AsyncCopy
