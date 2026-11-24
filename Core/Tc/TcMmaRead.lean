-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaValue

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TC-LOAD-VALUE — the values that Tensor Memory loads and A reads return
Statement: Each register of a `tcgen05.ld` returns the word that its read source
  (DEP-TC-READ-SOURCE) left in its cell. A 32-bit value fills the whole word, an FP16 result fixes
  only the low two bytes, and a byte of an A operand read from Tensor Memory is likewise the
  corresponding byte of the word its read source left.

Defs: TcMma.LoadCell, TcMma.WordContains, TcMma.LoadReadOk, TcMma.AReadOk, TcMma.ReadOk

Source:
- §9.7.18.2.3.1 (fragments of every shape)
- §9.7.18.10.4.1 (unpacked subword D)
- §9.7.18.6.4 (completion observation and handoff)
- §9.7.18.8.5 (wait::ld)
- DEP-TC-READ-SOURCE
- DEP-TC-MMA-VALUE

Direction: reading

Applies: Represented tcgen05.ld of every shape consuming dense MMA results, stored, copied or
  shifted words, and MMA A operands read from Tensor Memory

Premises: The actual load's register slot maps, by its recorded shape and address (`tcDataCell`), to
  the source cell in its own CTA. The source is a read source of the load (`ReadSource .ld`) or of
  the A read (`ReadSource .a`), and the value is the one it wrote (`Wrote`).

Effect: ReadOk is a Consistent field. Safety separately requires source existence
  (ERR-TMEM-READ-SOURCE), allocation coverage (ERR-TMEM-ACCESS-LIFETIME), instruction validity,
  resource lifetimes and conflict ordering. Completion of the load itself requires its own
  `tcgen05.wait::ld` before a later overwrite or release of the cell.
-/

/-- Register slot `j` of the load, by its recorded shape, in the loading CTA's local TMEM, using
the same address adapter as issue, StoreCell and StoreValue. -/
def LoadCell (L : Launch) (X : Execution) (load : EvId) (j : Nat) (cell : Cell) : Prop :=
  ∃ address vals shape, X.TLd load address vals shape ∧ j < vals.length ∧
    cell = tcDataCell L load.1 shape address j

/-- Subword D is not packed with the next matrix element. Unused upper bits are open. -/
def WordContains (value word : Value) : Prop :=
  (value.bytes = 4 ∧ word = value) ∨
  (value.bytes = 2 ∧ word.bytes = 4 ∧ ∀ k < 2, word.byteAt k = value.byteAt k)

/-- Each register of a load holds the value its read source wrote to its cell. -/
def LoadReadOk (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  ∀ load address vals shape j source cell value, X.TLd load address vals shape →
    LoadCell L X load j cell → ReadSource L X .ld source load cell →
    Wrote L A X source cell value →
    ∃ word, vals[j]? = some word ∧ WordContains value word

/-- The recorded A byte `index` of an MMA (cell `cell`, byte `pos` of its word) is the byte of
the word its read source wrote; bytes past a subword value are open. -/
def AReadOk (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  ∀ mma index cell pos source value operands,
    (∃ d s accum mask, X.MmaIssue mma d s accum mask ∧ aCell s index = some (cell, pos)) →
    ReadSource L X .a source mma cell → Wrote L A X source cell value →
    X.async.mmaOperands mma = some operands → pos < value.bytes →
    operands.a[index]? = some (some (value.byteAt pos))

/-- Loads and Tensor Memory A reads return the values of their sources. -/
def ReadOk (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  LoadReadOk L A X ∧ AReadOk L A X

/-! ## ERR-TMEM-READ-SOURCE — every Tensor Memory read has a source
Statement: Every register that a Tensor Memory load returns, every accumulator cell that a completed
  accumulating MMA may read, and every Tensor Memory A byte that a completed MMA reads has a read
  source as DEP-TC-READ-SOURCE defines it, with a value: a completed and stable write of a live
  allocation. An execution in which such a read sees uninitialized Tensor Memory, reads across an
  unprotected release or reads an overwritten value is unsafe.

Defs: TcMma.SourceRequired, TcMma.SourceSafe, TcMma.SourceUnsafe, TcMma.sourceSafe_iff

Source:
- §9.7.18.6.4 (completion)
- §9.7.18.6.3 (tcgen05 fences, DEP-TC-FENCE; standard synchronization also applies, EXT-TCACQUIRE)
- §9.7.18.7.1 (releases)
- DEP-TC-READ-SOURCE

Direction: stricter

Applies: Every register of every Tensor Memory load, and every accumulator and Tensor Memory A read
  of a completed MMA

Premises: Each such read has a read source (`ReadSource`) and a value written by it (`Wrote`). An
  accumulator read counts also for masked output lanes. The read of a `tcgen05.shift` needs no
  source of its own: the moved word has a value only with one (DEP-TMEM-SHIFT-VALUE), so a later
  load or MMA that reads the moved word without one fails this check.

Effect: Safety check (with the resource, lifetime, MMA instruction, conflict and commit checks, the
  Tensor Memory part of `Unsafe`). Writer order is ERR-TMEM-RACE; release at completion and
  access completion before release are ERR-TMEM-NOT-RELEASED and -ACCESS. Bulk copies and mbarriers
  instead use general object transitions, read-source constraints, proxy ordering and access-hazard
  checks, without a phase/count bound.
-/

/-- The Tensor Memory reads that must have a source: every register of a load, and the
accumulator and A reads of a completed MMA. -/
def SourceRequired (L : Launch) (X : Execution) : TmemRead → EvId → Cell → Prop
  | .ld, e, cell => ∃ j, LoadCell L X e j cell
  | .acc, e, cell => X.async.mmaDone e = true ∧ X.MmaReadCell e cell
  | .a, e, cell => X.async.mmaDone e = true ∧ X.MmaACell e cell
  | .shift, _, _ => False

/-- Every required Tensor Memory read has a read source with a value. -/
def SourceSafe (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  ∀ k e cell, SourceRequired L X k e cell →
    ∃ source value, ReadSource L X k source e cell ∧ Wrote L A X source cell value

/-- Some required Tensor Memory read has no source. -/
def SourceUnsafe (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  ¬ SourceSafe L A X

/-- The check by reader: the load registers (the former `TcSupported`), the accumulator reads
(the former `CompletedAccumulatorSources`) and the A reads (the former `CompletedASources`). -/
theorem sourceSafe_iff {L : Launch} {A : List Assumption} {X : Execution} :
    SourceSafe L A X ↔
      (∀ e j cell, LoadCell L X e j cell →
        ∃ source value, ReadSource L X .ld source e cell ∧ Wrote L A X source cell value) ∧
      (∀ i cell, X.async.mmaDone i = true → X.MmaReadCell i cell →
        ∃ source value, ReadSource L X .acc source i cell ∧ Wrote L A X source cell value) ∧
      (∀ i cell, X.async.mmaDone i = true → X.MmaACell i cell →
        ∃ source value, ReadSource L X .a source i cell ∧ Wrote L A X source cell value) := by
  constructor
  · intro h
    exact ⟨fun e j cell hc => h .ld e cell ⟨j, hc⟩,
      fun i cell hd hc => h .acc i cell ⟨hd, hc⟩, fun i cell hd hc => h .a i cell ⟨hd, hc⟩⟩
  · rintro ⟨hl, hc, ha⟩ k e cell hr
    cases k with
    | ld => obtain ⟨j, hj⟩ := hr; exact hl e j cell hj
    | acc => exact hc e cell hr.1 hr.2
    | a => exact ha e cell hr.1 hr.2
    | shift => exact hr.elim

end
end PTX.TcMma
