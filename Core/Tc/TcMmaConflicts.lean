-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOrder

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## ERR-TMEM-RACE — Tensor Memory write conflicts
Statement: An execution is unsafe when two Tensor Memory writes of one cell (MMA results, stores,
  copies or shifts) are ordered in neither direction, or when an MMA's accumulator or A read, or a
  `tcgen05.shift`'s read, of a cell is ordered in neither direction with a write of that cell.
  Accumulator reads count also for masked output lanes, shift reads also when the moved words are
  never read, and the orders are observed completion and the pipelined pairs.

Defs: TcMma.WritesSafe, TcMma.WritesUnsafe, TcMma.RaceRead, TcMma.ReadsSafe, TcMma.readsSafe_iff,
  TcMma.ReadsUnsafe

Source:
- §9.7.18.6.2: "The asynchronous tcgen05 operations may execute and complete in a different order
    than they were issued."
- §9.7.18.6.2–4 (pipeline and explicit completion ordering)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

Direction: reading

Applies: Every unmasked MMA write, store, copy, shift write, enabled accumulator read, Tensor
  Memory A read and shift read, including masked lanes and results never loaded

Premises: Conflicts are equality of physical CTA, lane and column. A write is ordered before a read
  by `WriteBefore`, and a read before a write by `ReadBefore` of the read's kind: the reader's
  observed completion, the reading operation's own write, or a pipelined pair of §9.7.18.6.2 that
  starts at the read (C read→D write, A read→D write and A read→copy; the table has no pair that
  starts at a shift's read and ends at another operation's write). The registers of a `tcgen05.ld`
  are not in this check: ERR-TMEM-READ-SOURCE requires every write of the cell to be ordered with
  every load register.

Effect: WritesUnsafe and ReadsUnsafe enter Unsafe. The direction is `reading` because acceptance
  rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE,
  EXT-TC-EXEC-ORDER; every other path is stricter than the text.
-/

/-- Every two Tensor Memory writes of one cell are ordered. -/
def WritesSafe (L : Launch) (X : Execution) : Prop :=
  ∀ x y cell, TmemWrite L X x cell → TmemWrite L X y cell →
    x = y ∨ WriteBefore L X x y ∨ WriteBefore L X y x

/-- Two Tensor Memory writes of one cell are ordered in neither direction. -/
def WritesUnsafe (L : Launch) (X : Execution) : Prop := ¬ WritesSafe L X

/-- The Tensor Memory reads of kind `k` that the race check covers: the accumulator (C) and A reads
of an MMA and the reads of a `tcgen05.shift`, whether or not the values are used. The registers of
a `tcgen05.ld` are checked by ERR-TMEM-READ-SOURCE instead. -/
def RaceRead (X : Execution) : TmemRead → EvId → Cell → Prop
  | .ld, _, _ => False
  | .acc, e, cell => X.MmaReadCell e cell
  | .a, e, cell => X.MmaACell e cell
  | .shift, e, cell => ShiftReadCell X e cell

/-- Every read of the race check is ordered with every write of its cell. Potential C reads
conflict with D writes even when their own output lane is masked. Read/read pairs need no ordering;
an operation's own read/write dependency is intrinsic. -/
def ReadsSafe (L : Launch) (X : Execution) : Prop :=
  ∀ k reader writer cell, RaceRead X k reader cell → TmemWrite L X writer cell →
    reader = writer ∨ WriteBefore L X writer reader ∨ ReadBefore L X k reader writer

/-- `ReadsSafe` by read kind: the accumulator reads, the A reads and the shift reads. -/
theorem readsSafe_iff {L : Launch} {X : Execution} :
    ReadsSafe L X ↔
      (∀ reader writer cell, X.MmaReadCell reader cell → TmemWrite L X writer cell →
        reader = writer ∨ WriteBefore L X writer reader ∨ ReadBefore L X .acc reader writer) ∧
      (∀ reader writer cell, X.MmaACell reader cell → TmemWrite L X writer cell →
        reader = writer ∨ WriteBefore L X writer reader ∨ ReadBefore L X .a reader writer) ∧
      (∀ reader writer cell, ShiftReadCell X reader cell → TmemWrite L X writer cell →
        reader = writer ∨ WriteBefore L X writer reader ∨ ReadBefore L X .shift reader writer) := by
  constructor
  · intro h
    exact ⟨h .acc, h .a, h .shift⟩
  · rintro ⟨hc, ha, hs⟩ k
    cases k
    · intro _ _ _ h; exact h.elim
    · exact hc
    · exact ha
    · exact hs

/-- A read of the race check and a write of its cell are ordered in neither direction. -/
def ReadsUnsafe (L : Launch) (X : Execution) : Prop := ¬ ReadsSafe L X

end
end PTX.TcMma
