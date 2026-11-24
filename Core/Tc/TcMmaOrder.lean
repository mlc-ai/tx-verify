-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TmemStore

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TC-READ-SOURCE — Tensor Memory write order and read sources
Statement: A Tensor Memory write is ordered before a later access when its completion has been
  observed before the access, or when the two form a pipelined pair (DEP-TC-PIPELINE). A Tensor
  Memory read (a register of a `tcgen05.ld`, an accumulator or A read of an MMA, or a read of a
  `tcgen05.shift`) takes its word from a source: a write of the cell ordered before the reading
  operation, such that every other write of the cell comes before the source or after the read has
  happened, and no release of the cell's allocation separates source and read.

Defs: TcMma.Before, TcMma.TmemWrite, TcMma.WriteBefore, TcMma.SourceLive, TcMma.TmemRead,
  TcMma.ReadBefore, TcMma.ReadSource, TcMma.readSource_ld, TcMma.readSource_acc,
  TcMma.readSource_a, TcMma.readSource_shift

Source:
- §9.7.18.6.2: "The asynchronous tcgen05 operations may execute and complete in a different order
    than they were issued."
- §9.7.18.6.2.1.1: "Completion of the following instruction’s asynchronous operations is observed
    through the mbarrier based waiting mechanism: tcgen05.mma tcgen05.cp tcgen05.shift"
- §9.7.18.6.2.1.2: "Completion of the following instruction’s asynchronous operations is observed
    through tcgen05.wait based waiting mechanism: tcgen05.ld tcgen05.st"
- §9.7.18.6.4 (inter-thread synchronization; 4.1 and 4.3 are pipelines)
- §9.7.18.7.1 (allocation lifetime)
- DEP-TC-PIPELINE
- DEP-TC-COMPLETION
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

Direction: reading

Applies: Every represented MMA, `tcgen05.cp`, `tcgen05.st` and `tcgen05.shift` write, and every
  register of a `tcgen05.ld`, accumulator and Tensor Memory A read of an MMA and read of a
  `tcgen05.shift`

Premises: A write is ordered before an event by its completion mechanism (an observed commit for an
  MMA or copy, a `tcgen05.wait::st` for a store) or by a pipelined pair. A read has happened before
  a write `w` by the reader's completion mechanism (a `tcgen05.wait::ld` for a load, an observed
  commit for an MMA or shift), when `w` is a write of the reading operation itself, or by the
  pipelined pairs that start at the read: ld→st for a load, C read→D write for an accumulator read,
  A read→D write and A read→copy for an A read. A source is a write other than the reading operation
  itself, and it survives all relevant releases: the reader completes (`CompletedBefore`) before
  each release of a covering allocation (`Tmem.Pair.Covers`), or the release precedes the source.
  Allocation coverage of the reader and the source is checked once, by ERR-TMEM-ACCESS-LIFETIME.

Effect: The relations of the write order and the read source. The value a read returns is
  DEP-TC-LOAD-VALUE (loads and A reads), DEP-TC-MMA-VALUE (accumulator reads) and
  DEP-TMEM-SHIFT-VALUE (shift reads); the requirement that a read has a source is
  ERR-TMEM-READ-SOURCE. The direction is `reading` because acceptance rests on named readings:
  EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path
  is stricter than the text.
-/

/-- MMA `x`'s accumulator accesses precede MMA `y`'s: by completion or by the pipelined
C/D pairs (all three C/D rows share one condition). -/
def Before (L : Launch) (X : Execution) (x y : EvId) : Prop :=
  DoneBefore L X x y ∨ Pipelined L X .dWrite x .dWrite y

/-- A Tensor Memory write: an MMA result cell, a store, a copy or a shift. -/
def TmemWrite (L : Launch) (X : Execution) (w : EvId) (cell : Cell) : Prop :=
  X.MmaCell w cell ∨ StoreCell L X w cell ∨ CpCell X w cell ∨ ShiftCell X w cell

/-- Write `x` is ordered before `y`: an MMA by completion or pipeline, a store by
completion or pipeline, a copy by completion or the copy→A-read pipeline. -/
def WriteBefore (L : Launch) (X : Execution) (x y : EvId) : Prop :=
  Before L X x y ∨ StoreDoneBefore L X x y ∨ Pipelined L X .cpWrite x .aRead y

/-- A free/reallocate cannot preserve the old value just because the address matches: the
consumer (an MMA or a load) has completed before every release of a covering allocation, or
the release precedes the source. -/
def SourceLive (L : Launch) (X : Execution) (source consumer : EvId) (cell : Cell) : Prop :=
  ∀ cta r, r ∈ X.tmemHistory cta →
    Tmem.Pair.Covers L X r cell.cta consumer cell.column →
    ∀ release, Tmem.Pair.ReleaseOf L X r release →
      CompletedBefore L X consumer release ∨ baseCausality L X release source

/-- The kinds of Tensor Memory read: a register of a `tcgen05.ld`, the accumulator (C) read and
the A read of an MMA, and the read of a `tcgen05.shift`. -/
inductive TmemRead where
  | ld | acc | a | shift
  deriving DecidableEq, Repr

/-- The read of kind `k` by the operation issued at `e` has happened before write `w`: by the
reader's completion mechanism, because `w` is the reading operation's own write, or by a
pipelined pair that starts at the read. -/
def ReadBefore (L : Launch) (X : Execution) : TmemRead → EvId → EvId → Prop
  | .ld, e, w => WaitBefore L X .waitLd e w ∨ Pipelined L X .ldRead e .stWrite w
  | .acc, e, w => w = e ∨ DoneBefore L X e w ∨ Pipelined L X .cRead e .dWrite w
  | .a, e, w => w = e ∨ DoneBefore L X e w ∨ Pipelined L X .aRead e .dWrite w ∨
      Pipelined L X .aRead e .cpWrite w
  | .shift, e, w => w = e ∨ DoneBefore L X e w

/-- `source` is the write whose word the read of kind `k` by `e` takes from `cell`: a write of
the cell, other than `e`, ordered before `e`, with every other write of the cell before the
source or after the read, and no release of the allocation between them. -/
def ReadSource (L : Launch) (X : Execution) (k : TmemRead) (source e : EvId) (cell : Cell) :
    Prop :=
  source ≠ e ∧ TmemWrite L X source cell ∧ WriteBefore L X source e ∧
    (∀ other, TmemWrite L X other cell →
      other = source ∨ WriteBefore L X other source ∨ ReadBefore L X k e other) ∧
    SourceLive L X source e cell

/-- The source of a load register (the former `LoadStable` with `LoadBefore`). -/
theorem readSource_ld {L : Launch} {X : Execution} {source e : EvId} {cell : Cell} :
    ReadSource L X .ld source e cell ↔
      source ≠ e ∧ TmemWrite L X source cell ∧ WriteBefore L X source e ∧
      (∀ other, TmemWrite L X other cell → other = source ∨ WriteBefore L X other source ∨
        WaitBefore L X .waitLd e other ∨
        (SameWarp L e.1 other.1 ∧ TcBefore L X e other ∧
          (∃ address vals shape, X.TLd e address vals shape) ∧
          ∃ address vals shape, X.TSt other address vals shape)) ∧
      SourceLive L X source e cell := Iff.rfl

/-- The source of an accumulator read (the former `AccSource`, with `AccStable` and `Before`). -/
theorem readSource_acc {L : Launch} {X : Execution} {source e : EvId} {cell : Cell} :
    ReadSource L X .acc source e cell ↔
      source ≠ e ∧ TmemWrite L X source cell ∧ WriteBefore L X source e ∧
      (∀ other, TmemWrite L X other cell →
        other = source ∨ other = e ∨ WriteBefore L X other source ∨ Before L X e other) ∧
      SourceLive L X source e cell := by
  simp only [ReadSource, ReadBefore, Before, pipelined_cRead_dWrite]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, fun o ho => ?_, h5⟩
    rcases h4 o ho with h | h | h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, fun o ho => ?_, h5⟩
    rcases h4 o ho with h | h | h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))

/-- The source of a Tensor Memory A read (the stability part of the former `AReadSource`). -/
theorem readSource_a {L : Launch} {X : Execution} {source e : EvId} {cell : Cell} :
    ReadSource L X .a source e cell ↔
      source ≠ e ∧ TmemWrite L X source cell ∧ WriteBefore L X source e ∧
      (∀ other, TmemWrite L X other cell →
        other = source ∨ WriteBefore L X other source ∨ other = e ∨ DoneBefore L X e other ∨
          Pipelined L X .aRead e .dWrite other ∨ Pipelined L X .aRead e .cpWrite other) ∧
      SourceLive L X source e cell := Iff.rfl

/-- The source of a shift read (the stability part of the former `ShiftSource`). -/
theorem readSource_shift {L : Launch} {X : Execution} {source e : EvId} {cell : Cell} :
    ReadSource L X .shift source e cell ↔
      source ≠ e ∧ TmemWrite L X source cell ∧ WriteBefore L X source e ∧
      (∀ other, TmemWrite L X other cell →
        other = source ∨ WriteBefore L X other source ∨ other = e ∨ DoneBefore L X e other) ∧
      SourceLive L X source e cell := Iff.rfl

end
end PTX.TcMma
