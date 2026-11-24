-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaSource
public import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # Tensor Memory cells written by MMAs and stores

A proof tool for kernels whose Tensor Memory cells are written both by MMA results and by
`tcgen05.st` (an accumulator rescaled in place, a tile published by stores). The library's
MMA-only lemmas assume no store (`tmemWrite_of_no_store`, `readOk_of_no_issue`); here:

* Without `tcgen05.cp` and `tcgen05.shift`, a Tensor Memory write is an MMA result cell or a
  store cell (`tmemWrite_of_no_copy`).
* The orders that make a write precede a later event, by kind: an MMA by observed completion
  (`WriteBefore.of_done`), a store by its thread's later `wait::st` (`WriteBefore.of_waitSt`) or
  by a tcgen05 order to a later load or store of its warp (`WriteBefore.of_pipe`); a load has read
  before a write by its thread's `wait::ld` (`ReadBefore.of_waitLd`).
* A cell's writes as a sequence `w 0, w 1, …, w (N - 1)` of any kind, the kernel's writer table
  (`Chain`). Its write `w k` is the source of a read that every later write follows
  (`Chain.stable`, `Chain.readSource`; `Chain.accSource` for the accumulator an MMA reads), and the
  last write of the table is the cell's last value (`Chain.lastWrote`).
* The Tensor Core read obligation without MMAs, copies and shifts, with stores whose loads return
  the stored words (`readOk_of_stores`; `readOk_of_no_issue` is the case without stores). -/

namespace PTX.TcMma
open PTX
noncomputable section

variable {L : Launch} {A : List Assumption} {X : Execution}

/-- **Without `tcgen05.cp` and `tcgen05.shift`, a Tensor Memory write is an MMA result cell or a
store cell.** -/
theorem tmemWrite_of_no_copy (hc : ∀ e c, ¬ X.CpIssue e c) (hs : ∀ e s, ¬ X.ShiftIssue e s)
    {w : EvId} {cell : Cell} (h : TmemWrite L X w cell) :
    X.MmaCell w cell ∨ StoreCell L X w cell := by
  rcases h with h | h | ⟨c, -, -, -, hp, -⟩ | ⟨sp, hp, -⟩
  · exact .inl h
  · exact .inr h
  · exact (hc _ _ hp).elim
  · exact (hs _ _ hp).elim

/-! ## Orders from a write -/

/-- An MMA whose completion is observed before `e` is written before `e`. -/
theorem WriteBefore.of_done {x e : EvId} (h : DoneBefore L X x e) : WriteBefore L X x e :=
  .inl (.inl h)

/-- A store followed by a `wait::st` of its thread, tcgen05-ordered before `e`, is written
before `e`. -/
theorem WriteBefore.of_waitSt {st w e : EvId} {a pc : Nat} {vals : List Value} {sh : TcShape}
    (hst : X.TSt st a vals sh) (hw : X.get w = some ⟨pc, .tc .waitSt⟩) (hthr : w.1 = st.1)
    (hlt : st.2 < w.2) (h : TcBefore L X w e) : WriteBefore L X st e :=
  .inr (.inl ⟨⟨a, vals, sh, hst⟩, .inl ⟨w, ⟨pc, hw⟩, hthr, hlt, h⟩⟩)

/-- A store tcgen05-ordered before a later load or store `e` of its warp is written before `e`
(the pipelined pairs st→ld and st→st). -/
theorem WriteBefore.of_pipe {st e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (hst : X.TSt st a vals sh) (hw : SameWarp L st.1 e.1) (h : TcBefore L X st e)
    (he : (∃ address vals sh, X.TLd e address vals sh) ∨
      ∃ address vals sh, X.TSt e address vals sh) :
    WriteBefore L X st e := by
  rcases he with he | he
  · exact .inr (.inl ⟨⟨a, vals, sh, hst⟩, .inr (.inl ⟨hw, h, ⟨a, vals, sh, hst⟩, he⟩)⟩)
  · exact .inr (.inl ⟨⟨a, vals, sh, hst⟩, .inr (.inr ⟨hw, h, ⟨a, vals, sh, hst⟩, he⟩)⟩)

/-- A load followed by a `wait::ld` of its thread, tcgen05-ordered before a write, has read
before it. -/
theorem ReadBefore.of_waitLd {ld w o : EvId} {pc : Nat} (hw : X.get w = some ⟨pc, .tc .waitLd⟩)
    (hthr : w.1 = ld.1) (hlt : ld.2 < w.2) (h : TcBefore L X w o) : ReadBefore L X .ld ld o :=
  .inl ⟨w, ⟨pc, hw⟩, hthr, hlt, h⟩

/-! ## A cell's writer table -/

/-- The writes of `cell` are `w 0, …, w (N - 1)`, each a write of the cell. -/
structure Chain (L : Launch) (X : Execution) (cell : Cell) (N : Nat) (w : Nat → EvId) : Prop where
  /-- Every write of the cell is in the table. -/
  cover : ∀ o, TmemWrite L X o cell → ∃ i < N, o = w i
  /-- Every entry writes the cell. -/
  write : ∀ i < N, TmemWrite L X (w i) cell

namespace Chain
variable {cell : Cell} {N : Nat} {w : Nat → EvId}

/-- **A read takes the value of the write before it.** Write `w k` is stable for the read of
kind `r` by `e` (the stability clause of `ReadSource`) when every earlier write is written before
it and the read happens before every later one. -/
theorem stable (hC : Chain L X cell N w) {r : TmemRead} {k : Nat} {e : EvId}
    (hbefore : ∀ i < k, w i ≠ w k → WriteBefore L X (w i) (w k))
    (hafter : ∀ j, k < j → j < N → w j ≠ w k → ReadBefore L X r e (w j)) :
    ∀ o, TmemWrite L X o cell → o = w k ∨ WriteBefore L X o (w k) ∨ ReadBefore L X r e o := by
  intro o ho
  obtain ⟨i, hi, rfl⟩ := hC.cover o ho
  by_cases he : w i = w k
  · exact .inl he
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · exact .inr (.inl (hbefore i h he))
  · exact .inl rfl
  · exact .inr (.inr (hafter i h hi he))

/-- **The last write of the table is the cell's last write**, when every other write is written
before it. -/
theorem lastWrote (hC : Chain L X cell N w) {k : Nat} {v : Value} (hk : Wrote L A X (w k) cell v)
    (hbefore : ∀ i < N, w i ≠ w k → WriteBefore L X (w i) (w k)) : LastWrote L A X cell v :=
  ⟨w k, hk, fun o ho => by
    obtain ⟨i, hi, rfl⟩ := hC.cover o ho
    by_cases he : w i = w k
    · exact .inl he
    · exact .inr (hbefore i hi he)⟩

/-- **A read source from the table**: write `w k < N`, other than the reader `e`, written before
`e`, stable for the read and live. -/
theorem readSource (hC : Chain L X cell N w) {r : TmemRead} {k : Nat} (hkN : k < N) {e : EvId}
    (hne : w k ≠ e) (hwb : WriteBefore L X (w k) e)
    (hbefore : ∀ i < k, w i ≠ w k → WriteBefore L X (w i) (w k))
    (hafter : ∀ j, k < j → j < N → w j ≠ w k → ReadBefore L X r e (w j))
    (hlive : SourceLive L X (w k) e cell) : ReadSource L X r (w k) e cell :=
  ⟨hne, hC.write k hkN, hwb, hC.stable hbefore hafter, hlive⟩

/-- **An MMA's accumulator source from the table**: write `w k < N`, written before the consuming
MMA `c`, with every later write other than `c` after `c`, and live. -/
theorem accSource (hC : Chain L X cell N w) {k : Nat} (hkN : k < N) {c : EvId}
    (hne : w k ≠ c) (hwb : WriteBefore L X (w k) c)
    (hbefore : ∀ i < k, w i ≠ w k → WriteBefore L X (w i) (w k))
    (hafter : ∀ j, k < j → j < N → w j ≠ w k → w j ≠ c → Before L X c (w j))
    (hlive : SourceLive L X (w k) c cell) : ReadSource L X .acc (w k) c cell := by
  refine hC.readSource hkN hne hwb hbefore (fun j hkj hjN hjk => ?_) hlive
  by_cases hjc : w j = c
  · exact .inl hjc
  · rcases hafter j hkj hjN hjk hjc with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

end Chain

/-! ## The read obligation with stores -/

/-- **The Tensor Core read obligation without MMAs, copies and shifts.** Every load's source is
then a store, and the kernel supplies that such a load returns a word containing the stored
value. -/
theorem readOk_of_stores (h : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hcp : ∀ e c, ¬ X.CpIssue e c) (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (hst : ∀ load address vals sh j source cell value, X.TLd load address vals sh →
      LoadCell L X load j cell → ReadSource L X .ld source load cell →
      StoreValue L X source cell value →
      ∃ word, vals[j]? = some word ∧ WordContains value word) : ReadOk L A X := by
  refine ⟨?_, fun mma _ _ _ _ _ _ ha _ _ _ _ => ?_⟩
  swap
  · obtain ⟨_, _, _, _, hi, _⟩ := ha
    exact (h _ _ _ _ _ hi).elim
  intro load address vals sh j source cell value hl hc hs hw
  rcases hw with hr | hv | ⟨c, _, _, _, _, _, _, hp, -⟩ | ⟨_, _, ⟨⟨sp, hp, -⟩, -⟩, -⟩
  · cases hr with
    | overwrite hi _ _ _ => exact (h _ _ _ _ _ hi).elim
    | accumulate hi _ _ _ _ _ => exact (h _ _ _ _ _ hi).elim
    | accumulateStored hi _ _ _ _ _ => exact (h _ _ _ _ _ hi).elim
  · exact hst load address vals sh j source cell value hl hc hs hv
  · exact (hcp _ _ hp).elim
  · exact (hsh _ _ hp).elim

end
end PTX.TcMma
