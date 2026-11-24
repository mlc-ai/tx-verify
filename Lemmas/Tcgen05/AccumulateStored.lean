-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TmemWriters

@[expose] public section

/-! # An MMA accumulating onto a value stored by `tcgen05.st`

A proof tool for an accumulator that a thread rewrites in place between MMAs (FA4's output
accumulator: the correction warps load `O`, scale it by `α`, store it back, and the next PV MMA
accumulates onto the stored value). Core derives such a result with `Result.accumulateStored`:
the accumulator's source is a store, not an earlier MMA result.

* An accumulating MMA's result from its accumulator source, whichever kind of write it is
  (`Result.of_source`: an MMA result or a store; a `tcgen05.cp` word is never an accumulator
  source in Core).
* The same from a cell's writer table (`TcMma.Chain`, `Chain.result`): the source is the table's
  write before the MMA, written before it and not overwritten until it completes.
* **The value chain** load → register computation → store → accumulate. A load returns a word
  containing its source's value (`load_word`, from `LoadReadOk`). If the store writes `F word`,
  the stored value is `F word` (`StoreValue.of_load`), and the MMA whose accumulator source is the
  store accumulates onto it (`Result.of_rescale`). `F` is the thread's computation between the load
  and the store (FA4: a multiplication by `α`), supplied by the thread layer. -/

namespace PTX.TcMma
open PTX
noncomputable section

variable {L : Launch} {A : List Assumption} {X : Execution}

/-- **An accumulating MMA's result from its accumulator source**, an MMA result or a store. -/
theorem Result.of_source {i src : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat}
    {row col : Nat} {cell : Cell} {operands : AsyncCopy.MmaOperands} {old value : Value}
    (hi : X.MmaIssue i d s true mask) (hpos : writeCell s d mask row col = some cell)
    (hreads : X.async.mmaOperands i = some operands)
    (hsrc : Result L A X src cell old ∨ StoreValue L X src cell old)
    (hacc : ReadSource L X .acc src i cell)
    (harith : eval A s.descriptor true operands.a operands.b (some old) row col = .ok value) :
    Result L A X i cell value := by
  rcases hsrc with h | h
  · exact .accumulate hi hpos hreads h hacc harith
  · exact .accumulateStored hi hpos hreads h hacc harith

/-- A store's value at a cell is a write of that cell. -/
theorem StoreValue.write {st : EvId} {cell : Cell} {v : Value} (h : StoreValue L X st cell v) :
    TmemWrite L X st cell := by
  obtain ⟨address, vals, sh, j, hst, hj, hc⟩ := h
  exact .inr (.inl ⟨address, vals, sh, j, hst, (List.getElem?_eq_some_iff.mp hj).1, hc⟩)

/-- **The result of an MMA accumulating onto the store `w k` of a cell's writer table**: the
store is written before the MMA, every earlier write of the table before the store, and every
later write other than the MMA follows the MMA. -/
theorem Chain.result {cell : Cell} {N : Nat} {w : Nat → EvId} (hC : Chain L X cell N w)
    {k : Nat} (hkN : k < N) {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat}
    {row col : Nat} {operands : AsyncCopy.MmaOperands} {old value : Value}
    (hi : X.MmaIssue i d s true mask) (hpos : writeCell s d mask row col = some cell)
    (hreads : X.async.mmaOperands i = some operands)
    (hsrc : Result L A X (w k) cell old ∨ StoreValue L X (w k) cell old) (hne : w k ≠ i)
    (hwb : WriteBefore L X (w k) i)
    (hbefore : ∀ j < k, w j ≠ w k → WriteBefore L X (w j) (w k))
    (hafter : ∀ j, k < j → j < N → w j ≠ w k → w j ≠ i → Before L X i (w j))
    (hlive : SourceLive L X (w k) i cell)
    (harith : eval A s.descriptor true operands.a operands.b (some old) row col = .ok value) :
    Result L A X i cell value :=
  Result.of_source hi hpos hreads hsrc (hC.accSource hkN hne hwb hbefore hafter hlive) harith

/-! ## The value chain -/

/-- **A load returns a word containing its source's value.** -/
theorem load_word (hok : LoadReadOk L A X) {ld src : EvId} {address : Nat}
    {vals : List Value} {sh : TcShape} {j : Nat} {cell : Cell} {v : Value}
    (hld : X.TLd ld address vals sh) (hcell : LoadCell L X ld j cell)
    (hrs : ReadSource L X .ld src ld cell) (hw : Wrote L A X src cell v) :
    ∃ word, vals[j]? = some word ∧ WordContains v word :=
  hok ld address vals sh j src cell v hld hcell hrs hw

/-- **The value a store writes after a load.** If store `st` writes `F word` at register slot
`j'` whenever the load's slot `j` holds `word`, it writes `F word`, at the cell of slot `j'` for
the store's shape, for a word containing the load source's value. -/
theorem StoreValue.of_load (hok : LoadReadOk L A X) {ld src st : EvId} {address address' : Nat}
    {vals vals' : List Value} {sh sh' : TcShape} {j j' : Nat} {cell : Cell} {v : Value}
    {F : Value → Value}
    (hld : X.TLd ld address vals sh) (hcell : LoadCell L X ld j cell)
    (hrs : ReadSource L X .ld src ld cell) (hw : Wrote L A X src cell v)
    (hst : X.TSt st address' vals' sh')
    (hval : ∀ word, vals[j]? = some word → vals'[j']? = some (F word)) :
    ∃ word, WordContains v word ∧
      StoreValue L X st (tcDataCell L st.1 sh' address' j') (F word) := by
  obtain ⟨word, hwd, hc⟩ := load_word hok hld hcell hrs hw
  exact ⟨word, hc, address', vals', sh', j', hst, hval word hwd, rfl⟩

/-- **Load → computation → store → accumulate.** The store `st` writes `F word` from the load's
word; the MMA `i` accumulates at the store's cell, with the store as its accumulator source. Its
result is the MMA arithmetic on `F word`, for a word containing the load source's value. The
store's cell is slot `j'` of its own shape `sh'`. -/
theorem Result.of_rescale (hok : LoadReadOk L A X) {ld src st i : EvId} {address address' : Nat}
    {vals vals' : List Value} {sh sh' : TcShape} {j j' : Nat} {cellL : Cell} {v : Value}
    {F : Value → Value}
    (hld : X.TLd ld address vals sh) (hcell : LoadCell L X ld j cellL)
    (hrs : ReadSource L X .ld src ld cellL) (hw : Wrote L A X src cellL v)
    (hst : X.TSt st address' vals' sh')
    (hval : ∀ word, vals[j]? = some word → vals'[j']? = some (F word))
    {d : Nat} {s : OperandSpec} {mask : List Nat} {row col : Nat}
    {operands : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s true mask)
    (hpos : writeCell s d mask row col = some (tcDataCell L st.1 sh' address' j'))
    (hreads : X.async.mmaOperands i = some operands)
    (hacc : ReadSource L X .acc st i (tcDataCell L st.1 sh' address' j'))
    (harith : ∀ word, WordContains v word →
      ∃ value, eval A s.descriptor true operands.a operands.b (some (F word)) row col = .ok value) :
    ∃ word value, WordContains v word ∧
      eval A s.descriptor true operands.a operands.b (some (F word)) row col = .ok value ∧
      Result L A X i (tcDataCell L st.1 sh' address' j') value := by
  obtain ⟨word, hc, hsv⟩ := StoreValue.of_load hok hld hcell hrs hw hst hval
  obtain ⟨value, hv⟩ := harith word hc
  exact ⟨word, value, hc, hv, .accumulateStored hi hpos hreads hsv hacc hv⟩

end
end PTX.TcMma
