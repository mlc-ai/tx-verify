-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # The number of finished blocks of a trace

The finished blocks `(w0Fin l).1` of a trace are the blocks closed (pc 1122) since the last arrival
at pc 200. When no block is closed before an arrival at pc 200, their number is the number of events
at pc 1122 (`w0Fin_length`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- The events of `l` at pc 1122 (the blocks closed so far). -/
def w0Closed (l : List Event) : Nat := l.countP fun e => e.pc = w0ArrSPc

/-- No block is closed before an arrival at pc 200. -/
def W0NoEarlyClose (l : List Event) : Prop :=
  ∀ i (hi : i < l.length), (l[i]'hi).pc = w0ArrLPc → w0Closed (l.take i) = 0

theorem W0NoEarlyClose.init {l : List Event} {e : Event} (h : W0NoEarlyClose (l ++ [e])) :
    W0NoEarlyClose l := by
  intro i hi hpc
  have := h i (by simp; omega) (by rw [List.getElem_append_left hi]; exact hpc)
  rwa [List.take_append_of_le_length hi.le] at this

/-- **The finished blocks of a trace are its closing events** (no block closed before pc 200). -/
theorem w0Fin_length {l : List Event} (h : W0NoEarlyClose l) :
    (w0Fin l).1.length = w0Closed l := by
  induction l using List.reverseRecOn with
  | nil => simp [w0Fin, w0Closed]
  | append_singleton l e ih =>
    have ih := ih h.init
    have hne : ¬ (w0ArrLPc = w0ArrSPc) := by unfold w0ArrLPc w0ArrSPc; decide
    unfold w0Closed at ih ⊢
    rw [w0Fin_snoc, List.countP_append]
    by_cases h1 : e.pc = w0ArrSPc
    · simp [h1, ih]
    · by_cases h2 : e.pc = w0ArrLPc
      · have := h l.length (by simp) (by simp [h2])
        simp only [List.take_left'] at this
        unfold w0Closed at this
        simp [h2, hne, this]
      · simp [h1, h2, ih]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
