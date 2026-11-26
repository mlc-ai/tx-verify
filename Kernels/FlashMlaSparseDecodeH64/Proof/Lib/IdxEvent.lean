-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxStore
public import Lemmas.Kit.CountAt

@[expose] public section

/-! # The index lane's stores by their count

The `m`-th store (counting from 0) of an index lane before its event `ia` is an event of the
lane before `ia`, a write at a pc of the index code, with `m` stores before it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Kit

variable {X : Execution}

/-- **The `m`-th store before an event.** -/
theorem idxWr_event_before {gl ia m : Nat} (h : m < ((X.tr gl).take ia).countP idxWr) :
    ∃ kw pcw aw bsw, kw < ia ∧ X.get (gl, kw) = some ⟨pcw, .wr aw bsw⟩ ∧
      (2332 ≤ pcw ∧ pcw ≤ 2586) ∧ ((X.tr gl).take kw).countP idxWr = m := by
  obtain ⟨kw, ev, hev, hev', hcnt⟩ := exists_countP_eq idxWr ((X.tr gl).take ia) m h
  have hlt : kw < ia := by
    rcases Nat.lt_or_ge kw ia with hk | hk
    · exact hk
    · simp [Nat.not_lt.mpr hk] at hev
  have hx : (X.tr gl)[kw]? = some ev := by
    simpa [List.getElem?_take, hlt] using hev
  obtain ⟨pcw, kd⟩ := ev
  obtain ⟨aw, bsw, rfl⟩ : ∃ aw bsw, kd = .wr aw bsw := by
    cases kd <;> first | (simp [idxWr] at hev'; done) | exact ⟨_, _, rfl⟩
  refine ⟨kw, pcw, aw, bsw, hlt, hx, by simpa [idxWr] using hev', ?_⟩
  rw [List.take_take, Nat.min_eq_left hlt.le] at hcnt
  exact hcnt

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
