-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine

@[expose] public section

/-! # The state before the softmax-ready arrival is the proxy fence

Warpgroup 0's block ends with the proxy fence (`fpx`, pc 1120) and the arrival on the
softmax-ready barrier (`arrS`, pc 1122): the machine reaches `arrS` only from `fpx`
(`pred_arrS`; the successor of `fpx` is `arrS`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- A list lookup that is `arrS` is the default or a member. -/
private theorem getD_arrS (l : List Site) (n : Nat) (x : Site) (h : l.getD n x = .arrS) :
    x = .arrS ∨ Site.arrS ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h
  rcases hx : l[n]? with _ | y
  · rw [hx] at h; exact .inl h
  · rw [hx] at h
    exact .inr (h ▸ List.mem_of_getElem? hx)

set_option linter.unusedSimpArgs false in
/-- **Only `fpx` leads to `arrS`.** -/
theorem pred_arrS {d d' : D} {e : Event} (hn : succ P L g w d e = some (some d'))
    (h' : d'.site = .arrS) : d.site = .fpx := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [succ, dataRd, ncWord, poll, tcLoad, afterSmr, afterSink, afterA,
    afterEld, elemNext, loopEntry, advance, afterOst, finish, nextChunk, afterObar] at hn ⊢
  all_goals (repeat' split at hn)
  all_goals try
    first
    | (simp at hn; done)
    | (simp at hn; subst hn; simp at h'; done)
    | (simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       rcases getD_arrS _ _ _ h' with h | h <;> simp at h)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
