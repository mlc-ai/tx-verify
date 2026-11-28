-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PredArr

@[expose] public section

/-! # The states before the rescale arm

The machine reaches the block's proxy fence (`fpx`) from the arm's last site (`rsfb`) or, when the
arm is skipped (`afterOst`: the block is the first or its vote is false), from the last
probability store; the arm's sites follow each other (`rsf`, then the loads, waits and stores of
the four chunks, `rsfb`); `rsf` is reached from the last probability store when the arm runs. A
step off these sites keeps the block index and the vote word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- A list lookup that is a site is the default or a member. -/
theorem getD_site (l : List Site) (n : Nat) (x s : Site) (h : l.getD n x = s) :
    x = s ∨ s ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h
  rcases hx : l[n]? with _ | y
  · rw [hx] at h; exact .inl h
  · rw [hx] at h
    exact .inr (h ▸ List.mem_of_getElem? hx)

/-- The block index and the vote word of two states agree. -/
def ArmSame (d d' : D) : Prop := d.vt = d'.vt ∧ d.bi = d'.bi

theorem ArmSame.trans {a b c : D} (h1 : ArmSame a b) (h2 : ArmSame b c) : ArmSame a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

-- The step tactic: split the machine's step off the site and close the goal.
set_option hygiene false in
local macro "pred_tac" : tactic => `(tactic|
  (obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d'
   cases s
   all_goals repeat' (rename_i x; fin_cases x)
   all_goals simp only [succ, dataRd, ncWord, poll, tcLoad, afterSmr, afterSink, afterA,
     afterEld, elemNext, loopEntry, advance, afterOst, finish, nextChunk, afterObar] at hn ⊢
   all_goals (repeat' split at hn)
   all_goals try
     first
     | (simp at hn; done)
     | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
     | (simp only [Option.some.injEq] at hn; subst hn
        rcases getD_site _ _ _ _ h with h1 | h1 <;> simp at h1)))

set_option linter.unusedSimpArgs false in
/-- **The state before `arrS`** is `fpx`, with the block index and the vote word kept. -/
theorem pred_arrS_same {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .arrS) : d'.site = .fpx ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `fpx`** is the arm's last site or the last probability store with the arm
skipped; the block index and the vote word are kept. -/
theorem pred_fpx {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .fpx) :
    (d'.site = .rsfb ∨ (d'.site = .ost 3 ∧ 3 ≤ d'.el ∧
      (scmpi .eq .b d'.bi 1 || !d'.vt) = true)) ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rsfb`** is the last chunk's store wait. -/
theorem pred_rsfb {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rsfb) : d'.site = .rstw 3 ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rstw c`** is the chunk's store. -/
theorem pred_rstw {d d' : D} {e : Event} {c : Fin 4} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rstw c) : d'.site = .rst c ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rst c`** is the chunk's load wait. -/
theorem pred_rst {d d' : D} {e : Event} {c : Fin 4} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rst c) : d'.site = .rldw c ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rldw c`** is the chunk's load. -/
theorem pred_rldw {d d' : D} {e : Event} {c : Fin 4} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rldw c) : d'.site = .rld c ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rld 0`**. -/
theorem pred_rld0 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rld 0) : d'.site = .rsf ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rld 1`**. -/
theorem pred_rld1 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rld 1) : d'.site = .rstw 0 ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rld 2`**. -/
theorem pred_rld2 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rld 2) : d'.site = .rstw 1 ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rld 3`**. -/
theorem pred_rld3 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rld 3) : d'.site = .rstw 2 ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before `rsf`** is the last probability store, with the arm running. -/
theorem pred_rsf {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .rsf) : d'.site = .ost 3 ∧ 3 ≤ d'.el ∧
      (scmpi .eq .b d'.bi 1 || !d'.vt) = false ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before the first element of `ost 0`** is the vote; its result is the vote word. -/
theorem pred_ost0 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .ost 0) (hel : d.el = 0) :
    d'.site = .vote ∧ (∀ q mm a r, e.kind = .voteMode q mm a r → d.vt = r) ∧ d.bi = d'.bi := by
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before the first element of `ost 1`** is the last element of `ost 0`. -/
theorem pred_ost1 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .ost 1) (hel : d.el = 0) :
    d'.site = .ost 0 ∧ 3 ≤ d'.el ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before the first element of `ost 2`** is the last element of `ost 1`. -/
theorem pred_ost2 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .ost 2) (hel : d.el = 0) :
    d'.site = .ost 1 ∧ 3 ≤ d'.el ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before the first element of `ost 3`** is the last element of `ost 2`. -/
theorem pred_ost3 {d d' : D} {e : Event} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .ost 3) (hel : d.el = 0) :
    d'.site = .ost 2 ∧ 3 ≤ d'.el ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

set_option linter.unusedSimpArgs false in
/-- **The state before a later element of `ost k`** is the previous element. -/
theorem pred_ostEl {d d' : D} {e : Event} {k : Fin 4} (hn : succ P L g w d' e = some (some d))
    (h : d.site = .ost k) (hel : 0 < d.el) :
    d'.site = .ost k ∧ d.el = d'.el + 1 ∧ ArmSame d d' := by
  unfold ArmSame
  pred_tac

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
