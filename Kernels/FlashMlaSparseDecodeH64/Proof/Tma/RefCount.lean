-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The TMA warp's counts along its order

An event at a pc of the role bumps exactly its kind's class (`bump_kind`), and the counts at each
place of the role's order plus the class of the event there are the counts at the next place
(`pro_*` in the prologue, `blk_*` in a block, `fin_bar`). The objects are a parameter
`O : Objs` (`Ref.lean`): the unfolding never compares two object locations. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedSimpArgs false

variable {O : Objs}

/-- The counts `A` after an event of class `X` (`none`: of no class). -/
def plus (A : Cnt → Nat) (X : Option Cnt) (c : Cnt) : Nat :=
  A c + (X.map fun x => ind (c = x)).getD 0

/-- **The counts after a step**: from counts `A` at the state, those after the event. -/
theorem bump_kind {n A B : Cnt → Nat} {e : Event} (hpc : inRole e = true)
    (hn : ∀ c, c ≠ .ub → n c = A c)
    (h : ∀ c, c ≠ .ub → plus A (kindOf e) c = B c) :
    ∀ c, c ≠ .ub → Code.bump cls n e c = B c := by
  intro c hc
  rw [← h c hc, Code.bump, hn c hc, plus]
  congr 1
  unfold cls
  rw [hpc, Bool.true_and]
  rcases kindOf e with _ | x
  · simp
  · by_cases hx : c = x
    · subst hx; simp
    · simp [hx, Ne.symm hx]

/-- Undefined behaviour is in no class but its own. -/
theorem bump_ub0 {n : Cnt → Nat} {e : Event} (hub : ∀ f, e.kind ≠ .ub f) (h : n .ub = 0) :
    Code.bump cls n e .ub = 0 := by
  have hk : kindOf e ≠ some .ub := by
    unfold kindOf
    split <;> simp_all
  simp [Code.bump, h, cls, hk]

/-- An event of no class keeps the counts. -/
theorem plus_none' (A : Cnt → Nat) : plus A none = A := by
  funext c
  simp [plus]

/-- The counts' unfolding: the objects' indicators stay atoms. -/
macro "tcnt_simp" : tactic => `(tactic| simp only [plus, Option.map_some, Option.getD_some,
    Option.map_none, Option.getD_none, cntAt, proCnt, loopCnt, ind, useAt, reduceCtorEq,
    Cnt.acq.injEq, Cnt.arrive.injEq, Cnt.gather.injEq, Cnt.bar.injEq,
    ↓reduceIte, Bool.false_eq_true, and_true,
    and_false, true_and, false_and, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.le_refl, Nat.mul_add, Nat.mul_one, Nat.add_zero, Nat.zero_add])

/-- `tcnt_step`: per class, the counts unfolded, the facts in the context applied. -/
macro "tcnt_step" : tactic => `(tactic| (intro c; cases c <;> tcnt_simp <;>
    (try simp only [*, and_false, false_and, and_true, true_and, ↓reduceIte, Nat.reduceEqDiff,
      Nat.reduceLeDiff, Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero]) <;> omega))

/-! ### The prologue -/

theorem pro_elect :
    ∀ c, plus (cntAt O 0 0 0 0 0 false) (some .elect) c = cntAt O 1 0 0 0 0 false c := by
  tcnt_step

theorem pro_acqU :
    ∀ c, plus (cntAt O 1 0 0 0 0 false) (some (.acq O.qUt)) c = cntAt O 2 0 0 0 0 false c := by
  tcnt_step

theorem pro_acqL :
    ∀ c, plus (cntAt O 2 0 0 0 0 false) (some (.acq O.last)) c = cntAt O 3 0 0 0 0 false c := by
  tcnt_step

/-! ### A block -/

/-- The four values of `r % 4`, with `r % 2`. -/
theorem mod4_cases (r : Nat) :
    (r % 4 = 0 ∧ r % 2 = 0) ∨ (r % 4 = 1 ∧ r % 2 = 1) ∨ (r % 4 = 2 ∧ r % 2 = 0) ∨
      (r % 4 = 3 ∧ r % 2 = 1) := by omega

theorem blk_ready (r : Nat) :
    ∀ c, plus (cntAt O 3 r 0 0 0 false) (some (.acq (O.ready (r % 4)))) c =
      cntAt O 3 r 1 0 0 false c := by
  rcases mod4_cases r with ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ <;> rw [h4] <;> tcnt_step

theorem blk_free (r : Nat) :
    ∀ c, plus (cntAt O 3 r 1 0 0 false) (some (.acq (O.free (r % 2)))) c =
      cntAt O 3 r 2 0 0 false c := by
  rcases mod4_cases r with ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ <;> rw [h2] <;> tcnt_step

theorem blk_rd (r i rd gs : Nat) :
    ∀ c, plus (cntAt O 3 r i rd gs false) (some .rd) c = cntAt O 3 r i (rd + 1) gs false c := by
  intro c; cases c <;> (tcnt_simp; try omega)

theorem blk_gather (r i rd gs : Nat) :
    ∀ c, plus (cntAt O 3 r i rd gs false) (some (.gather (O.raw (r % 2)))) c =
      cntAt O 3 r i rd (gs + 1) false c := by
  rcases mod4_cases r with ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ <;> rw [h2] <;> tcnt_step

theorem blk_raw (r : Nat) :
    ∀ c, plus (cntAt O 3 r 2 64 16 false) (some (.arrive (O.raw (r % 2)))) c =
      cntAt O 3 r 3 64 16 false c := by
  rcases mod4_cases r with ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ <;> rw [h2] <;> tcnt_step

/-- **The block's end**: the arrival on `valid_coord_free[r % 4]` starts block `r + 1`. -/
theorem blk_end (r : Nat) :
    ∀ c, plus (cntAt O 3 r 3 64 16 false) (some (.arrive (O.cfree (r % 4)))) c =
      cntAt O 3 (r + 1) 0 0 0 false c := by
  have a0 := ringUses_succ (S := 4) (s := 0) (by decide) r
  have a1 := ringUses_succ (S := 4) (s := 1) (by decide) r
  have a2 := ringUses_succ (S := 4) (s := 2) (by decide) r
  have a3 := ringUses_succ (S := 4) (s := 3) (by decide) r
  have b0 := ringUses_succ (S := 2) (s := 0) (by decide) r
  have b1 := ringUses_succ (S := 2) (s := 1) (by decide) r
  rcases mod4_cases r with ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ <;> rw [h4] <;> tcnt_step

/-- **The CTA barrier.** -/
theorem fin_bar {R : Nat} (c : Cnt) :
    plus (cntAt O 3 R 0 0 0 false) (some (.bar 12)) c = cntAt O 3 R 0 0 0 true c := by
  simp [plus, cntAt]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
