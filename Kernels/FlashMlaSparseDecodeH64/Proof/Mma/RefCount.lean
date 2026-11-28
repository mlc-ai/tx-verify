-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ref
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The MMA warp's counts along its order

The classes of each event kind of the role (`cls_kind`), and the counts at each place of the
role's order plus the class of the event there are the counts at the next place (`pro_*` in the
prologue, `loop_*` in a block, `bar_step`). The objects are a parameter `O : Objs` (`Ref.lean`),
so the counts' unfolding never compares two object locations. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedSimpArgs false

variable {L : Launch} {g : Nat} {O : Objs}

/-- The counts after an event of class `X` (or of no class, `X = none`). -/
def plus (A : Cnt → Nat) (X : Option Cnt) (c : Cnt) : Nat :=
  A c + match X with | some x => ind (c = x) | none => 0

theorem cls_kind {e : Event} (hpc : inRole e = true) (c : Cnt) :
    (if cls c e then 1 else 0) = match kindOf e with | some x => ind (c = x) | none => 0 := by
  simp only [cls, hpc, Bool.true_and]
  cases kindOf e <;> simp [eq_comm]

/-- **The counts after a step**: from counts `A` at the state, those after the event. -/
theorem core_bump {n A B : Cnt → Nat} {e : Event} (hpc : inRole e = true)
    (hn : ∀ c, c ≠ .ub → n c = A c)
    (h : ∀ c, c ≠ .ub → plus A (kindOf e) c = B c) :
    ∀ c, c ≠ .ub → Code.bump cls n e c = B c := fun c hc => by
  simp only [Code.bump]
  have h' := h c hc
  unfold plus at h'
  rw [hn c hc, cls_kind hpc c]
  exact h'

/-- `.ub` is in no class but its own. -/
theorem bump_ub {n : Cnt → Nat} {e : Event} (hub : ∀ f, e.kind ≠ .ub f) (h : n .ub = 0) :
    Code.bump cls n e .ub = 0 := by
  have hk : kindOf e ≠ some .ub := by
    unfold kindOf
    split <;> simp_all
  simp [Code.bump, h, cls, hk]

/-- The counts' unfolding: the objects' indicators stay atoms. -/
macro "cnt_simp" : tactic => `(tactic| simp only [plus, cntAt, proCnt, loopCnt, ind, useAt,
    reduceCtorEq, Cnt.acq.injEq, Cnt.arrive.injEq, Cnt.commit.injEq, Cnt.bar.injEq, ↓reduceIte,
    Bool.false_eq_true, and_true, and_false, true_and, false_and, Nat.reduceLeDiff,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.le_refl, Nat.mul_add, Nat.mul_one,
    Nat.add_zero, Nat.zero_add])

/-- `cnt_step`: per class, the counts unfolded, the place facts in the context applied. -/
macro "cnt_step" : tactic => `(tactic| (intro c; cases c <;> cnt_simp <;>
    (try simp only [*, and_false, false_and, and_true, true_and, ↓reduceIte, Nat.reduceEqDiff])
    <;> omega))

/-- `cnt_stepN`: `cnt_step` at literal places (the MMA counts evaluated). -/
macro "cnt_stepN" : tactic => `(tactic| (intro c; cases c <;> cnt_simp <;>
    (try simp only [*, mmaIn, and_false, false_and, and_true, true_and, ↓reduceIte,
      Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.lt_irrefl, Nat.mul_add,
      Nat.mul_one, Nat.mul_zero, Nat.add_zero]) <;> omega))

/-- An event of no class keeps the counts. -/
theorem plus_none (A : Cnt → Nat) : plus A none = A := by
  funext c
  simp [plus]

/-! ### The prologue -/

theorem pro_elect :
    ∀ c, plus (cntAt O 0 0 0 false) (some .elect) c = cntAt O 1 0 0 false c := by cnt_stepN

theorem pro_tma (j : Nat) (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    ∀ c, plus (cntAt O j 0 0 false) (some .tma) c = cntAt O (j + 1) 0 0 false c := by
  have : ¬ 9 ≤ j := by omega
  have : ¬ 10 ≤ j := by omega
  have : ¬ 11 ≤ j := by omega
  have : ¬ 28 ≤ j := by omega
  have : ¬ 29 ≤ j := by omega
  have : ¬ 30 ≤ j := by omega
  cnt_step

theorem pro_arrive :
    ∀ c, plus (cntAt O 9 0 0 false) (some (.arrive O.qTma)) c = cntAt O 10 0 0 false c := by
  cnt_stepN

theorem pro_acqQ :
    ∀ c, plus (cntAt O 10 0 0 false) (some (.acq O.qTma)) c = cntAt O 11 0 0 false c := by
  cnt_stepN

/-- The two fences. -/
theorem pro_none (j : Nat) (h : j = 11 ∨ j = 30) :
    ∀ c, plus (cntAt O j 0 0 false) none c = cntAt O (j + 1) 0 0 false c := by
  rcases h with rfl | rfl <;> cnt_stepN

theorem pro_cp (j : Nat) (h1 : 12 ≤ j) (h8 : j ≤ 27) :
    ∀ c, plus (cntAt O j 0 0 false) (some .cp) c = cntAt O (j + 1) 0 0 false c := by
  have : 9 ≤ j := by omega
  have : 10 ≤ j := by omega
  have : 11 ≤ j := by omega
  have : ¬ 28 ≤ j := by omega
  have : ¬ 29 ≤ j := by omega
  have : ¬ 30 ≤ j := by omega
  have : 1 ≤ j := by omega
  cnt_step

theorem pro_commit :
    ∀ c, plus (cntAt O 28 0 0 false) (some (.commit O.qUt)) c = cntAt O 29 0 0 false c := by
  cnt_stepN

theorem pro_acqU :
    ∀ c, plus (cntAt O 29 0 0 false) (some (.acq O.qUt)) c = cntAt O 30 0 0 false c := by
  cnt_stepN

/-! ### A block -/

theorem loop_acqR (r : Nat) :
    ∀ c, plus (cntAt O 31 r 0 false) (some (.acq (O.ready (r % 2)))) c =
      cntAt O 31 r 1 false c := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;> rw [hr] <;> cnt_stepN

/-- The two fences. -/
theorem loop_none (r i : Nat) (h : i = 1 ∨ i = 20) :
    ∀ c, plus (cntAt O 31 r i false) none c = cntAt O 31 r (i + 1) false c := by
  rcases h with rfl | rfl <;> cnt_stepN

theorem loop_mma1 (r i : Nat) (h2 : 2 ≤ i) (h17 : i ≤ 17) :
    ∀ c, plus (cntAt O 31 r i false) (some .mma) c = cntAt O 31 r (i + 1) false c := by
  have : 1 ≤ i := by omega
  have : ¬ 18 ≤ i := by omega
  have : ¬ 19 ≤ i := by omega
  have : ¬ 20 ≤ i := by omega
  have : mmaIn (i + 1) = mmaIn i + 1 := by unfold mmaIn; split_ifs <;> omega
  cnt_step

theorem loop_mma2 (r i : Nat) (h2 : 21 ≤ i) (h17 : i ≤ 28) :
    ∀ c, plus (cntAt O 31 r i false) (some .mma) c = cntAt O 31 r (i + 1) false c := by
  have : 1 ≤ i := by omega
  have : 18 ≤ i := by omega
  have : 19 ≤ i := by omega
  have : 20 ≤ i := by omega
  have : mmaIn (i + 1) = mmaIn i + 1 := by unfold mmaIn; split_ifs <;> omega
  cnt_step

theorem loop_commitK (r : Nat) :
    ∀ c, plus (cntAt O 31 r 18 false) (some (.commit (O.qk (r % 2)))) c =
      cntAt O 31 r 19 false c := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;> rw [hr] <;> cnt_stepN

theorem loop_acqS (r : Nat) :
    ∀ c, plus (cntAt O 31 r 19 false) (some (.acq (O.so (r % 2)))) c =
      cntAt O 31 r 20 false c := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;> rw [hr] <;> cnt_stepN

/-- **The block's end**: the commit to `bar_sv_done[r % 2]` starts block `r + 1`. -/
theorem loop_end (r : Nat) :
    ∀ c, plus (cntAt O 31 r 29 false) (some (.commit (O.sv (r % 2)))) c =
      cntAt O 31 (r + 1) 0 false c := by
  have h0 := ringUses_succ (S := 2) (s := 0) (by decide) r
  have h1 := ringUses_succ (S := 2) (s := 1) (by decide) r
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;> rw [hr] <;> cnt_stepN

/-- **The CTA barrier.** -/
theorem bar_step {R : Nat} (c : Cnt) :
    plus (cntAt O 31 R 0 false) (some (.bar 12)) c = cntAt O 31 R 0 true c := by
  simp [plus, cntAt]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
