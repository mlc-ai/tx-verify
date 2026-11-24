-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # The successors of the correction machine's states: definitions

Every step of the correction machine (`succ_cases`) either stays at its state (a failed poll), or
moves to the next element of a vector store, or moves to a listed successor of its site (`nexts`)
at the successor's sub-step; in the last case it keeps the rounds' values (the counter, the
used-K length, the scan) when it lands in the rounds or the final stage, unless it is the entry
or the end of a round, and it keeps the row sums when it lands in the final stage, unless it reads
a row sum. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The values the rounds' conjuncts read are unchanged. -/
def frameT (v v' : V) : Prop := v'.trip = v.trip ∧ v'.ukw = v.ukw ∧ v'.sc = v.sc

/-- The row sums are unchanged. -/
def frameR (v v' : V) : Prop := v'.rs0 = v.rs0 ∧ v'.rs1 = v.rs1

variable {p : Params} {L : Launch} {g : Nat}

@[simp] theorem setS_trip (v : V) (x : Sc) (st : Fin 2) : (setS v x st).trip = v.trip := by
  fin_cases st <;> rfl
@[simp] theorem setS_ukw (v : V) (x : Sc) (st : Fin 2) : (setS v x st).ukw = v.ukw := by
  fin_cases st <;> rfl
@[simp] theorem setS_sc (v : V) (x : Sc) (st : Fin 2) : (setS v x st).sc = v.sc := by
  fin_cases st <;> rfl
@[simp] theorem setS_rs0 (v : V) (x : Sc) (st : Fin 2) : (setS v x st).rs0 = v.rs0 := by
  fin_cases st <;> rfl
@[simp] theorem setS_rs1 (v : V) (x : Sc) (st : Fin 2) : (setS v x st).rs1 = v.rs1 := by
  fin_cases st <;> rfl
@[simp] theorem setB_trip (v : V) (x : BitVec 64) (st : Fin 2) : (setB v x st).trip = v.trip := by
  fin_cases st <;> rfl
@[simp] theorem setB_ukw (v : V) (x : BitVec 64) (st : Fin 2) : (setB v x st).ukw = v.ukw := by
  fin_cases st <;> rfl
@[simp] theorem setB_sc (v : V) (x : BitVec 64) (st : Fin 2) : (setB v x st).sc = v.sc := by
  fin_cases st <;> rfl
@[simp] theorem setB_rs0 (v : V) (x : BitVec 64) (st : Fin 2) : (setB v x st).rs0 = v.rs0 := by
  fin_cases st <;> rfl
@[simp] theorem setB_rs1 (v : V) (x : BitVec 64) (st : Fin 2) : (setB v x st).rs1 = v.rs1 := by
  fin_cases st <;> rfl
@[simp] theorem setRs_trip (v : V) (x : ℝ) (st : Fin 2) : (setRs v x st).trip = v.trip := by
  fin_cases st <;> rfl
@[simp] theorem setRs_ukw (v : V) (x : ℝ) (st : Fin 2) : (setRs v x st).ukw = v.ukw := by
  fin_cases st <;> rfl
@[simp] theorem setRs_sc (v : V) (x : ℝ) (st : Fin 2) : (setRs v x st).sc = v.sc := by
  fin_cases st <;> rfl
@[simp] theorem setRm_trip (v : V) (x : Mx) (st : Fin 2) : (setRm v x st).trip = v.trip := by
  fin_cases st <;> rfl
@[simp] theorem setRm_ukw (v : V) (x : Mx) (st : Fin 2) : (setRm v x st).ukw = v.ukw := by
  fin_cases st <;> rfl
@[simp] theorem setRm_sc (v : V) (x : Mx) (st : Fin 2) : (setRm v x st).sc = v.sc := by
  fin_cases st <;> rfl
@[simp] theorem setRm_rs0 (v : V) (x : Mx) (st : Fin 2) : (setRm v x st).rs0 = v.rs0 := by
  fin_cases st <;> rfl
@[simp] theorem setRm_rs1 (v : V) (x : Mx) (st : Fin 2) : (setRm v x st).rs1 = v.rs1 := by
  fin_cases st <;> rfl

/-- The step facts of a move to a listed successor. -/
def MoveFacts (d d' : D) (e : Event) : Prop :=
  d'.site ∈ nexts d.site ∧ d'.k = kIn d'.site ∧ (d.site.isFst = true → d.k.val = 3) ∧
    (d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc) ∧
    (d.site.special = false → (inRound d'.site.pc = true ∨ tailR d'.site = true) →
      frameT d.v d'.v) ∧
    (d.site.isFsum = false → tailR d'.site = true → frameR d.v d'.v)

set_option hygiene false in
/-- Unfold a step and split it into its branches, each with its successor substituted. -/
macro "sc_split" : tactic => `(tactic| (
  simp only [succ, word32, real32, scale32, max32, scAt, D.mk', D.ite, afterTotal, loopHead,
    scanExit, passStart, afterTiles, enterRounds, roundEnd, afterVote, afterFinal, afterLse,
    Fin.isValue, ↓reduceIte, Bool.false_eq_true] at h
  repeat' (first | (cases h; done) | split at h |
    simp only [Option.map_some, Option.map_none, reduceCtorEq] at h)
  all_goals first | (cases h; done) | (cases h) | skip))

set_option hygiene false in
/-- Close one branch. -/
macro "sc_close" : tactic => `(tactic| (
  first
    | (left; exact ⟨rfl, _, _, _, _, ‹_›⟩)
    | (left; refine ⟨rfl, ?_⟩; rename_i hk hok; simp only [Bool.not_eq_true] at hok; subst hok
       exact ⟨_, _, _, _, hk⟩)
    | (right; left; exact ⟨rfl, ‹_›, rfl⟩)
    | (right; right
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
       · first | try_rt (dsimp only; decide) | (simp [nexts, Fin.ext_iff, *]; done)
       · rfl
       · first | (intro hf; cases hf; done) | (intro; simp only at *; omega)
       · first | (intro hf; cases hf; done) | (intro _ m par a sc hw; simp_all; done)
       · first
           | (intro _ _; exact ⟨rfl, rfl, rfl⟩)
           | (intro _ hr; exact absurd hr (by try_rt ((try dsimp only); decide)))
           | (intro hs _; simp [Site.isFsum, Site.special] at hs; done)
           | (intro _ _; simp [frameT]; done)
       · first
           | (intro _ _; exact ⟨rfl, rfl⟩)
           | (intro _ hr; exact absurd hr (by try_rt ((try dsimp only); decide)))
           | (intro hs _; simp [Site.isFsum, Site.special] at hs; done)
           | (intro _ _; simp [frameR]; done))))

/-- What a step from `d` to `d'` on `e` satisfies: it stays (a failed poll), moves to the next
element of a vector store, or moves to a listed successor with the step facts. -/
abbrev StepConcl (d d' : D) (e : Event) : Prop :=
  (d' = d ∧ ∃ m par a sc, e.kind = .wait m par false a sc) ∨
    (d.site.isFst = true ∧ d.k.val < 3 ∧ d' = { d with k := d.k + 1 }) ∨ MoveFacts d d' e

/-- The steps from the states at site `s`. -/
def SuccOk (p : Params) (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ (v : V) (k : Fin 4) (e : Event) (d' : D), succ p L g ⟨s, v, k⟩ e = some (some d') →
    StepConcl ⟨s, v, k⟩ d' e

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
