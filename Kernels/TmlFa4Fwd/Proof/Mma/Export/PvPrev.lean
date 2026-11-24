-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Prev
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unnecessarySeqFocus false

@[expose] public section

/-! # The site before a PV MMA and the first QK MMA of a block

PV step 0 follows its block's election, step 6 the poll of the second P-full barrier, which the lane
that issues the block repeats after step 5, and any other step the one before; QK step 0 follows its
block's election (`pred_pv`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- The sites this file gives the predecessors of. -/
def pvSite : Mma.Site → Bool
  | .pv _ _ => true
  | .mw _ l => l
  | .qk _ j => j == 0
  | _ => false

/-- A predecessor of such a site. -/
def PvPrevOf (d : Mma.D) (e : Event) (s : Mma.Site) : Prop :=
  match s with
  | .pv b j => (j = 0 ∧ d.site = .ep b ∧ ∃ mk inst ld, e.kind = .elect mk inst ld) ∨
      (j = 6 ∧ d.site = .mw b true ∧ ∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      ∃ j' : Fin 8, j'.val + 1 = j.val ∧ j ≠ 6 ∧ d.site = .pv b j'
  | .mw b true => d.site = .pv b 5 ∨
      (d.site = .mw b true ∧ ∃ l q ok acq sc, e.kind = .wait l q ok acq sc)
  | .qk _ 0 => ∃ mk inst ld, e.kind = .elect mk inst ld
  | _ => True

theorem pvDone_nv (b : Fin 4) : pvSite (Mma.pvDone b) = false := by fin_cases b <;> rfl
theorem wtNext_nv (k : Fin 10) : pvSite (Mma.wtNext k) = false := by fin_cases k <;> rfl
theorem shNext_nv (k : Fin 14) : pvSite (Mma.shNext k) = false := by fin_cases k <;> rfl
theorem scanExit_nv {l : Bool} {d : Mma.D} {gx cur : BitVec 64} :
    pvSite (Mma.scanExit p l d gx cur).site = false := by
  unfold Mma.scanExit; split <;> rfl
theorem loopHead_nv {l : Bool} {d : Mma.D}
    {grp acc : BitVec 64} : pvSite (Mma.loopHead p L g l d grp acc).site = false := by
  unfold Mma.loopHead
  split
  · exact scanExit_nv
  · split <;> rfl
theorem afterTotal_nv {k : Epilogue.Scan} {d : Mma.D}
    {x : BitVec 64} : pvSite (Mma.afterTotal p L g k d x).site = false := by
  cases k <;> unfold Mma.afterTotal <;> dsimp only <;> split <;>
    first | exact scanExit_nv | exact loopHead_nv
theorem afterTiles_nv {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : pvSite d'.site = false := by
  simp only [Mma.afterTiles] at h
  repeat' split at h
  all_goals (cases h <;> (try split) <;> rfl)
theorem ceNext_nv {d : Mma.D} (c : Fin 12) :
    pvSite (Mma.ceNext p L g d c).site = false := by
  fin_cases c <;> simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.passStart] <;>
    ((repeat' split) <;> rfl)

theorem qkDone_nv (b : Fin 4) : pvSite (Mma.qkDone b) = false := by fin_cases b <;> rfl

set_option maxHeartbeats 4000000 in
/-- **The site before a site of `pvSite`.** -/
theorem pred_pv {d d' : Mma.D} {e : Event}
    (hn : Mma.succ p L g d e = some (some d')) (hw : pvSite d'.site = true) :
    PvPrevOf d e d'.site := by
  obtain ⟨s, v⟩ := d
  cases s
  case qk b j =>
    exfalso
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    dsimp only at hw
    split at hw
    · rw [qkDone_nv] at hw; cases hw
    · rename_i h
      have : ∀ j : Fin 8, j.val ≠ 7 → (j + 1 == 0) = false := by decide
      simp [pvSite, this j h] at hw
  case eq b =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · rename_i h
        simp only [h, ↓reduceIte]
        exact ⟨m, inst, ld, heq⟩
      · rw [qkDone_nv] at hw; cases hw
    · cases hn
  case ep b =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · rename_i h
        simp only [h, ↓reduceIte]
        exact .inl ⟨rfl, rfl, m, inst, ld, heq⟩
      · simp [pvSite] at hw
    · cases hn
  case ce c =>
    exfalso
    simp only [Mma.succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · cases hw
      · rw [ceNext_nv c] at hw; cases hw
    · cases hn
  case cm c =>
    exfalso
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    rw [ceNext_nv c] at hw; cases hw
  case pv b j =>
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    dsimp only at hw ⊢
    by_cases h5 : j.val = 5
    · obtain rfl : j = 5 := Fin.ext h5
      exact .inl rfl
    · simp only [h5, ↓reduceIte] at hw ⊢
      by_cases h7 : j.val = 7
      · simp only [h7, ↓reduceIte] at hw
        rw [pvDone_nv] at hw; cases hw
      · simp only [h7, ↓reduceIte]
        have key : ∀ j : Fin 8, j.val ≠ 5 → j.val ≠ 7 → j.val + 1 = (j + 1).val ∧ j + 1 ≠ 6 := by
          decide
        exact .inr (.inr ⟨j, (key j h5 h7).1, (key j h5 h7).2, rfl⟩)
  case mw b l =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i lo q ok acq sc heq
      simp only [Option.some.injEq] at hn
      subst hn
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
        cases l
        · cases hw
        · exact .inr ⟨rfl, _, _, _, _, _, heq⟩
      · simp only [↓reduceIte] at hw ⊢
        cases l
        · change pvSite (Mma.pvDone b) = true at hw
          rw [pvDone_nv] at hw; cases hw
        · exact .inr (.inl ⟨rfl, rfl, _, _, _, _, _, heq⟩)
    · cases hn
  case total k =>
    exfalso
    simp only [Mma.succ, Mma.word32] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals (simp only [Option.some.injEq] at hn; subst hn; rw [afterTotal_nv] at hw; cases hw)
  case tiles l =>
    exfalso
    simp only [Mma.succ, Mma.word32] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals first
      | (simp only [Option.some.injEq] at hn; subst hn; simp [pvSite, Mma.scAt] at hw; done)
      | (obtain ⟨x, hx, hx2⟩ := Option.map_eq_some_iff.mp hn
         cases hx2
         rw [afterTiles_nv hx] at hw; cases hw)
  all_goals exfalso
  all_goals simp only [Mma.succ, Mma.word32, Mma.passStart, Option.map] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [pvSite] at hw; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (rw [wtNext_nv] at hw; cases hw)
         | (rw [shNext_nv] at hw; cases hw)
         | (simp [pvSite, Mma.scAt] at hw; (repeat' split at hw) <;> simp at hw))
    | skip

end
end PTX.Kernels.TmlFa4Fwd.Proof
