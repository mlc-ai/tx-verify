-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Pred
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unnecessarySeqFocus false

@[expose] public section

/-! # The site before a commit, a QK MMA and a QK block's end

A commit follows its election, the second Q commit's election the first Q commit, a QK MMA of step
`j ≠ 0` the block's step `j - 1`, and the site after a QK block its last MMA; the elections among
these may be ones the lane lost (`pred_site`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- The sites this file gives the predecessors of. -/
def prevSite : Mma.Site → Bool
  | .qk _ j => j != 0
  | .cm _ => true
  | .ce c => c == 0 || c == 1 || c == 3 || c == 5 || c == 8
  | _ => false

/-- A predecessor of such a site. -/
def PrevOf (L : Launch) (g : Nat) (d : Mma.D) (e : Event) (s : Mma.Site) : Prop :=
  match s with
  | .qk b j => ∃ j' : Fin 8, j'.val + 1 = j.val ∧ d.site = .qk b j'
  | .cm c => d.site = .ce c
  | .ce c => (∃ b, Mma.qkDone b = .ce c ∧ d.site = .qk b 7) ∨ (c = 8 ∧ d.site = .cm 7) ∨
      ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g ≠ ld
  | _ => True

theorem pvDone_np (b : Fin 4) : prevSite (Mma.pvDone b) = false := by fin_cases b <;> rfl
theorem wtNext_np (k : Fin 10) : prevSite (Mma.wtNext k) = false := by fin_cases k <;> rfl
theorem shNext_np (k : Fin 14) : prevSite (Mma.shNext k) = false := by fin_cases k <;> rfl
theorem scanExit_np {l : Bool} {d : Mma.D} {gx cur : BitVec 64} :
    prevSite (Mma.scanExit p l d gx cur).site = false := by
  unfold Mma.scanExit; split <;> rfl
theorem loopHead_np {l : Bool} {d : Mma.D}
    {grp acc : BitVec 64} : prevSite (Mma.loopHead p L g l d grp acc).site = false := by
  unfold Mma.loopHead
  split
  · exact scanExit_np
  · split <;> rfl
theorem afterTotal_np {k : Epilogue.Scan} {d : Mma.D}
    {x : BitVec 64} : prevSite (Mma.afterTotal p L g k d x).site = false := by
  cases k <;> unfold Mma.afterTotal <;> dsimp only <;> split <;>
    first | exact scanExit_np | exact loopHead_np
theorem afterTiles_np {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : prevSite d'.site = false := by
  simp only [Mma.afterTiles] at h
  repeat' split at h
  all_goals (cases h <;> (try split) <;> rfl)
theorem ceNext_np {d : Mma.D} (c : Fin 12) (hc : c ≠ 7) :
    prevSite (Mma.ceNext p L g d c).site = false := by
  fin_cases c <;> simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.passStart] <;>
    first | exact absurd rfl hc | ((repeat' split) <;> rfl)

theorem prevOf_done (b : Fin 4) {d : Mma.D} {e : Event}
    (h : d.site = .qk b 7 ∨ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g ≠ ld) :
    PrevOf L g d e (Mma.qkDone b) := by
  have h' := h.imp_left fun h =>
    (⟨b, rfl, h⟩ : ∃ b', Mma.qkDone b' = Mma.qkDone b ∧ d.site = .qk b' 7)
  revert h'
  generalize hs : Mma.qkDone b = s
  intro h'
  cases s <;> first | trivial | exact h'.imp_right .inr | (fin_cases b <;> cases hs)

set_option maxHeartbeats 4000000 in
/-- **The site before a site of `prevSite`.** -/
theorem pred_site {d d' : Mma.D} {e : Event}
    (hn : Mma.succ p L g d e = some (some d')) (hw : prevSite d'.site = true) :
    PrevOf L g d e d'.site := by
  obtain ⟨s, v⟩ := d
  cases s
  case qk b j =>
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    dsimp only
    split
    · rename_i h
      obtain rfl : j = 7 := Fin.ext h
      exact prevOf_done b (.inl rfl)
    · exact ⟨j, by have := j.isLt; simp only [Fin.val_add, Fin.val_one]; omega, rfl⟩
  case eq b =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · simp [prevSite] at hw
      · rename_i h
        simp only [h, ↓reduceIte]
        exact prevOf_done b (.inr ⟨m, inst, ld, heq, h⟩)
    · cases hn
  case ce c =>
    simp only [Mma.succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · rename_i h
        simp only [h, ↓reduceIte]
        rfl
      · rename_i m inst ld heq h
        by_cases hc : c = 7
        · subst hc
          simp only [h, ↓reduceIte]
          exact .inr (.inr ⟨m, inst, ld, heq, h⟩)
        · rw [ceNext_np c hc] at hw; cases hw
    · cases hn
  case cm c =>
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    by_cases hc : c = 7
    · subst hc
      exact .inr (.inl ⟨rfl, rfl⟩)
    · rw [ceNext_np c hc] at hw; cases hw
  case pv b j =>
    exfalso
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    dsimp only at hw
    (repeat' split at hw)
    · cases hw
    · rw [pvDone_np] at hw; cases hw
    · cases hw
  case mw b ld =>
    exfalso
    simp only [Mma.succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      (repeat' split at hw)
      · cases hw
      · change prevSite (Mma.pvDone b) = true at hw
        rw [pvDone_np] at hw; cases hw
      · cases hw
    · cases hn
  case total k =>
    exfalso
    simp only [Mma.succ, Mma.word32] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals (simp only [Option.some.injEq] at hn; subst hn; rw [afterTotal_np] at hw; cases hw)
  case tiles l =>
    exfalso
    simp only [Mma.succ] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals first
      | (simp only [Option.some.injEq] at hn; subst hn; simp [prevSite, Mma.scAt] at hw; done)
      | (obtain ⟨x, hx, hx2⟩ := Option.map_eq_some_iff.mp hn
         cases hx2
         rw [afterTiles_np hx] at hw; cases hw)
  all_goals exfalso
  all_goals simp only [Mma.succ, Mma.word32, Mma.passStart, Option.map] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [prevSite] at hw; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (rw [wtNext_np] at hw; cases hw)
         | (rw [shNext_np] at hw; cases hw)
         | (simp [prevSite, Mma.scAt] at hw; (repeat' split at hw) <;> simp at hw))
    | skip

end
end PTX.Kernels.TmlFa4Fwd.Proof
