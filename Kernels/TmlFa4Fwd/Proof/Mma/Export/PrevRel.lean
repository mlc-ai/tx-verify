-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Pred
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unnecessarySeqFocus false

@[expose] public section

/-! # The site before a K/V release, a PV MMA and a PV block's poll

The release of a K slot follows the S-full commit of stage 1 (`.ce 2`, `.ce 6`), the release of a
V slot the PV block of stage 1 (`.ce 4`, `.ce 9`), or an election the lane lost; a PV MMA of step
`j ≠ 0` the step `j - 1`, step 6 the block's poll, which follows step 5 (`rel_pred`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- The sites this file gives the predecessors of. -/
def relSite : Mma.Site → Bool
  | .pv _ j => j != 0
  | .mw _ _ => true
  | .ce c => c == 2 || c == 4 || c == 6 || c == 9
  | _ => false

/-- The event is an election the lane lost. -/
def LostEl (L : Launch) (g : Nat) (e : Event) : Prop :=
  ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g ≠ ld

/-- A predecessor of such a site. -/
def RelOf (L : Launch) (g : Nat) (d : Mma.D) (e : Event) (s : Mma.Site) : Prop :=
  match s with
  | .pv b j => (j = 6 ∧ d.site = .mw b true) ∨
      (j ≠ 6 ∧ ∃ j' : Fin 8, j'.val + 1 = j.val ∧ d.site = .pv b j')
  | .mw b ld => d.site = .mw b ld ∨ (ld = true ∧ d.site = .pv b 5) ∨ (ld = false ∧ LostEl L g e)
  | .ce c => LostEl L g e ∨ (c = 2 ∧ d.site = .cm 1) ∨ (c = 6 ∧ d.site = .cm 5) ∨
      ∃ b, Mma.pvDone b = .ce c ∧ (d.site = .pv b 7 ∨ d.site = .mw b false)
  | _ => True

theorem qkDone_np2 (b : Fin 4) : relSite (Mma.qkDone b) = false := by fin_cases b <;> rfl
theorem wtNext_np2 (k : Fin 10) : relSite (Mma.wtNext k) = false := by fin_cases k <;> rfl
theorem shNext_np2 (k : Fin 14) : relSite (Mma.shNext k) = false := by fin_cases k <;> rfl
theorem scanExit_np2 {l : Bool} {d : Mma.D} {gx cur : BitVec 64} :
    relSite (Mma.scanExit p l d gx cur).site = false := by
  unfold Mma.scanExit; split <;> rfl
theorem loopHead_np2 {l : Bool} {d : Mma.D}
    {grp acc : BitVec 64} : relSite (Mma.loopHead p L g l d grp acc).site = false := by
  unfold Mma.loopHead
  split
  · exact scanExit_np2
  · split <;> rfl
theorem afterTotal_np2 {k : Epilogue.Scan} {d : Mma.D}
    {x : BitVec 64} : relSite (Mma.afterTotal p L g k d x).site = false := by
  cases k <;> unfold Mma.afterTotal <;> dsimp only <;> split <;>
    first | exact scanExit_np2 | exact loopHead_np2
theorem afterTiles_np2 {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : relSite d'.site = false := by
  simp only [Mma.afterTiles] at h
  repeat' split at h
  all_goals (cases h <;> (try split) <;> rfl)

theorem relOf_done (b : Fin 4) {d : Mma.D} {e : Event}
    (h : d.site = .pv b 7 ∨ d.site = .mw b false) : RelOf L g d e (Mma.pvDone b) := by
  generalize hs : Mma.pvDone b = s
  cases s <;> first | trivial | exact .inr (.inr (.inr ⟨b, hs, h⟩)) | (fin_cases b <;> cases hs)

theorem relOf_ce (c : Fin 12) {d d0 : Mma.D} {e : Event} (h : d0.site = .cm c ∨ LostEl L g e)
    (hw : relSite (Mma.ceNext p L g d c).site = true) :
    RelOf L g d0 e (Mma.ceNext p L g d c).site := by
  fin_cases c
  case «1» => exact h.elim (fun h => .inr (.inl ⟨rfl, h⟩)) .inl
  case «5» => exact h.elim (fun h => .inr (.inr (.inl ⟨rfl, h⟩))) .inl
  all_goals exfalso
  all_goals simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.passStart] at hw
  all_goals (repeat' split at hw)
  all_goals simp [relSite, Mma.scAt] at hw

set_option maxHeartbeats 4000000 in
/-- **The site before a site of `relSite`.** -/
theorem rel_pred {d d' : Mma.D} {e : Event}
    (hn : Mma.succ p L g d e = some (some d')) (hw : relSite d'.site = true) :
    RelOf L g d e d'.site := by
  obtain ⟨s, v⟩ := d
  cases s
  case qk b j =>
    exfalso
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    dsimp only at hw
    split at hw
    · rw [qkDone_np2] at hw; cases hw
    · cases hw
  case eq b =>
    exfalso
    simp only [Mma.succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · cases hw
      · change relSite (Mma.qkDone b) = true at hw
        rw [qkDone_np2] at hw; cases hw
    · cases hn
  case ep b =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · simp [relSite] at hw
      · rename_i h
        simp only [h, ↓reduceIte]
        exact .inr (.inr ⟨rfl, m, inst, ld, heq, h⟩)
    · cases hn
  case ce c =>
    simp only [Mma.succ] at hn
    split at hn
    · rename_i m inst ld heq
      simp only [Option.some.injEq] at hn
      subst hn
      split at hw
      · simp [relSite] at hw
      · rename_i h
        simp only [h, ↓reduceIte]
        exact relOf_ce c (.inr ⟨m, inst, ld, heq, h⟩) hw
    · cases hn
  case cm c =>
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    exact relOf_ce c (.inl rfl) hw
  case pv b j =>
    simp only [Mma.succ, Option.some.injEq] at hn
    subst hn
    dsimp only
    split
    · rename_i h
      obtain rfl : j = 5 := Fin.ext h
      exact .inr (.inl ⟨rfl, rfl⟩)
    · split
      · rename_i h
        obtain rfl : j = 7 := Fin.ext h
        exact relOf_done b (.inl rfl)
      · have hj := j.isLt
        have h1 : (j + 1 : Fin 8).val = j.val + 1 := by
          simp only [Fin.val_add, Fin.val_one]; omega
        refine .inr ⟨fun h => ?_, j, h1.symm, rfl⟩
        have := congrArg Fin.val h
        have h6 : ((6 : Fin 8) : Nat) = 6 := rfl
        omega
  case mw b ld =>
    simp only [Mma.succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split
      · dsimp only
        cases ld
        · exact relOf_done b (.inr rfl)
        · exact .inl ⟨rfl, rfl⟩
      · exact .inl rfl
    · cases hn
  case total k =>
    exfalso
    simp only [Mma.succ, Mma.word32] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals (simp only [Option.some.injEq] at hn; subst hn; rw [afterTotal_np2] at hw; cases hw)
  case tiles l =>
    exfalso
    simp only [Mma.succ] at hn
    repeat' split at hn
    all_goals first | (cases hn; done) | skip
    all_goals first
      | (simp only [Option.some.injEq] at hn; subst hn; simp [relSite, Mma.scAt] at hw; done)
      | (obtain ⟨x, hx, hx2⟩ := Option.map_eq_some_iff.mp hn
         cases hx2
         rw [afterTiles_np2 hx] at hw; cases hw)
  all_goals exfalso
  all_goals simp only [Mma.succ, Mma.word32, Mma.passStart, Option.map] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [relSite] at hw; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (rw [wtNext_np2] at hw; cases hw)
         | (rw [shNext_np2] at hw; cases hw)
         | (simp [relSite, Mma.scAt] at hw; (repeat' split at hw) <;> simp at hw))
    | skip

end
end PTX.Kernels.TmlFa4Fwd.Proof
