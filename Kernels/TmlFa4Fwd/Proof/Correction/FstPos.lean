-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The final stores of a stage, in order

`fstPos st d` counts the elements of stage `st`'s final stores before a state of the stage's store
block, up to its two arrivals; a step into such a state is from the state before it, one store
element earlier at a store (`fstPos_succ`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The store elements of stage `st` before a state of its store block. -/
def fstPos (st : Fin 2) (d : D) : Option Nat :=
  match d.site with
  | .fld s j | .fwl s j => if s = st then some (8 * j.val) else none
  | .fst s j h => if s = st then some (8 * j.val + 4 * h.val + d.k.val) else none
  | .fence s | .fdone s _ => if s = st then some 128 else none
  | _ => none

/-- A store site of stage `st`. -/
def isFstS (st : Fin 2) : Site → Bool
  | .fst s _ _ => s == st
  | _ => false

/-- The region's sites. -/
def inFst : Site → Bool
  | .fld .. | .fwl .. | .fst .. | .fence _ | .fdone .. => true
  | _ => false

/-- The sites whose successors are checked directly. -/
private def direct : Site → Bool
  | .fld .. | .fwl .. | .fst .. | .fence _ => true
  | .fdone _ k => k == 0
  | _ => false

private theorem enter_tab : allSites.all (fun s => direct s || (nexts s).all fun s' => match s' with
    | .fld _ j => j == 0
    | s' => !inFst s') = true := by decide +kernel

variable {p : Params} {L : Launch} {g : Nat}

/-- **A step into the store block.** -/
theorem fstPos_succ {st : Fin 2} {d d' : D} {e : Event} {N : Nat}
    (hn : succ p L g d e = some (some d')) (hN : fstPos st d' = some N) :
    N = 0 ∨ ∃ M, fstPos st d = some M ∧ N = M + if isFstS st d.site then 1 else 0 := by
  by_cases hd : direct d.site = true
  · obtain ⟨site, v, k⟩ := d
    cases site <;> simp only [direct, Bool.false_eq_true, beq_iff_eq] at hd
    case fld s j =>
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp only [succ, reduceCtorEq] at hn
      rename_i tk
      cases tk <;> simp only [reduceCtorEq] at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        simp only [fstPos] at hN
        split_ifs at hN with hs
        simp only [Option.some.injEq] at hN
        exact .inr ⟨8 * j.val, by simp [fstPos, hs], by simp [isFstS, ← hN]⟩
      · simp at hn
    case fwl s j =>
      simp only [succ, Option.some.injEq] at hn
      subst hn
      simp only [fstPos] at hN
      split_ifs at hN with hs
      simp only [Option.some.injEq] at hN
      exact .inr ⟨8 * j.val, by simp [fstPos, hs], by simp [isFstS, ← hN]⟩
    case fst s j h =>
      simp only [succ] at hn
      have hk := k.isLt
      have hh := h.isLt
      by_cases h3 : k.val < 3
      · simp only [h3, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        simp only [fstPos] at hN
        split_ifs at hN with hs
        simp only [Option.some.injEq] at hN
        have hk1 : (k + 1).val = k.val + 1 := by
          rw [Fin.val_add]; simp; omega
        exact .inr ⟨_, by simp only [fstPos, hs, ↓reduceIte]; rfl, by
          simp only [isFstS, hs, beq_self_eq_true, ↓reduceIte]; omega⟩
      · simp only [h3, ↓reduceIte] at hn
        by_cases h0 : h.val = 0
        · simp only [h0, ↓reduceIte, Option.some.injEq] at hn
          subst hn
          simp only [fstPos] at hN
          split_ifs at hN with hs
          simp only [Option.some.injEq] at hN
          exact .inr ⟨_, by simp only [fstPos, hs, ↓reduceIte]; rfl, by
            simp only [isFstS, hs, beq_self_eq_true, ↓reduceIte]
            simp at hN
            omega⟩
        · simp only [h0, ↓reduceIte] at hn
          by_cases h15 : j.val = 15
          · simp only [h15, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            simp only [fstPos] at hN
            split_ifs at hN with hs
            simp only [Option.some.injEq] at hN
            exact .inr ⟨_, by simp only [fstPos, hs, ↓reduceIte]; rfl, by
              simp only [isFstS, hs, beq_self_eq_true, ↓reduceIte]; omega⟩
          · simp only [h15, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            simp only [fstPos] at hN
            split_ifs at hN with hs
            simp only [Option.some.injEq] at hN
            have hj := j.isLt
            have hj1 : (j + 1).val = j.val + 1 := by rw [Fin.val_add]; simp; omega
            exact .inr ⟨_, by simp only [fstPos, hs, ↓reduceIte]; rfl, by
              simp only [isFstS, hs, beq_self_eq_true, ↓reduceIte]; omega⟩
    case fence s =>
      simp only [succ, Option.some.injEq] at hn
      subst hn
      simp only [fstPos] at hN
      split_ifs at hN with hs
      exact .inr ⟨128, by simp [fstPos, hs], by simp [isFstS]; simpa using hN.symm⟩
    case fdone s kk =>
      subst hd
      simp only [succ, Option.some.injEq] at hn
      subst hn
      simp only [fstPos] at hN
      split_ifs at hN with hs
      exact .inr ⟨128, by simp [fstPos, hs], by simp [isFstS]; simpa using hN.symm⟩
  · rcases succ_cases hn with ⟨rfl, -⟩ | ⟨hf, -⟩ | hM
    · refine .inr ⟨N, hN, ?_⟩
      have : isFstS st d'.site = false := by
        revert hd
        cases d'.site <;> simp [direct, isFstS]
      rw [this]
      simp
    · exfalso
      revert hd hf
      cases d.site <;> simp [direct, Site.isFst]
    · left
      have h1 := List.all_eq_true.mp enter_tab d.site (mem_allSites _)
      simp only [hd, Bool.false_or] at h1
      have h2 := List.all_eq_true.mp h1 d'.site hM.1
      obtain ⟨site, v, k⟩ := d'
      cases site <;> simp [inFst] at h2 <;> simp [fstPos] at hN
      obtain ⟨-, rfl⟩ := hN
      rw [h2]
      rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
