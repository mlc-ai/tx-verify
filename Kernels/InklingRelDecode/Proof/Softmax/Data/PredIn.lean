-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskFin

@[expose] public section

/-! # The two predicates the first window leaves are predicates

Registers 179 and 180 are copies of the head predicates (registers 1 and 2) when the window skips
the bias, and the conjunctions of the window's tests (`runT`) on the other paths; either way the
exponent window selects on predicates. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

theorem setp_imm_pred {cmp : Cmp} {ty : DType} {d a w : Nat} {n : ℤ} {x : BitVec 64} (v : Value) :
    ∃ b, okVal v (coreF (.int ⟨.setp cmp none, ty, false, [some d], [.reg a, .imm n]⟩) [a]
      [.bits w x]) = .pred b := by
  have h : lk [a] [Value.bits w x] a = .bits w x := by simp [lk]
  refine ⟨compare cmp (ty.kind?.getD .b) ty.width (truncBits ty.width x)
    (truncBits ty.width (BitVec.ofInt 64 n)), ?_⟩
  have e : coreF (.int ⟨.setp cmp none, ty, false, [some d], [.reg a, .imm n]⟩) [a]
      [.bits w x] = .ok (.pred (compare cmp (ty.kind?.getD .b) ty.width (truncBits ty.width x)
        (truncBits ty.width (BitVec.ofInt 64 n)))) := by
    simp only [coreF, coreW, oBits, h, pure, Except.pure, bind, Except.bind]
  rw [okVal_ok e]

theorem setp_reg_pred {cmp : Cmp} {ty : DType} {d a b w1 w2 : Nat} (hab : b ≠ a)
    {x y : BitVec 64} (v : Value) :
    ∃ q, okVal v (coreF (.int ⟨.setp cmp none, ty, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [.bits w1 x, .bits w2 y]) = .pred q := by
  have h1 : lk [a, b] [Value.bits w1 x, .bits w2 y] a = .bits w1 x := by simp [lk]
  have h2 : lk [a, b] [Value.bits w1 x, .bits w2 y] b = .bits w2 y := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  refine ⟨compare cmp (ty.kind?.getD .b) ty.width (truncBits ty.width x)
    (truncBits ty.width y), ?_⟩
  have e : coreF (.int ⟨.setp cmp none, ty, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [.bits w1 x, .bits w2 y] = .ok (.pred (compare cmp (ty.kind?.getD .b) ty.width
        (truncBits ty.width x) (truncBits ty.width y))) := by
    simp only [coreF, coreW, oBits, h1, h2, pure, Except.pure, bind, Except.bind]
  rw [okVal_ok e]

theorem shr_bits {ty : DType} {d a w : Nat} {n : ℤ} {x : BitVec 64} (v : Value) :
    ∃ y, okVal v (coreF (.int ⟨.shr, ty, false, [some d], [.reg a, .imm n]⟩) [a]
      [.bits w x]) = .bits ty.width y := by
  have h : lk [a] [Value.bits w x] a = .bits w x := by simp [lk]
  simp only [coreF, coreW, oBits, h, pure, Except.pure, bind, Except.bind, okVal]
  split_ifs <;> exact ⟨_, rfl⟩

theorem and_pred {d a b : Nat} (hab : b ≠ a) (p q : Bool) (v : Value) :
    okVal v (coreF (.int ⟨.and, .pred, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [.pred p, .pred q]) = .pred (p && q) := by
  have h1 : lk [a, b] [Value.pred p, .pred q] a = .pred p := by simp [lk]
  have h2 : lk [a, b] [Value.pred p, .pred q] b = .pred q := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have e : coreF (.int ⟨.and, .pred, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [.pred p, .pred q] = .ok (.pred (p && q)) := by
    simp only [coreF, coreW, logicW, oPred, h1, h2, DType.width, ↓reduceIte, pure, Except.pure,
      bind, Except.bind]
  rw [okVal_ok e]

theorem runT_preds {W : Nat → Value} (h1901 : ∃ w x, W 1901 = .bits w x)
    (h1912 : ∃ w x, W 1912 = .bits w x) (h484 : ∃ w x, W 484 = .bits w x) :
    (∃ q, Gen.w1t_v1762 W = .pred q) ∧ ∃ q, Gen.w1t_v1763 W = .pred q := by
  obtain ⟨w1, x1, e1⟩ := h1901
  obtain ⟨w2, x2, e2⟩ := h1912
  obtain ⟨w3, x3, e3⟩ := h484
  obtain ⟨y, e58⟩ : ∃ y, Gen.w1t_v1758 W = .bits 32 y := by
    unfold Gen.w1t_v1758; rw [e2]; exact shr_bits _
  obtain ⟨p9, e59⟩ : ∃ q, Gen.w1t_v1759 W = .pred q := by
    unfold Gen.w1t_v1759; rw [e58, e3]; exact setp_reg_pred (by decide) _
  obtain ⟨p0, e60⟩ : ∃ q, Gen.w1t_v1760 W = .pred q := by
    unfold Gen.w1t_v1760; rw [e58]; exact setp_imm_pred _
  have e61 : ∃ q, Gen.w1t_v1761 W = .pred q := by
    unfold Gen.w1t_v1761; rw [e59, e60]; exact ⟨_, and_pred (by decide) _ _ _⟩
  obtain ⟨q1, e61⟩ := e61
  constructor
  · obtain ⟨p7, e57⟩ : ∃ q, Gen.w1t_v1757 W = .pred q := by
      unfold Gen.w1t_v1757; rw [e1]; exact setp_imm_pred _
    exact ⟨_, by unfold Gen.w1t_v1762; rw [e57, e61]; exact and_pred (by decide) _ _ _⟩
  · obtain ⟨p6, e56⟩ : ∃ q, Gen.w1t_v1756 W = .pred q := by
      unfold Gen.w1t_v1756; rw [e1]; exact setp_imm_pred _
    exact ⟨_, by unfold Gen.w1t_v1763; rw [e56, e61]; exact and_pred (by decide) _ _ _⟩


theorem mov_pred {d a : Nat} (q : Bool) (v : Value) :
    okVal v (coreF (.move ⟨.scalar, .pred, [some d], [.reg a]⟩) [a] [.pred q]) = .pred q := by
  have h : lk [a] [Value.pred q] a = .pred q := by simp [lk]
  have e : coreF (.move ⟨.scalar, .pred, [some d], [.reg a]⟩) [a] [.pred q] = .ok (.pred q) := by
    simp only [coreF, coreW, ite_true, oPred, h, pure, Except.pure, bind, Except.bind]
  rw [okVal_ok e]

theorem runT_q {W : Nat → Value} (h1901 : ∃ w x, W 1901 = .bits w x)
    (h1912 : ∃ w x, W 1912 = .bits w x) (h484 : ∃ w x, W 484 = .bits w x) :
    (∃ q, runT.V' W 179 = .pred q) ∧ ∃ q, runT.V' W 180 = .pred q := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := runT_preds h1901 h1912 h484
  constructor
  · refine ⟨a, ?_⟩
    refine V'_out runT runT_ok (P := fun r v => r = 179 → v = .pred a) (fun p hp => ?_)
      (show 179 ∈ runT.outs by decide +kernel) rfl
    change p ∈ Gen.w1t_facts1 W at hp
    simp only [Gen.w1t_facts1, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · intro _; exact ha
    · intro h; dsimp only at h; omega
  · refine ⟨b, ?_⟩
    refine V'_out runT runT_ok (P := fun r v => r = 180 → v = .pred b) (fun p hp => ?_)
      (show 180 ∈ runT.outs by decide +kernel) rfl
    change p ∈ Gen.w1t_facts1 W at hp
    simp only [Gen.w1t_facts1, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · intro h; dsimp only at h; omega
    · intro _; exact hb

/-- **The predicates the exponent window selects on** exist on every path. -/
theorem fin_q {V : Nat → Value} (h1 : ∃ q, V 1 = .pred q) (h2 : ∃ q, V 2 = .pred q)
    (hA : ∃ w x, vA V 1901 = .bits w x) (hB : ∃ w x, vA V 1912 = .bits w x)
    (hC : ∃ w x, vA V 484 = .bits w x) :
    (∃ q, vFin V 179 = .pred q) ∧ ∃ q, vFin V 180 = .pred q := by
  have n179 : (179 : Nat) ∉ runM.outs := by decide +kernel
  have n180 : (180 : Nat) ∉ runM.outs := by decide +kernel
  by_cases h96 : pick96 V = true
  · simp only [vFin, h96, ↓reduceIte, vS, V'_notin runM runM_ok _ n179,
      V'_notin runM runM_ok _ n180]
    obtain ⟨q1, e1⟩ := h1
    obtain ⟨q2, e2⟩ := h2
    constructor
    · refine ⟨q1, ?_⟩
      refine V'_out runP runP_ok (P := fun r v => r = 179 → v = .pred q1) (fun p hp => ?_)
        (show 179 ∈ runP.outs by decide +kernel) rfl
      change p ∈ Gen.w1p_facts1 V at hp
      simp only [Gen.w1p_facts1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      all_goals first
        | (intro h; dsimp only at h; omega)
        | (intro _; unfold Gen.w1p_v1300; rw [e1]; dsimp only; exact mov_pred _ _)
    · refine ⟨q2, ?_⟩
      refine V'_out runP runP_ok (P := fun r v => r = 180 → v = .pred q2) (fun p hp => ?_)
        (show 180 ∈ runP.outs by decide +kernel) rfl
      change p ∈ Gen.w1p_facts1 V at hp
      simp only [Gen.w1p_facts1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      all_goals first
        | (intro h; dsimp only at h; omega)
        | (intro _; unfold Gen.w1p_v1301; rw [e2]; dsimp only; exact mov_pred _ _)
  · by_cases h97 : pick97 V = true
    · simp only [vFin, h96, h97, vU, ↓reduceIte, V'_notin runM runM_ok _ n179,
        V'_notin runM runM_ok _ n180]
      exact runT_q hA hB hC
    · simp only [vFin, h96, h97, vM, ↓reduceIte, V'_notin runM runM_ok _ n179,
        V'_notin runM runM_ok _ n180, Bool.false_eq_true]
      refine runT_q ?_ ?_ ?_
      · rwa [V'_notin runC runC_ok _ (by decide +kernel),
          V'_notin runB runB_ok _ (by decide +kernel)]
      · rwa [V'_notin runC runC_ok _ (by decide +kernel),
          V'_notin runB runB_ok _ (by decide +kernel)]
      · rwa [V'_notin runC runC_ok _ (by decide +kernel),
          V'_notin runB runB_ok _ (by decide +kernel)]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
