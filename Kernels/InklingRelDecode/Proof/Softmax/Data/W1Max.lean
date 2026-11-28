-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Pair

@[expose] public section

/-! # The first window's maximum on exact scores

The last run of the first window (`runM`) takes the maximum of the 64 scores of the 32 pairs
(registers 2447 to 2478). When each score is the exact word of `xs i` (no `+inf`), register 1520
is the exact word of the maximum. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

theorem ev_max2 {d a b : Value} {x y : EReal} (ha : Ev a x) (hb : Ev b y) :
    Ev (okVal d (maxE [a, b])) (max x y) := by
  have e : maxE [a, b] = pure (erealValue .f32 (max x y)) := by
    unfold maxE
    simp only [idealMax, ha.read, hb.read, bindRead]
  rw [e]
  exact ⟨rfl, ne_top_max ha.2 hb.2⟩

/-- The pairs the maximum reads: the exact words of `xs`. -/
def PairsEv (W : Nat → Value) (xs : Nat → EReal) : Prop :=
  ∀ r, 2447 ≤ r → r < 2479 → PE (W r) (xs (2 * (r - 2447))) (xs (2 * (r - 2447) + 1))

theorem ev_of_eq {v : Value} {x y : EReal} (h : Ev v x) (e : x = y) : Ev v y := e ▸ h

/-- The maximum of the first `n` scores. -/
def maxOf (xs : Nat → EReal) (n : Nat) : EReal := (Finset.range n).sup xs

theorem leaf1 {W : Nat → Value} {xs : Nat → EReal} (h : PairsEv W xs) {r : Nat}
    (h1 : 2447 ≤ r) (h2 : r < 2479) :
    Ev (splitValue 64 (W r)).1 (xs (2 * (r - 2447))) := by
  obtain ⟨a, b, e, ha, hb⟩ := h r h1 h2
  rw [e]
  exact ha

theorem leaf2 {W : Nat → Value} {xs : Nat → EReal} (h : PairsEv W xs) {r : Nat}
    (h1 : 2447 ≤ r) (h2 : r < 2479) :
    Ev (splitValue 64 (W r)).2 (xs (2 * (r - 2447) + 1)) := by
  obtain ⟨a, b, e, ha, hb⟩ := h r h1 h2
  rw [e]
  exact hb

theorem m_exact {W : Nat → Value} {xs : Nat → EReal} (h : PairsEv W xs) :
    Ev (runM.V' W 1520) (maxOf xs 64) := by
  show Ev (Gen.w1m_v1837 W) _
  obtain ⟨x, hx, e⟩ : ∃ x, Ev (Gen.w1m_v1837 W) x ∧ x = maxOf xs 64 :=
    ⟨_, by
    repeat' first
      | (apply leaf1 h <;> omega)
      | (apply leaf2 h <;> omega)
      | apply ev_max3 | apply ev_max2, by
    refine le_antisymm ?_ (Finset.sup_le fun i hi => ?_)
    · simp only [maxOf, max_le_iff]
      repeat' constructor
      all_goals exact Finset.le_sup (f := xs) (Finset.mem_range.2 (by norm_num))
    · have : i < 64 := Finset.mem_range.1 hi
      interval_cases i <;> simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, le_max_iff,
        le_refl, true_or, or_true]⟩
  exact e ▸ hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
