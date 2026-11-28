-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Max
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpWindow

@[expose] public section

/-! # The bias run on exact scores

The bias run of the first window (`runA`, pcs 1303 to 1465) adds the bias to the score pairs:
score pair `2447 + i` becomes `bias * (1 / scale) + S` on its two columns, the bias halves of the
pack `1916 + i` widened from `bf16`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- **What the bias run reads, exactly**: the scores `S`, the biases `β` (as `bf16` halves of the
packs) and the reciprocal `isc` of the scale. -/
structure BiasIn (V : Nat → Value) (S β : Nat → ℝ) (isc : ℝ) : Prop where
  score : ∀ r, 2447 ≤ r → r < 2479 →
    PE (V r) ((S (2 * (r - 2447)) : ℝ) : EReal) ((S (2 * (r - 2447) + 1) : ℝ) : EReal)
  lo : ∀ r, 1916 ≤ r → r < 1948 →
    readEReal .bf16 (splitValue 32 (V r)).1 = some (.ok ((β (2 * (r - 1916)) : ℝ) : EReal))
  hi : ∀ r, 1916 ≤ r → r < 1948 →
    readEReal .bf16 (splitValue 32 (V r)).2 = some (.ok ((β (2 * (r - 1916) + 1) : ℝ) : EReal))
  step : PE (V 1960) (isc : EReal) (isc : EReal)

theorem BiasIn.lo' {V S β isc} (h : BiasIn V S β isc) {r : Nat} (h1 : 1916 ≤ r) (h2 : r < 1948) :
    readEReal .bf16 (splitValue 32 (V r)).1 = some (.ok ((β (2 * (r - 1916)) : ℝ) : EReal)) :=
  h.lo r h1 h2

theorem BiasIn.hi' {V S β isc} (h : BiasIn V S β isc) {r : Nat} (h1 : 1916 ≤ r) (h2 : r < 1948) :
    readEReal .bf16 (splitValue 32 (V r)).2 =
      some (.ok ((β (2 * (r - 1916) + 1) : ℝ) : EReal)) :=
  h.hi r h1 h2

/-- The score of a column after the bias. -/
def biased (S β : Nat → ℝ) (isc : ℝ) (j : Nat) : ℝ := β j * isc + S j

theorem ev_widen {d h : Value} {b : ℝ}
    (e : readEReal .bf16 h = some (.ok (b : EReal))) :
    Ev (okVal d (Softmax.widenBfE [h])) (b : EReal) := by
  have : Softmax.widenBfE [h] = .ok (erealValue .f32 (b : EReal)) := by simp [Softmax.widenBfE, e]
  rw [okVal_ok this]
  exact ⟨rfl, EReal.coe_ne_top _⟩

theorem a_exact {V : Nat → Value} {S β : Nat → ℝ} {isc : ℝ} (h : BiasIn V S β isc) :
    ∀ r, 2447 ≤ r → r < 2479 → PE (runA.V' V r) ((biased S β isc (2 * (r - 2447)) : ℝ) : EReal)
      ((biased S β isc (2 * (r - 2447) + 1) : ℝ) : EReal) := by
  intro r h1 h2
  have hm : r ∈ runA.outs := by
    have : ∀ r, 2447 ≤ r → r < 2479 → r ∈ runA.outs := by decide +kernel
    exact this r h1 h2
  refine V'_out runA runA_ok (P := fun r v => 2447 ≤ r → r < 2479 →
    PE v ((biased S β isc (2 * (r - 2447)) : ℝ) : EReal)
      ((biased S β isc (2 * (r - 2447) + 1) : ℝ) : EReal)) ?_ hm h1 h2
  intro p hp
  change p ∈ Gen.w1a_facts6 V at hp
  simp only [Gen.w1a_facts6, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals first
    | (intro h1 h2; dsimp only at h1 h2; exfalso; omega)
    | (intro _ _
       dsimp only
       refine pe_fma2 (pe_join ?_ ?_) h.step (h.score _ (by omega) (by omega))
       · apply ev_widen; apply BiasIn.lo' h <;> omega
       · apply ev_widen; apply BiasIn.hi' h <;> omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
