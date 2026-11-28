-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskC
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Fin

@[expose] public section

/-! # The first window's maximum on the masked path

On the path that adds the bias and masks, register 1520 at pc 1838 is the exact maximum of the
biased scores of the columns whose key is visible: `cO + b + c <= P`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- **The test is the key comparison** on 32-bit words that do not wrap. -/
theorem vis_iff {cO b P : ℤ} (h0 : 0 ≤ cO) (h1 : 0 ≤ b) (h2 : cO + b + 64 ≤ 2 ^ 31) (h3 : 0 ≤ P)
    (h4 : P < 2 ^ 31) {c : Nat} (hc : c < 64) : vis cO b P c = decide (cO + b + c ≤ P) := by
  unfold vis zc
  by_cases e : c = 1
  · subst e
    simp only [↓reduceIte, sg_eq (z := cO - P + b) (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  · simp only [e, ↓reduceIte, sg_eq (z := P - c - (cO + b)) (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)

theorem vB_score {W : Nat → Value} {x : Nat} (h1 : 2447 ≤ x) (h2 : x < 2479) :
    runB.V' W x = W x :=
  V'_pass runB runB_ok (by decide +kernel) W h1 h2

theorem isSub_out {r : Nat} (h : IsSub r) : r ∈ runB.outs := by
  have : ∀ r < 1067, IsSub r → r ∈ runB.outs := by decide +kernel
  exact this r (by unfold IsSub at h; omega) h

theorem pred_out {r : Nat} (h1 : 98 ≤ r) (h2 : r < 134) : r ∈ runB.outs := by
  have : ∀ r, 98 ≤ r → r < 134 → r ∈ runB.outs := by decide +kernel
  exact this r h1 h2

theorem mask_fin {V : Nat → Value} {S β : Nat → ℝ} {isc : ℝ} {cO b P : ℤ}
    (h : BiasIn V S β isc) (h96 : pick96 V = false) (h97 : pick97 V = false)
    (m : MaskIn (vA V) cO b P) :
    Ev (vFin V 1520) (maxOf (fun c => if vis cO b P c then ((biased S β isc c : ℝ) : EReal)
      else ⊥) 64) := by
  have e : vFin V 1520 = runM.V' (runT.V' (runC.V' (runB.V' (vA V)))) 1520 := by
    simp [vFin, h96, h97, vM]
  rw [e]
  have hB : PairsEv (runB.V' (vA V)) (fun c => ((biased S β isc c : ℝ) : EReal)) :=
    fun r h1 h2 => by rw [vB_score h1 h2]; exact a_exact (biasIn_vP h) r h1 h2
  have hC := mask_c (V := runB.V' (vA V)) (cO := cO) (b := b) (P := P)
    (fun r hr => (mask_b m (isSub_out hr)).2.1 hr)
    ((mask_b m (r := 1139) (by decide +kernel)).2.2 rfl)
    (fun r h1 h2 => (mask_b m (pred_out h1 h2)).1 h1 h2) hB
  exact m_exact fun r h1 h2 => by rw [vT_score h1 h2]; exact hC r h1 h2

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
