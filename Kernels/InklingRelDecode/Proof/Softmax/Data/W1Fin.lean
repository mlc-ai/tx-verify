-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Bias
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Kinds

@[expose] public section

/-! # The first window's word on the paths without a mask

On the path that skips the bias (`pick96`) register 1520 at pc 1838 is the maximum of the scores;
on the path that adds the bias without a mask (`pick97`) it is the maximum of the biased scores. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

theorem vP_bias {V : Nat → Value} {x : Nat} (h1 : 1916 ≤ x) (h2 : x < 1948) : vP V x = V x :=
  V'_pass runP runP_ok (by decide +kernel) V h1 h2

theorem vP_score {V : Nat → Value} {x : Nat} (h1 : 2447 ≤ x) (h2 : x < 2479) : vP V x = V x :=
  V'_pass runP runP_ok (by decide +kernel) V h1 h2

theorem vP_step {V : Nat → Value} : vP V 1960 = V 1960 :=
  V'_pass runP runP_ok (lo := 1960) (hi := 1961) (by decide +kernel) V (by omega) (by omega)

theorem vT_score {W : Nat → Value} {x : Nat} (h1 : 2447 ≤ x) (h2 : x < 2479) :
    runT.V' W x = W x :=
  V'_pass runT runT_ok (by decide +kernel) W h1 h2

theorem fin96 {V : Nat → Value} {xs : Nat → EReal}
    (h : PairsEv V xs) (h96 : pick96 V = true) : Ev (vFin V 1520) (maxOf xs 64) := by
  have : vFin V 1520 = runM.V' (vP V) 1520 := by simp [vFin, h96, vS]
  rw [this]
  exact m_exact fun r h1 h2 => by rw [vP_score h1 h2]; exact h r h1 h2

theorem biasIn_vP {V : Nat → Value} {S β : Nat → ℝ} {isc : ℝ} (h : BiasIn V S β isc) :
    BiasIn (vP V) S β isc :=
  { score := fun r h1 h2 => by rw [vP_score h1 h2]; exact h.score r h1 h2
    lo := fun r h1 h2 => by rw [vP_bias h1 h2]; exact h.lo r h1 h2
    hi := fun r h1 h2 => by rw [vP_bias h1 h2]; exact h.hi r h1 h2
    step := by rw [vP_step]; exact h.step }

theorem fin97 {V : Nat → Value} {S β : Nat → ℝ} {isc : ℝ} (h : BiasIn V S β isc)
    (h96 : pick96 V = false) (h97 : pick97 V = true) :
    Ev (vFin V 1520) (maxOf (fun j => ((biased S β isc j : ℝ) : EReal)) 64) := by
  have : vFin V 1520 = runM.V' (runT.V' (vA V)) 1520 := by simp [vFin, h96, h97, vU]
  rw [this]
  exact m_exact fun r h1 h2 => by rw [vT_score h1 h2]; exact a_exact (biasIn_vP h) r h1 h2

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
