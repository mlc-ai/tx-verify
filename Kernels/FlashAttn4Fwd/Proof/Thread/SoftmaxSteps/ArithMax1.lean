-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1a
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1b
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1c
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSpec

@[expose] public section

/-! # A loop tile's row maximum and lazy rescale -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- **A loop tile's last wait, row maximum and lazy rescale**: the implicit wait of the last
load, the maximum `mx` of the reference maximum and the scores, its test against `-∞`,
`gap = sc · (m - mx)` and `2 ^ gap`, then the selections by `gap ≥ -8` of the new reference
maximum (`mNV`), the exponent maximum (`mExpV`) and the register of `α` (`alphaV`), to the store
of `α`. -/
theorem step_ldW3_alphaSt : StepSpec (.ldW true 3) := by
  intro P L mem0 g d t u e ins hpre hs hi h hc hf
  obtain ⟨-, hu⟩ := ldW_at hs h hc hf
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs hu hi ⊢
  subst hs
  let d0 : D := ⟨.ldW true 3, i, tt, s, m, l⟩
  have hu' : At u 2780 (factsFrom (Flow.live 2779 ++ ldRegs true 3)
      (valueEx (valueOf L g { d0 with site := .ldW true 3 }) [])) := hu
  have hseg := ((((segMax1_packs (L := L) (g := g) d0).comp (segMax1_2796 (L := L) (g := g)
    d0)).comp (segMax1_2926 (L := L) (g := g) d0)).comp
    (SegD.of_seg (segMax1_addr (L := L) (g := g) hpre d0))).of_len (n := 159) rfl
  refine step_of_segD (d' := ⟨.alphaSt, i, tt, s, m, l⟩) (C := Max1Ok L g d0)
    (fun hC => by
      have h' : WaitOk L g true 3 d0 := waitOk_max1.mpr hC
      simp only [next, d0, h', ite_true]; rfl)
    (fun hC => by
      have h' : ¬ WaitOk L g true 3 d0 := mt waitOk_max1.mp hC
      simp only [next, d0, h', ite_false])
    (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
    (hseg.iff (by simp only [Max1Ok, and_true, and_assoc]; exact Iff.rfl)) hu'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
