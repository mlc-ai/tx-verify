-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0a
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0b
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0c
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0d
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0e
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0f
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSpec

@[expose] public section

/-! # The first tile's row maximum -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- **The first tile's last wait and row maximum**: the implicit wait of the last load, the
packs of its words, the column mask (all columns valid), the selected halves and the row
maximum `rmax0V` and its test against `-∞`, to the named barrier `gen 0`, when the words are
accepted (`Max0Ok`); otherwise the thread is dead. -/
theorem step_ldW3_gen0 : StepSpec (.ldW false 3) := by
  intro P L mem0 g d t u e ins hpre hs hi h hc hf
  obtain ⟨-, hu⟩ := ldW_at hs h hc hf
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs hu hi ⊢
  subst hs
  let d0 : D := ⟨.ldW false 3, i, tt, s, m, l⟩
  have hu' : At u 1318 (factsFrom (Flow.live 1317 ++ ldRegs false 3)
      (valueEx (valueOf L g { d0 with site := .ldW false 3 }) [])) := hu
  have hseg := ((((((((((segMax0_packs (L := L) (g := g) d0).comp (SegD.of_seg ((segMax0_1334 (L :=
    L) (g := g) hpre d0).comp (segMax0_1337 (L := L) (g := g) d0)))).comp (segMax0_1341 (L := L) (g
    := g) d0)).comp (SegD.of_seg (segMax0_1452 (L := L) (g := g) d0))).comp (segMax0_1455 (L := L)
    (g := g) d0)).comp (SegD.of_seg (segMax0_1566 (L := L) (g := g) d0))).comp (segMax0_1569 (L :=
    L) (g := g) d0)).comp (SegD.of_seg (segMax0_1680 (L := L) (g := g) d0))).comp (segMax0_1683 (L
    := L) (g := g) d0)).comp (segMax0_1860 (L := L) (g := g) d0)).of_len (n := 544)
    rfl
  refine step_of_segD (d' := ⟨.gen 0, i, tt, half s, rmax0V s, l⟩) (C := Max0Ok L g d0)
    (fun hC => by
      have h' : WaitOk L g false 3 d0 := waitOk_max0.mpr hC
      simp only [next, d0, h', ite_true]; rfl)
    (fun hC => by
      have h' : ¬ WaitOk L g false 3 d0 := mt waitOk_max0.mp hC
      simp only [next, d0, h', ite_false])
    (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
    (hseg.iff (by simp only [Max0Ok, and_true, and_assoc]; exact Iff.rfl)) hu'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
