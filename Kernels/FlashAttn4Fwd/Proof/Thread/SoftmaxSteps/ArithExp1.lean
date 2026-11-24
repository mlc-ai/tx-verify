-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1a
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1b
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1c
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1d
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSpec

@[expose] public section

/-! # A loop tile's exponentials -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- **A loop tile's named barrier and exponentials**: `bar.arrive` of generation 1, then
the exponent arguments `s · scale - scale · mN` (`fma.rn.f32x2` by the scale pair), the
exponentials (`ex2.approx` and the software `exp2`), and the half-precision packs, to the
first probability store. -/
theorem step_gen1_pst : StepSpec (.gen 1) := by
  intro P L mem0 g d t u e ins hpre hs hi h hc hf
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_1)
  have hA : At t 2940 (factsAt L g 2940 ⟨.gen 1, i, tt, s, m, l⟩) :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      (facts_eq (d := ⟨.gen 1, i, tt, s, m, l⟩) rfl) ▸ h.2.2.2.2⟩
  have hr : t.regs 1017 = some (b32 (kOf L g + 3 + 4 * stOf L g)) :=
    (reg_of h (by table_decide)).trans rfl
  obtain ⟨-, rfl⟩ := fires_barArrive_reg hr (by simp only [stOf, kOf] at hk ⊢; omega)
    (by decide) (by decide) (by decide) (by rw [hpre.block]; decide) hf
  let d0 : D := ⟨.gen 1, i, tt, s, m, l⟩
  have hu' : At (PTX.next t) 2941 (factsFrom (Flow.live 2940) (valueOf L g d0)) := hA.next
  have hch := chain_seg (L := L) (g := g) exp1Pieces 2941 (valueOf L g d0)
    (chainSeg_append _ _ _ _ (exp1A_seg d0) (chainSeg_append _ _ _ _ (exp1B_seg d0)
      (chainSeg_append _ _ _ _ (exp1C_seg d0) (exp1D_seg d0))))
  have hseg : SegD kernel asms L g 353 2941 (factsFrom (Flow.live 2940) (valueOf L g d0)) 3544
      (factsAt L g 3544 ⟨.pst true 0, i, tt, s, m, l⟩) (ExpOk1 L g d0) :=
    ((hch.weaken_start fun _ h => holds_live_sub (by decide +kernel) h).weaken_end
      fun _ h => holds_live_congr (by kernel_rfl) h).iff expOk1_iff.symm
  refine step_of_segD (d' := ⟨.pst true 0, i, tt, s, m, l⟩) (C := ExpOk1 L g d0)
    (fun hC => by simp only [next, d0, hC, ite_true])
    (fun hC => by simp only [next, d0, hC, ite_false])
    (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl hseg hu'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
