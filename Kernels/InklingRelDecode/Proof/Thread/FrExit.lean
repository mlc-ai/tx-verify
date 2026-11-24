-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FrNn
public import Kernels.InklingRelDecode.Proof.Thread.BrEmpty
public import Kernels.InklingRelDecode.Proof.Thread.DCompBase

@[expose] public section

/-!
# The bridge to the epilogue does not fault for a sum that is a number at least `0`

`DComp.exitNext` is `none` where `Br.In.NoFault` fails: `lg2.approx` of the row sum and
`fma.rn.f32 sc, mx, lg2l` have no outcome. `Br.nofault_of_row` covers a positive sum with a finite
maximum and a zero sum with the maximum `-inf`. The softmax region's invariant (`NnInv`) gives a
sum that is a number at least `0` and a maximum that is a number or `-inf`, so the combinations of
the two kinds (a positive sum with the maximum `-inf`, a zero sum with a finite maximum) have to
be covered too: `Br.noFault_of_nn`. The logarithm of a positive finite sum is a finite number, of
zero is `-inf`; the fused multiply-add of a positive finite scale, a maximum that is not `+inf`
and a logarithm that is not `+inf` is defined (`floatE_lse_ok`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX.Kernels.InklingRelDecode.Proof.Sm (ReadsAs)

noncomputable section
set_option maxRecDepth 100000

/-- **The log-sum-exp's fused multiply-add** of a positive finite scale, a maximum that is not
`+inf` and a logarithm that is not `+inf` has an outcome. -/
theorem floatE_lse_ok {sc mx c : Value} {s : ℝ} {m c' : EReal} (hs : valFloat .f32 sc = .ok s)
    (hpos : 0 < s) (hm : ReadsAs mx m) (hmt : m ≠ ⊤) (hc : ReadsAs c c') (hct : c' ≠ ⊤) :
    (floatE lseI [sc, mx, c]).toBool = true := by
  have hs0 : (s : EReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hmul : mulEReal (s : EReal) m = some ((s : EReal) * m) := by
    unfold mulEReal
    rw [ite_eq_right_iff]
    rintro (⟨h1, -⟩ | ⟨-, h2 | h2⟩)
    · exact absurd h1 hs0
    · exact absurd h2 (EReal.coe_ne_top _)
    · exact absurd h2 (EReal.coe_ne_bot _)
  have hp : (s : EReal) * m ≠ ⊤ := by
    induction m using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos (by exact_mod_cast hpos)]; exact bot_ne_top
    | coe a => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    | top => exact absurd rfl hmt
  have hadd : addEReal ((s : EReal) * m) c' = some ((s : EReal) * m + c') := by
    unfold addEReal
    rw [ite_eq_right_iff]
    rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact absurd h1 hp
    · exact absurd h2 hct
  have : floatE lseI [sc, mx, c] = .ok (erealValue .f32 ((s : EReal) * m + c')) := by
    simp only [floatE, idealVal, readEReal_of_valFloat hs, hm, hc, bindRead, hmul,
      Option.bind_some, hadd]
    simp [pure, Except.pure]
  rw [this]
  rfl

/-- A value that is `b32 0` or a payload and reads as the number `0` classifies as a zero. -/
theorem classify_zero_of {l : Value} (h : l = b32 0 ∨ ∃ x : ℝ, l = .float .f32 x)
    (hx : valFloat .f32 l = .ok 0) : ∃ sg, classify .f32 l = .ok (.zero sg) := by
  rcases h with rfl | ⟨x, rfl⟩
  · have hd : FloatFmt.f32.layout.decode 0 = some (.zero false) := by
      simp [FloatFmt.layout, Layout.decode, Layout.fieldVal]
    exact ⟨false, by simpa [b32, FloatFmt.bytes] using classify_bits (fmt := .f32) (by norm_num) hd⟩
  · have hx0 : x = 0 := by
      have : valFloat .f32 (.float .f32 x) = .ok x := valFloat_float
      rw [this] at hx
      exact Except.ok.inj hx
    subst hx0
    have hrep : FloatFmt.f32.representable 0 :=
      ⟨0, 0, (by decide +kernel : f32Value 0 = some 0), by simp⟩
    obtain ⟨q, hq, hc⟩ := classify_float_repr hrep
    have hq0 : q = 0 := by exact_mod_cast hq
    subst hq0
    exact ⟨false, by simpa [FVal.ofRat] using hc⟩

/-- **The bridge does not fault** where the scale is a positive finite number, the row sum is a
finite number at least `0` (a zero classifies as a zero datum), and the maximum reads as an
extended real that is not `+inf`. -/
theorem noFault_of_nn (i : In) {s : ℝ} (hs : valFloat .f32 i.sc = .ok s) (hpos : 0 < s) {x : ℝ}
    (hx : valFloat .f32 i.l = .ok x) (hx0 : 0 ≤ x)
    (hsh : i.l = b32 0 ∨ ∃ y : ℝ, i.l = .float .f32 y) {m : EReal} (hm : ReadsAs i.mx m)
    (hmt : m ≠ ⊤) : i.NoFault := by
  rcases hx0.lt_or_eq with hxp | hxz
  · have hg : lg2E i.l = .ok (.float .f32 (Real.logb 2 x)) := by
      unfold lg2E
      rw [readEReal_of_valFloat hx]
      have h1 : (0 : EReal) < (x : EReal) := EReal.coe_pos.mpr hxp
      simp [h1, EReal.coe_ne_top]
    have hv : i.lg2v = .float .f32 (Real.logb 2 x) := by simp [In.lg2v, hg, okVal]
    refine ⟨by rw [hg]; rfl, floatE_lse_ok hs hpos hm hmt (c' := ((Real.logb 2 x : ℝ) : EReal))
      ?_ (EReal.coe_ne_top _)⟩
    rw [hv]
    exact readEReal_of_valFloat valFloat_float
  · subst hxz
    have hr : readEReal .f32 i.l = some (.ok 0) := by simpa using readEReal_of_valFloat hx
    obtain ⟨sg, hcl⟩ := classify_zero_of hsh hx
    have hg : lg2E i.l = .ok ((FVal.inf true).toValue .f32) := lg2E_zero hcl hr
    have hv : i.lg2v = (FVal.inf true).toValue .f32 := by simp [In.lg2v, hg, okVal]
    refine ⟨by rw [hg]; rfl, floatE_lse_ok hs hpos hm hmt (c' := ⊥) ?_ bot_ne_top⟩
    rw [hv]
    exact infValue_read true

end
end PTX.Kernels.InklingRelDecode.Proof.Br

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The loop's exit does not fault** at a softmax state with the numbers `NnInv`: the bridge's
first part (`DComp.exitNext`) has an outcome. -/
theorem exitIn_noFault {L : Launch} {g : Nat} {d : Sm.D} (hI : Sm.Inv L g d)
    (hN : Sm.NnInv d) : (exitIn L g d).NoFault := by
  have hsc : valFloat .f32 (exitIn L g d).sc = .ok (d.e.sc * log2eF32) := valFloat_float
  have hpos : 0 < d.e.sc * log2eF32 :=
    mul_pos hI.ok.scalePos (by norm_num [log2eF32])
  obtain ⟨x, hx0, hx⟩ := hN.l
  obtain ⟨m, hmt, hm⟩ := hN.m
  exact Br.noFault_of_nn _ hsc hpos hx hx0 hN.lsh hm hmt

end
end PTX.Kernels.InklingRelDecode.Proof.DComp
