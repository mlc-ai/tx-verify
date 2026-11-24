-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiPm
public import Kernels.InklingRelDecode.Proof.Thread.EpiValue
public import Kernels.InklingRelDecode.Proof.Thread.BrAll
public import Lemmas.Flow.SetpCore

@[expose] public section

/-! # The epilogue's load check holds for `f32` words

`loadOk_of_fl`: when the 64 loaded words are `f32` numbers and the reciprocal `inv_l` is an `f32`
number, the packs are of four-byte words and the products have outcomes (`D.loadOk`). The packs
read the loaded words (`valueOf_o`) and `inv_l` (register 1761); the products are those of the
pair `(inv_l, inv_l)` (`valueOf_cpair`) with the packed pairs (`valueOf_pack`), which
`floatE_mulI_fin` evaluates. `prm_inv_fl`: when the row sum the softmax region leaves reads as an
`f32` number, the reciprocal is an `f32` number (the zero test selects `1.0` for a zero sum). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

/-- `inv_l` is register 1761. -/
theorem valueOf_inv (d : D) : valueOf d 1761 = d.pr.inv := by
  have : (d.scalars).lookup 1761 = some d.pr.inv := rfl
  simp [valueOf, D.table, lookup_append', this]

/-- **The load check holds for `f32` words and an `f32` reciprocal.** -/
theorem loadOk_of_fl (d : D) (hc : ∀ k < 64, ∃ c, d.o.getD k (b32 0) = fl c) {y : ℝ}
    (hy : d.pr.inv = fl y) : d.loadOk = true := by
  unfold D.loadOk
  simp only [Bool.and_eq_true]
  constructor
  · unfold packsOk
    rw [List.all_eq_true]
    intro p hp
    simp only [packsAll, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton] at hp
    rcases hp with ⟨q, hq, rfl⟩ | rfl
    · obtain ⟨c0, h0⟩ := hc (2 * q) (by omega)
      obtain ⟨c1, h1⟩ := hc (2 * q + 1) (by omega)
      have e0 := valueOf_o d (k := 2 * q) (by omega)
      have e1 := valueOf_o d (k := 2 * q + 1) (by omega)
      rw [show 1763 + (2 * q + 1) = 1764 + 2 * q by omega] at e1
      simp only [e0, e1, h0, h1, fl]
      rfl
    · simp only [valueOf_inv, hy, fl]
      rfl
  · unfold mulsOkC
    rw [List.all_eq_true]
    intro m hm
    obtain ⟨q, hq, rfl⟩ := mulsAll_src m hm
    obtain ⟨c0, h0⟩ := hc (2 * q) (by omega)
    obtain ⟨c1, h1⟩ := hc (2 * q + 1) (by omega)
    have hcp : d.pr.cpair = .pair (fl y) (fl y) := by
      simp [Prm.cpair, hy, joinValue, fl]
    have hj : joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)) =
        .pair (fl c0) (fl c1) := by
      rw [h0, h1]
      simp [joinValue, fl]
    simp only [valueOf_cpair, valueOf_pack d hq, hcp, hj]
    rw [floatE_mulI_fin (x0 := y) (x1 := y) (y0 := c0) (y1 := c1)
      (by simp [fl, splitValue, valFloat_float]) (by simp [fl, splitValue, valFloat_float])
      (by simp [fl, splitValue, valFloat_float]) (by simp [fl, splitValue, valFloat_float])]
    rfl

/-- **The reciprocal is an `f32` number** when the row sum reads as one. -/
theorem prm_inv_fl (i : Br.In) {x : ℝ} (hx : valFloat .f32 i.l = .ok x) :
    ∃ y, (Br.prm i).inv = fl y := by
  have h3 : setpE (.unord .eq) false i.l zero32 =
      .ok (erealCompare .eq (x : EReal) ((0 : ℝ) : EReal)) :=
    setpE_fin (Or.inr rfl) hx valFloat_zero
  have he : (Br.prm i).eq0 = decide (x = 0) := by
    show i.eq0 = _
    simp only [Br.In.eq0, h3, erealCompare, EReal.coe_eq_coe_iff]
  by_cases h0 : x = 0
  · have hE : (Br.prm i).eq0 = true := by simp [he, h0]
    exact ⟨_, inv_fin (Br.prm i) (x := 1) (by simp only [hE, ite_true]; exact valFloat_one)
      one_ne_zero⟩
  · have hE : (Br.prm i).eq0 = false := by simp [he, h0]
    exact ⟨_, inv_fin (Br.prm i) (x := x)
      (by simp only [hE, Bool.false_eq_true, ite_false]; exact hx) h0⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
