-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MExact
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Run

@[expose] public section

/-! # Pairs of exact words

`PE v x y`: the 64-bit pair `v` splits into the exact words of `x` and `y`. The join of two exact
words is one, and the packed fused multiply-add of exact pairs is the pair of the exact results. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

def PE (v : Value) (x y : EReal) : Prop :=
  ∃ a b, splitValue 64 v = (a, b) ∧ Ev a x ∧ Ev b y

theorem clean_ev {v : Value} {x : EReal} (h : Ev v x) : Clean v := by
  obtain ⟨rfl, hx⟩ := h
  induction x using EReal.rec with
  | bot => rw [erealValue_bot]; exact ⟨rfl, nofun, by intro w y h; cases h; decide⟩
  | top => exact absurd rfl hx
  | coe r => rw [erealValue_coe]; exact ⟨rfl, nofun, nofun⟩

theorem pe_join {a b : Value} {x y : EReal} (ha : Ev a x) (hb : Ev b y) :
    PE (joinValue a b) x y :=
  ⟨a, b, split_join_clean (clean_ev ha) (clean_ev hb), ha, hb⟩

theorem PE.read {v : Value} {x y : EReal} (h : PE v x y) : pairRead v = some (.ok (x, y)) := by
  obtain ⟨a, b, e, ha, hb⟩ := h
  exact pairRead_of_reads (by rw [e]; exact ha.read) (by rw [e]; exact hb.read)

theorem pe_fma2 {d a b c : Value} {x0 x1 y0 y1 z0 z1 : ℝ} (ha : PE a x0 x1) (hb : PE b y0 y1)
    (hc : PE c z0 z1) :
    PE (okVal d (fma2E a b c)) ((x0 * y0 + z0 : ℝ) : EReal) ((x1 * y1 + z1 : ℝ) : EReal) := by
  have e := fma2E_reads (w0 := ((x0 * y0 + z0 : ℝ) : EReal)) (w1 := ((x1 * y1 + z1 : ℝ) : EReal))
    ha.read hb.read hc.read (by rw [mulEReal_coe, Option.bind_some, addEReal_coe])
    (by rw [mulEReal_coe, Option.bind_some, addEReal_coe])
  rw [okVal_ok e]
  exact ⟨_, _, rfl, ⟨rfl, EReal.coe_ne_top _⟩, ⟨rfl, EReal.coe_ne_top _⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
