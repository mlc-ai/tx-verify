-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPKeys

@[expose] public section

/-! # The registers of the probability stores

When the scale word, the reference maximum and the words are single-precision numbers, every
source register of a probability store (`tcgen05.st` at a `pst` site) holds a packed pair of
half-precision values (`pst_keys_*`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat} {d : D} {t : TState} {ta : Nat} {ss : List Opnd} (hsc : ScaleOk L)
    {x : ℝ} (hm : d.m = .float .f32 x) (hwf : WordsF32 d.w)
include hsc hm hwf

/-- The source registers of store site `pst false 0` hold packed half-precision pairs. -/
theorem pst_pairs_0 (hs : d.site = .pst false 0) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 0).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_0 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst false 1` hold packed half-precision pairs. -/
theorem pst_pairs_1 (hs : d.site = .pst false 1) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 1).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_1 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst false 2` hold packed half-precision pairs. -/
theorem pst_pairs_2 (hs : d.site = .pst false 2) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 2).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_2 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst false 3` hold packed half-precision pairs. -/
theorem pst_pairs_3 (hs : d.site = .pst false 3) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst false 3).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_3 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst true 0` hold packed half-precision pairs. -/
theorem pst_pairs_4 (hs : d.site = .pst true 0) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 0).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_4 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst true 1` hold packed half-precision pairs. -/
theorem pst_pairs_5 (hs : d.site = .pst true 1) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 1).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_5 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst true 2` hold packed half-precision pairs. -/
theorem pst_pairs_6 (hs : d.site = .pst true 2) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 2).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_6 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

/-- The source registers of store site `pst true 3` hold packed half-precision pairs. -/
theorem pst_pairs_7 (hs : d.site = .pst true 3) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[(Site.pst true 3).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := fun p hp => by
  obtain ⟨r, h1, h2⟩ := pst_keys_7 hsc hm hwf hs h hc p hp
  exact ⟨r, _, _, h1, h2⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
