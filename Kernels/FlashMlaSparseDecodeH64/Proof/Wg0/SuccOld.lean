-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites

@[expose] public section

/-! # The chain of the output chunks

The site before a staging store `ost2 c j` on the block's chain is the store itself (the next
element), the store `j - 1` or, for `j = 0`, the chunk's wait (`succOk_ost2`); the site before the
wait is the chunk's load (`succOk_oldw`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof Wg0.Data

noncomputable section

theorem succOk_ost2 {c c' : Control.D} {k : Fin 4} {j : Fin 8} (h : succOk c c' = true)
    (hs : c'.site = .ost2 k j) : c.site = .ost2 k j ∨ (∃ j' : Fin 8, j'.val + 1 = j.val ∧
      c.site = .ost2 k j') ∨ (j.val = 0 ∧ c.site = .oldw k) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  case sld a k' => fin_cases k' <;> simp at h
  case pst k' => fin_cases k' <;> simp at h
  case pld k' => fin_cases k' <;> simp at h
  case ost k' => fin_cases k' <;> simp at h
  case rstw k' => fin_cases k' <;> simp at h
  case oldw => exact ⟨h.2, h.1.symm⟩
  case ost2 c1 k1 => fin_cases k1 <;> fin_cases j <;> simp_all

theorem succOk_oldw {c c' : Control.D} {k : Fin 4} (h : succOk c c' = true)
    (hs : c'.site = .oldw k) : c.site = .old k := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  case sld a k' => fin_cases k' <;> simp at h
  case pst k' => fin_cases k' <;> simp at h
  case pld k' => fin_cases k' <;> simp at h
  case ost k' => fin_cases k' <;> simp at h
  case rstw k' => fin_cases k' <;> simp at h
  case old => exact h.symm
  case ost2 c1 k1 => fin_cases k1 <;> simp at h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
