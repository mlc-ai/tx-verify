-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites

@[expose] public section

/-! # The chain of the rescale arm

A site is determined by its pc (`site_pc_inj`: the sites' pcs are a list without repetition), and
the sites before a rescale chunk's store on the block's chain are its wait for the load and its
load (`succOk_rst`, `succOk_rldw`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof Wg0.Data

noncomputable section

theorem mem_allSites (s : Site) : s ∈ allSites := by
  cases s <;> first | decide +kernel | (rename_i a; revert a; decide +kernel) |
    (rename_i a b; revert a b; decide +kernel)

theorem site_pc_inj {s t : Site} (h : s.pc = t.pc) : s = t :=
  List.inj_on_of_nodup_map sites_nodup (mem_allSites s) (mem_allSites t) h

theorem succOk_rst {c c' : Control.D} {k : Fin 4} (h : succOk c c' = true)
    (hs : c'.site = .rst k) : c.site = .rldw k := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  case sld a k' => fin_cases k' <;> simp at h
  case pst k' => fin_cases k' <;> simp at h
  case pld k' => fin_cases k' <;> simp at h
  case rstw k' => fin_cases k' <;> simp at h
  case ost k' => fin_cases k' <;> simp at h
  case ost2 c' k' => fin_cases k' <;> simp at h
  case rldw => exact h.symm

theorem succOk_rldw {c c' : Control.D} {k : Fin 4} (h : succOk c c' = true)
    (hs : c'.site = .rldw k) : c.site = .rld k := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  case sld a k' => fin_cases k' <;> simp at h
  case pst k' => fin_cases k' <;> simp at h
  case pld k' => fin_cases k' <;> simp at h
  case rstw k' => fin_cases k' <;> simp at h
  case ost k' => fin_cases k' <;> simp at h
  case ost2 c' k' => fin_cases k' <;> simp at h
  case rld => exact h.symm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
