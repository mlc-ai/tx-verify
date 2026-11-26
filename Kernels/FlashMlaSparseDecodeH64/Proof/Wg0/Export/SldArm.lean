-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SldSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepInto
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine

@[expose] public section

/-! # The arm of the score loads is the lane's half

The two score loads of a lane of warpgroup 0 are at pcs 278 and 280 (the arm of warps 0 and 1) or
at 283 and 285 (the arm of warps 2 and 3): the control machine takes the arm `scmpi .gt .s w 1` at
the fence before them (`w0_sld_arm`), and the second load follows the first. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

private theorem succOk_sld0 {c c' : Control.D} (h : succOk c c' = true) {a : Bool}
    (hs : c'.site = .sld a 0) : c.site = .tcfa := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

private theorem succOk_sld1 {c c' : Control.D} (h : succOk c c' = true) {a : Bool}
    (hs : c'.site = .sld a 1) : c.site = .sld a 0 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))
  all_goals (try (exact h.symm))

private theorem arm_eq (hw : warp L g < 4) :
    scmpi .gt .s (warpW L g) 1 = decide (2 ≤ warp L g) := by
  have h : warpOf L g = warp L g := rfl
  obtain ⟨a0, a1, a2, a3⟩ := pair_test
  simp only [warpW, h]
  rcases (by omega : warp L g = 0 ∨ warp L g = 1 ∨ warp L g = 2 ∨ warp L g = 3) with h | h | h | h
  <;> rw [h] <;> simp [a0, a1, a2, a3]

private theorem arrS_not' {c c' : Control.D} {f : Event} {a : Bool} {k : Fin 2}
    (h : Control.succ P L g (warpW L g) c f = some (some c')) (hc : c.site = .arrS)
    (hs : c'.site = .sld a k) : False := by
  simp only [Control.succ, hc] at h
  split at h <;> cases h <;> simp_all

end Wg0

open Wg0 Wg0.Data in
/-- **The first score load's pc is the lane's arm**: pc 283 for the warps 2 and 3, 278 for the
others. -/
theorem w0_sld_fst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 278 ∨ e.pc = 283)
    (hv0 : W0Valid P.scale ((X.tr g).take j)) :
    (e.pc = 283 ↔ 2 ≤ warp L g) := by
  cases j with
  | zero => exact (w0_not_first hp hX hFw he hub (by omega)).elim
  | succ j =>
    have hsite : ∃ a : Bool, (∀ s' : Site, s'.pc = e.pc → s' = .sld a 0) ∧
        (e.pc = 283 ↔ a = true) := by
      rcases hpc with h | h
      · exact ⟨false, fun s' hs => by
          rcases site_sld_of_pc s' (by omega) with h' | h' | h' | h' <;> subst h' <;>
            simp_all [Site.pc], by simp [h]⟩
      · exact ⟨true, fun s' hs => by
          rcases site_sld_of_pc s' (by omega) with h' | h' | h' | h' <;> subst h' <;>
            simp_all [Site.pc], by simp [h]⟩
    obtain ⟨a, hs', hiff⟩ := hsite
    obtain ⟨f, c, d, hf, hcpc, hs, hsucc, hc⟩ := w0_step_into_hub hp hX hFw hw he hub (by omega)
      hv0 hs' (by cases a <;> rfl)
    rcases hc with hc | hc
    · exact (arrS_not' hsucc hc (by rw [hs])).elim
    · have hcs := succOk_sld0 hc (a := a) hs
      simp only [Control.succ, hcs] at hsucc
      have h2 := congrArg Control.D.site (Option.some.inj (Option.some.inj hsucc))
      simp only [hs] at h2
      have h3 : a = scmpi .gt .s (warpW L g) 1 := by
        have := Wg0.Site.sld.inj h2
        exact this.1.symm
      rw [hiff, h3, arm_eq hw]
      simp

open Wg0 Wg0.Data in
/-- **The score loads' pcs are the lane's arm**: the loads at pcs 283 and 285 are the warps 2 and
3's, those at 278 and 280 the others'. -/
theorem w0_sld_arm (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hub : ∀ u, e.kind ≠ .ub u)
    (hpc : e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285)
    (hv0 : W0Valid P.scale ((X.tr g).take j)) :
    ((e.pc = 283 ∨ e.pc = 285) ↔ 2 ≤ warp L g) := by
  rcases hpc with h | h | h | h
  · have := w0_sld_fst hp hX hFw hw he hub (Or.inl h) hv0
    omega
  · cases j with
    | zero => exact (w0_not_first hp hX hFw he hub (by omega)).elim
    | succ j =>
      obtain ⟨f, c, d, hf, hcpc, hs, hsucc, hc⟩ := w0_step_into_hub hp hX hFw hw he hub (by omega)
        hv0 (s := .sld false 1) (fun s' hs' => by
          rcases site_sld_of_pc s' (by omega) with h' | h' | h' | h' <;> subst h' <;>
            simp_all [Site.pc]) rfl
      rcases hc with hc | hc
      · exact (arrS_not' hsucc hc (by rw [hs])).elim
      · have hcs := succOk_sld1 hc (a := false) hs
        have hfpc : f.pc = 278 := by rw [← hcpc, hcs]; rfl
        have := w0_sld_fst hp hX hFw hw hf
          (NoUbBefore.ne (noUbBefore_of_get hX he) (Nat.lt_succ_self _) hf) (Or.inl hfpc)
          (W0Valid.take_le hv0 (by omega))
        omega
  · have := w0_sld_fst hp hX hFw hw he hub (Or.inr h) hv0
    omega
  · cases j with
    | zero => exact (w0_not_first hp hX hFw he hub (by omega)).elim
    | succ j =>
      obtain ⟨f, c, d, hf, hcpc, hs, hsucc, hc⟩ := w0_step_into_hub hp hX hFw hw he hub (by omega)
        hv0 (s := .sld true 1) (fun s' hs' => by
          rcases site_sld_of_pc s' (by omega) with h' | h' | h' | h' <;> subst h' <;>
            simp_all [Site.pc]) rfl
      rcases hc with hc | hc
      · exact (arrS_not' hsucc hc (by rw [hs])).elim
      · have hcs := succOk_sld1 hc (a := true) hs
        have hfpc : f.pc = 283 := by rw [← hcpc, hcs]; rfl
        have := w0_sld_fst hp hX hFw hw hf
          (NoUbBefore.ne (noUbBefore_of_get hX he) (Nat.lt_succ_self _) hf) (Or.inr hfpc)
          (W0Valid.take_le hv0 (by omega))
        omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
