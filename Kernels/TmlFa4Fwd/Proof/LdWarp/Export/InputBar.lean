-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Input
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAltQ
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.Start
public import Kernels.TmlFa4Fwd.Proof.Loader.Input
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAltQ
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.TcSpec
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The barrier of a tensor copy's site

A decoded tensor copy of site `j` completes on the full barrier of the slot its box lies in:
Q stage 0 and 1 (offsets 0 and 8), bias stage 0 and 1 (320 and 328): `ld_input_bar`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

/-- The full barrier of a decoded copy's site. -/
def siteBar (j : Fin 14) : Nat :=
  [0, 0, 320, 320, 8, 8, 328, 328, 320, 320, 328, 328, 320, 320].getD j.val 0

/-- **A site's slot**: 16384 bytes, a half of the 32768 bytes of the slot of its barrier. -/
theorem siteBar_slot : ∀ j : Fin 14,
    ((siteBar j = 0 ∧ (Loader.inputSite j).sharedOffset = 3072 + 16384 * (j.val % 2)) ∨
      siteBar j = 8 ∧ (Loader.inputSite j).sharedOffset = 35840 + 16384 * (j.val % 2)) ∨
    ((siteBar j = 320 ∧ (Loader.inputSite j).sharedOffset = 166912 + 16384 * (j.val % 2)) ∨
      siteBar j = 328 ∧ (Loader.inputSite j).sharedOffset = 199680 + 16384 * (j.val % 2)) := by
  decide

private theorem siteBar_of : ∀ (t : Fin 7) (c : Fin 2),
    Loader.taOff t = siteBar (Loader.siteOf t c) := by
  decide

/-- **A loader lane's tensor copy**, with its barrier. -/
theorem ld_input_bar (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc a : Nat} {s : TensorCopy.Spec} (he : X.get (h, k) = some ⟨pc, .tensorIssue a s⟩) :
    ∃ j org, a = Loader.inputMapAddress p (Loader.inputSite j) ∧
      s = inputSpec p L (h / L.block) j org (obj L h (siteBar j)) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tensorIssue a s⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_no_tensor hev hi.2).elim
  obtain ⟨-, -, h3, h4⟩ := Loader.copy_site hev hub
  obtain ⟨t, c, hs⟩ := h3.mp ⟨a, s, rfl⟩
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  obtain ⟨xc, xr, xh, mb, -, -, -, hk⟩ := Loader.tc_spec hp hg hat hc hf
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨a', s', hk', hb⟩ := h4 _ _ rfl
  simp only [Kind.tensorIssue.injEq] at hk'
  obtain ⟨-, rfl⟩ := hk'
  rw [Loader.tc_loc' hp] at hb
  have hmb : mb = obj L h (siteBar (Loader.siteOf t c)) := by
    rw [← siteBar_of]
    rw [hk.2] at hb
    exact hb
  exact ⟨_, _, hk.1, hmb ▸ hk.2⟩

/-- **A loader lane's copy on a Q stage's barrier** fills the box of its parity. -/
theorem ld_q_copy (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (hwon : ∀ k pc mask inst ld, X.get (h, k) = some ⟨pc, .elect mask inst ld⟩ →
      ld = laneOf L h) (st : Fin 2)
    {pc a : Nat} {s : TensorCopy.Spec} (he : X.get (h, k) = some ⟨pc, .tensorIssue a s⟩)
    (hb : s.mbar = obj L h (8 * st.val)) :
    ∃ j org, s = inputSpec p L (h / L.block) j org s.mbar ∧
      (Loader.inputSite j).sharedOffset = 3072 + 32768 * st.val +
        16384 * (((X.tr h).take k).countP (issuesTo (obj L h (8 * st.val))) % 2) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tensorIssue a s⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_no_tensor hev hi.2).elim
  obtain ⟨-, -, h3, h4⟩ := Loader.copy_site hev hub
  obtain ⟨t, c, hs⟩ := h3.mp ⟨a, s, rfl⟩
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨a', s', hk', hm⟩ := h4 t c hs
  simp only [Kind.tensorIssue.injEq] at hk'
  obtain ⟨rfl, rfl⟩ := hk'
  have h14w : Loader.wOf b = 14 := by
    have h8 : 8 * st.val = 0 ∨ 8 * st.val = 8 := by omega
    rw [hR.1]
    exact (ld_tma_copy hp hX hFw hw (o := 8 * st.val) (by unfold LdTmaOff; omega) he hb).1
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  rw [tc_loc hp t c] at hm
  have hoff : Loader.taOff t = 8 * st.val := (obj_off (hm.symm.trans hb)).2.symm
  obtain ⟨xc, xr, xh, mb, -, -, -, hk⟩ := Loader.tc_spec hp hg hat hc hf
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  refine ⟨_, _, rfl, ?_⟩
  · have key : ∀ (t : Fin 7) (c st : Fin 2), Loader.taOff t = 8 * st.val →
        (Loader.inputSite (Loader.siteOf t c)).sharedOffset =
          3072 + 32768 * st.val + 16384 * c.val := by decide
    rw [key t c st hoff]
    have hN : ∃ N, ((X.tr h).take k).countP (issuesTo (obj L h (8 * st.val))) + (2 - c.val) =
        2 * N := by
      by_cases h0' : st.val = 0
      · have := Loader.tc_alt (o := 0) (by simp) hp hX hg hwon hw hσ h0
        simp only [Loader.TcAlt, Loader.tcRem, show Loader.taOff t = 0 by omega, ↓reduceIte] at this
        refine ⟨_, Eq.trans ?_ this⟩
        rw [h0']
        rfl
      · have := Loader.tc_alt8 hp hX hg hwon hw hσ h0 h14w
        have ht : t = 2 := by
          have h1 : Loader.taOff t = 8 := by omega
          have key : ∀ t : Fin 7, Loader.taOff t = 8 → t = 2 := by decide
          exact key t h1
        subst ht
        simp only [Loader.tcRem, show Loader.taOff 2 = 8 from rfl, ↓reduceIte, Loader.past2,
          show ¬ ((2 : Fin 7).val < 2) by decide] at this
        refine ⟨1, Eq.trans ?_ this⟩
        rw [show st.val = 1 by omega]
        rfl
    obtain ⟨N, hN⟩ := hN
    have hc2 := c.isLt
    congr 2
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
