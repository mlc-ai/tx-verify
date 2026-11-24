-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.Start
public import Kernels.TmlFa4Fwd.Proof.Loader.Input
public import Lemmas.Flow.NotTensor
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.TcSpec
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' tensor copies

Every tensor copy of a lane of warp 14 or 15 is one of the fourteen decoded copies (`inputSite`): a
box of the launch's Q or Bias map into the CTA's shared window at the site's offset
(`ld_input`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

/-- The issued copy of site `j` in CTA `c`, at box origin `org`, completing on `mb`. -/
def inputSpec (p : Params) (L : Launch) (c : Nat) (j : Fin 14) (org : Fin 3 → Int) (mb : Loc) :
    TensorCopy.Spec :=
  ⟨⟨2, Loader.inputMap p (Loader.inputSite j), org,
    ⟨.shared, c, L.sharedBase + (Loader.inputSite j).sharedOffset⟩, none⟩, mb, false, .one⟩

/-- **A loader lane's tensor copy** is one of the decoded copies. -/
theorem ld_input (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc a : Nat} {s : TensorCopy.Spec} (he : X.get (h, k) = some ⟨pc, .tensorIssue a s⟩) :
    ∃ j org mb, a = Loader.inputMapAddress p (Loader.inputSite j) ∧
      s = inputSpec p L (h / L.block) j org mb := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tensorIssue a s⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_no_tensor hev hi.2).elim
  obtain ⟨-, -, h3, -⟩ := Loader.copy_site hev hub
  obtain ⟨t, c, hs⟩ := h3.mp ⟨a, s, rfl⟩
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  obtain ⟨xc, xr, xh, mb, -, -, -, hk⟩ := Loader.tc_spec hp hg hat hc hf
  simp only [Kind.tensorIssue.injEq] at hk
  exact ⟨_, _, mb, hk.1, hk.2⟩

/-- **The electing lane's copies on a bias full barrier**: copy `c` of a group has `2 u + c` earlier
ones, and its destination is box `c` of the stage's window. -/
theorem ld_bias_copy (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (hwon : ∀ k pc mask inst ld, X.get (h, k) = some ⟨pc, .elect mask inst ld⟩ →
      ld = laneOf L h) (st : Fin 2)
    {pc a : Nat} {s : TensorCopy.Spec} (he : X.get (h, k) = some ⟨pc, .tensorIssue a s⟩)
    (hb : s.mbar = obj L h (320 + 8 * st.val)) :
    ∃ j org, s = inputSpec p L (h / L.block) j org s.mbar ∧
      (Loader.inputSite j).bias = true ∧
      (Loader.inputSite j).sharedOffset = 166912 + 32768 * st.val +
        16384 * (((X.tr h).take k).countP (issuesTo (obj L h (320 + 8 * st.val))) % 2) := by
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
  have halt := Loader.tc_alt (o := 320 + 8 * st.val)
    (by fin_cases st <;> simp) hp hX hg hwon hw hσ h0
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  rw [tc_loc hp t c] at hm
  have hoff : Loader.taOff t = 320 + 8 * st.val := (obj_off (hm.symm.trans hb)).2.symm
  obtain ⟨xc, xr, xh, mb, -, -, -, hk⟩ := Loader.tc_spec hp hg hat hc hf
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  refine ⟨_, _, rfl, ?_, ?_⟩
  · have key : ∀ (t : Fin 7) (c st : Fin 2), Loader.taOff t = 320 + 8 * st.val →
        (Loader.inputSite (Loader.siteOf t c)).bias = true := by decide
    exact key t c st hoff
  · have key : ∀ (t : Fin 7) (c st : Fin 2), Loader.taOff t = 320 + 8 * st.val →
        (Loader.inputSite (Loader.siteOf t c)).sharedOffset =
          166912 + 32768 * st.val + 16384 * c.val := by decide
    rw [key t c st hoff]
    have hN : ((X.tr h).take k).countP (issuesTo (obj L h (320 + 8 * st.val))) + (2 - c.val) =
        2 * n (.load (.acquire (obj L h (320 + 8 * st.val + 16)))) := by
      have := halt
      simp only [Loader.TcAlt, Loader.tcRem, hoff, ↓reduceIte] at this
      exact this
    have hc2 := c.isLt
    congr 2
    omega

/-- **A loader lane's copy into the box of a bias stage** completes on that stage's bias full
barrier. -/
theorem ld_bias_bar (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc a : Nat} {s : TensorCopy.Spec} (he : X.get (h, k) = some ⟨pc, .tensorIssue a s⟩)
    (st q : Fin 2) (hoff : s.sharedBase.addr =
      L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val)) :
    s.mbar = obj L h (320 + 8 * st.val) := by
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
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  rw [tc_loc hp t c] at hm
  obtain ⟨xc, xr, xh, mb, -, -, -, hk⟩ := Loader.tc_spec hp (Frame.lt_of_get hX he) hat hc hf
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  have key : ∀ (t : Fin 7) (c st q : Fin 2), (Loader.inputSite (Loader.siteOf t c)).sharedOffset =
      166912 + 32768 * st.val + 16384 * q.val → Loader.taOff t = 320 + 8 * st.val := by decide
  simp only at hoff hm ⊢
  rw [hm, key t c st q (by omega)]

/-- Two boxes of input sites that share a byte are one. -/
theorem site_apart : ∀ j j' : Fin 14,
    (Loader.inputSite j).sharedOffset < (Loader.inputSite j').sharedOffset + 16384 →
    (Loader.inputSite j').sharedOffset < (Loader.inputSite j).sharedOffset + 16384 →
    (Loader.inputSite j).sharedOffset = (Loader.inputSite j').sharedOffset := by decide

end
end PTX.Kernels.TmlFa4Fwd.Proof
