-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Place
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The positions of the softmax warps' barrier events -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **A softmax lane's barrier event is at its ordinal's position.** -/
theorem soft_pc {d : Softmax.D} {n : Cls → Nat} {c : Softmax.Cnt → Nat} {rb rp ns nv : Nat}
    {pc id : Nat} {cnt : Option Nat} {mode : BarMode} (hQ : Softmax.RefQ p L g d c rb rp)
    (hL : SmWarp.Linked n c) (hF : SmWarp.SFits p L g d ns nv)
    (hev : Softmax.Ev p L g d ⟨pc, .bar id cnt mode⟩)
    (hB : n (.mma .bar) = 1 + n (.soft .bar2) + n (.soft .nb) + n (.soft .sb))
    (hLate : d.site.late = true → ∃ R bal, Picked p L g R bal ∧
        n (.soft .sb) = 1 + (Softmax.nB p L g (refVS p L g R bal)).toNat ∧
        n (.soft .nb) = 2 + (Softmax.nB p L g (refVS p L g R bal)).toNat +
          (Softmax.nP p L g (refVS p L g R bal)).toNat) :
    d.site.pc = softPc (tileS p L g) (n (.mma .bar)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := soft_ord hQ
  have l0 := hL .bar2 rfl
  have l1 := hL .nb rfl
  have l2 := hL .sb rfl
  simp only [sbar] at o1 o2 o3 o4 o5 o6 o7 o8 o9
  have tile : SmWarp.epi d.site = .ready 0 → d.site.hasUk = true → ∃ R bal, Picked p L g R bal ∧
      Softmax.nB p L g d.v = Softmax.nB p L g (refVS p L g R bal) ∧
        Softmax.nP p L g d.v = Softmax.nP p L g (refVS p L g R bal) := by
    intro hep huk
    obtain ⟨hFE, hu⟩ := hF
    simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
    obtain ⟨R, bal, hC, h0, h1⟩ := hFE
    exact ⟨R, bal, hC.1, nBP_ref hC h0 h1 (hu huk)⟩
  -- a position in a tile of `B` biased and `P` plain rounds
  have at_ : ∀ {B P N q : Nat}, n (.mma .bar) = N → q = softPc (some (B, P)) N →
      tileS p L g = some (B, P) → q = softPc (tileS p L g) (n (.mma .bar)) := by
    intro B P N q h1 h2 h3
    rw [h1, h3, h2]
  obtain ⟨s, v, k, acc⟩ := d
  cases s
  case bar1 =>
    have := o1 rfl
    rw [show n (.mma .bar) = 1 by omega]
    rfl
  case bsync l =>
    obtain ⟨R, bal, hP, eB, -⟩ := tile rfl rfl
    have hT := tileS_of hP
    generalize Softmax.nB p L g (refVS p L g R bal) = Bi at *
    generalize Softmax.nP p L g (refVS p L g R bal) = Pi at *
    cases l
    · have := o2 rfl
      exact at_ (N := 2) (by omega) rfl hT
    · have hb := hQ.bias rfl
      simp only at hb
      rw [eB] at hb
      have := o4 rfl
      refine at_ (N := 4 + 2 * rb) (by omega) ?_ hT
      simp only [softPc, show 4 + 2 * rb ≠ 0 by omega, show 4 + 2 * rb ≠ 1 by omega,
        show 4 + 2 * rb ≠ 2 by omega, show 4 + 2 * rb ≠ 3 by omega,
        show 4 + 2 * rb ≤ 3 + 2 * Bi.toNat by omega, show (4 + 2 * rb) % 2 = 0 by omega,
        ↓reduceIte, Softmax.Site.pc]
  case narr r =>
    obtain ⟨R, bal, hP, eB, eP⟩ := tile rfl rfl
    have hT := tileS_of hP
    generalize Softmax.nB p L g (refVS p L g R bal) = Bi at *
    generalize Softmax.nP p L g (refVS p L g R bal) = Pi at *
    cases r
    · have := o3 rfl
      exact at_ (N := 3) (by omega) rfl hT
    · have hb := hQ.bias rfl
      simp only at hb
      rw [eB] at hb
      have := o5 rfl
      refine at_ (N := 5 + 2 * rb) (by omega) ?_ hT
      simp only [softPc, show 5 + 2 * rb ≠ 0 by omega, show 5 + 2 * rb ≠ 1 by omega,
        show 5 + 2 * rb ≠ 2 by omega, show 5 + 2 * rb ≠ 3 by omega,
        show 5 + 2 * rb ≤ 3 + 2 * Bi.toNat by omega, show ¬ (5 + 2 * rb) % 2 = 0 by omega,
        ↓reduceIte, Softmax.Site.pc, Softmax.Rd.pc]
    · have hb := hQ.plain rfl
      simp only at hb
      rw [eB, eP] at hb
      obtain ⟨-, h2, -, h4⟩ := hb
      have h4' := done_toNat h4
      have := o6 rfl
      refine at_ (N := 4 + 2 * rb + rp) (by omega) ?_ hT
      simp only [softPc, show 4 + 2 * rb + rp ≠ 0 by omega, show 4 + 2 * rb + rp ≠ 1 by omega,
        show 4 + 2 * rb + rp ≠ 2 by omega, show 4 + 2 * rb + rp ≠ 3 by omega,
        show ¬ 4 + 2 * rb + rp ≤ 3 + 2 * Bi.toNat by omega,
        show 4 + 2 * rb + rp ≤ 3 + 2 * Bi.toNat + Pi.toNat by omega, ↓reduceIte,
        Softmax.Site.pc, Softmax.Rd.pc]
  case finarr =>
    obtain ⟨R, bal, hP, eB, eP⟩ := tile rfl rfl
    have hT := tileS_of hP
    generalize Softmax.nB p L g (refVS p L g R bal) = Bi at *
    generalize Softmax.nP p L g (refVS p L g R bal) = Pi at *
    have hf := hQ.fin rfl
    simp only at hf
    rw [eB, eP] at hf
    have f1 := done_toNat hf.1
    have f2 := done_toNat hf.2
    have := (o7 rfl).1
    refine at_ (N := 4 + 2 * Bi.toNat + Pi.toNat) (by omega) ?_ hT
    generalize Bi.toNat = b at *
    generalize Pi.toNat = q at *
    simp only [softPc, show 4 + 2 * b + q ≠ 0 by omega, show 4 + 2 * b + q ≠ 1 by omega,
      show 4 + 2 * b + q ≠ 2 by omega, show 4 + 2 * b + q ≠ 3 by omega,
      show ¬ 4 + 2 * b + q ≤ 3 + 2 * b by omega,
      show ¬ 4 + 2 * b + q ≤ 3 + 2 * b + q by omega, ↓reduceIte, Softmax.Site.pc]
  case barEnd l =>
    cases l
    · obtain ⟨hFE, -⟩ := hF
      have hFE' : Epilogue.Fits p L g { v.sc with site := .exit false } ns nv := hFE
      have := o9 rfl
      rw [tileS_none (noPicked_exit hFE' rfl), show n (.mma .bar) = 2 by omega]
      rfl
    · obtain ⟨R, bal, hP, h2, h3⟩ := hLate rfl
      obtain ⟨h5, h6, h7⟩ := o8 rfl
      have hT := tileS_of hP
      generalize Softmax.nB p L g (refVS p L g R bal) = Bi at *
      generalize Softmax.nP p L g (refVS p L g R bal) = Pi at *
      refine at_ (N := 5 + 2 * Bi.toNat + Pi.toNat) (by omega) ?_ hT
      simp only [softPc, show 5 + 2 * Bi.toNat + Pi.toNat ≠ 0 by omega,
        show 5 + 2 * Bi.toNat + Pi.toNat ≠ 1 by omega,
        show 5 + 2 * Bi.toNat + Pi.toNat ≠ 2 by omega,
        show 5 + 2 * Bi.toNat + Pi.toNat ≠ 3 by omega,
        show ¬ 5 + 2 * Bi.toNat + Pi.toNat ≤ 3 + 2 * Bi.toNat by omega,
        show ¬ 5 + 2 * Bi.toNat + Pi.toNat ≤ 3 + 2 * Bi.toNat + Pi.toNat by omega,
        show 5 + 2 * Bi.toNat + Pi.toNat ≠ 4 + 2 * Bi.toNat + Pi.toNat by omega, ↓reduceIte,
        Softmax.Site.pc]
  all_goals exfalso
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Softmax.Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq] at *)

/-- **A softmax lane's barrier event is at its ordinal's position.** -/
theorem soft_bar_pc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    pc = softPc (tileS p L g) (((X.tr g).take k).countP Execution.isBar) := by
  have hg := Frame.lt_of_get hX he
  rcases SmWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, hσ, -, hJ, -, hev⟩ | ⟨d, n, hσ, h0, hR, -, hev⟩
  · rw [start_bar_pc hp hX he hσ hJ hev, start_bar_ord hp hX hFw hg he hσ]
    rfl
  · obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hFs⟩ := hR.2 h0
    have hpc : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ
      (fun f h => by cases h)
    rw [← cls_bar (L := L) (g := g), count hσ, hpc]
    exact soft_pc hQ hLk hFs hev.1 (bar_count hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ)
      (soft_late hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ h0)

end
end PTX.Kernels.TmlFa4Fwd.Proof
