-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Place
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The positions of the correction warps' barrier events -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **A correction lane's barrier event is at its ordinal's position.** -/
theorem corr_pc {d : Correction.D} {n : Cls → Nat} {ns nv : Nat} {pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (hR : Correction.Ref p L g (d, CorrWarp.rc n))
    (hF : CorrWarp.CFits p L g d ns nv) (hev : Correction.Ev p L g d ⟨pc, .bar id cnt mode⟩)
    (hB : n (.mma .bar) = 1 + n (.corr .bar2) + n (.corr (.nb 0)) + n (.corr (.nb 1)))
    (hLate : d.site.late = true → ∃ R bal, Picked p L g R bal ∧ 2 ≤ n (.corr (.nb 0)) ∧
        2 * (n (.corr (.nb 0)) - 2) =
          CorrWarp.rvN (Correction.Bs p L g (CorrWarp.refV p L g R bal))) :
    d.site.pc = corrPc (tileC p L g) (n (.mma .bar)) := by
  obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := hR
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := corr_ord hQ
  simp only [cbar, CorrWarp.rc] at o1 o2 o3 o4 o5 o6
  have tile : CorrWarp.epi d.site = .ready 0 → d.site.hasUk = true → ∃ R bal, Picked p L g R bal ∧
      Correction.Bs p L g d.v = Correction.Bs p L g (CorrWarp.refV p L g R bal) := by
    intro hep huk
    obtain ⟨rv, -, -, hFE, hu⟩ := hF
    simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
    obtain ⟨R, bal, hC, h0, h1⟩ := hFE
    exact ⟨R, bal, hC.1, CorrWarp.bs_ref hC h0 h1 (hu huk)⟩
  obtain ⟨s, v, k⟩ := d
  cases s
  case bar1 =>
    have := o1 rfl
    rw [show n (.mma .bar) = 1 by omega]
    rfl
  case nb kk =>
    obtain ⟨R, bal, hP, -⟩ := tile rfl (by fin_cases kk <;> rfl)
    have := o2 kk rfl
    rw [tileC_of hP, show n (.mma .bar) = 2 + kk.val by omega]
    fin_cases kk <;> simp [corrPc, Correction.Site.pc]
  case rbar st =>
    obtain ⟨R, bal, hP, hBs⟩ := tile rfl (by fin_cases st <;> rfl)
    have hl := hQ.loop (by fin_cases st <;> rfl)
    simp only at hl
    rw [hBs] at hl
    have := o3 st rfl
    have hst := st.isLt
    rw [tileC_of hP, show n (.mma .bar) = 4 + 2 * r + st.val by omega]
    have h3 : ¬ 4 + 2 * r + st.val ≤ 3 := by omega
    have h5 : 4 + 2 * r + st.val ≤
        3 + 2 * (CorrWarp.rvN (Correction.Bs p L g (CorrWarp.refV p L g R bal)) / 2) := by
      simp only [CorrWarp.rvN]; split <;> omega
    have hm : (4 + 2 * r + st.val) % 2 = st.val := by omega
    simp only [corrPc, h3, h5, hm, Correction.Site.pc, show 4 + 2 * r + st.val ≠ 0 by omega,
      show 4 + 2 * r + st.val ≠ 1 by omega, ↓reduceIte]
  case fbar st =>
    obtain ⟨R, bal, hP, hBs⟩ := tile rfl (by fin_cases st <;> rfl)
    have ht := hQ.tail (by fin_cases st <;> rfl)
    simp only at ht
    rw [hBs] at ht
    have := o4 st rfl
    have hst := st.isLt
    rw [tileC_of hP, rvN_half ht, show n (.mma .bar) = 4 + 2 * r + st.val by omega]
    have h3 : ¬ 4 + 2 * r + st.val ≤ 3 := by omega
    have h4 : ¬ 4 + 2 * r + st.val ≤ 3 + 2 * r := by omega
    have h5 : 4 + 2 * r + st.val ≤ 5 + 2 * r := by omega
    have hm : (4 + 2 * r + st.val) % 2 = st.val := by omega
    simp only [corrPc, h3, h4, h5, hm, Correction.Site.pc, show 4 + 2 * r + st.val ≠ 0 by omega,
      show 4 + 2 * r + st.val ≠ 1 by omega, ↓reduceIte]
  case barEnd l =>
    cases l
    · obtain ⟨rv, -, -, hFE, -⟩ := hF
      have := o6 rfl
      rw [tileC_none (noPicked_exit hFE rfl), show n (.mma .bar) = 2 by omega]
      rfl
    · obtain ⟨R, bal, hP, h2, h3⟩ := hLate rfl
      obtain ⟨h5, h6⟩ := o5 rfl
      rw [tileC_of hP, show n (.mma .bar) = 6 + 2 * r by omega,
        show CorrWarp.rvN (Correction.Bs p L g (CorrWarp.refV p L g R bal)) / 2 = r by omega]
      simp only [corrPc, Correction.Site.pc, show 6 + 2 * r ≠ 0 by omega,
        show 6 + 2 * r ≠ 1 by omega, show ¬ 6 + 2 * r ≤ 3 by omega,
        show ¬ 6 + 2 * r ≤ 3 + 2 * r by omega, show ¬ 6 + 2 * r ≤ 5 + 2 * r by omega, ↓reduceIte]
  all_goals exfalso
  all_goals simp only [Correction.Ev, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq] at *)

/-- **A correction lane's barrier event is at its ordinal's position.** -/
theorem corr_bar_pc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    pc = corrPc (tileC p L g) (((X.tr g).take k).countP Execution.isBar) := by
  have hg := Frame.lt_of_get hX he
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s, n, hσ, -, hJ, -, hev⟩ | ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · rw [start_bar_pc hp hX he hσ hJ hev, start_bar_ord hp hX hFw hg he hσ]
    rfl
  · obtain ⟨hRc, hFc⟩ := hR h0
    have hpc : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ
      (fun f h => by cases h)
    rw [← cls_bar (L := L) (g := g), count hσ, hpc]
    exact corr_pc hRc hFc (hev.data_or_vote.resolve_right (by rintro ⟨_, _, h⟩; cases h))
      (bar_count hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ)
      (corr_late hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ h0)

end
end PTX.Kernels.TmlFa4Fwd.Proof
