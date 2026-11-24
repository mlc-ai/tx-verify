-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Lag
public import Kernels.TmlFa4Fwd.Proof.Correction.Order
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Lib.CorrGood
import Kernels.TmlFa4Fwd.Proof.Progress.CorrPre
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The place of a correction lane's state in its tile

`corr_place`: a state of a correction lane is a startup state, or a role state whose counts are the
places' at its rounds, in the region of the tile of its CTA. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites Reg)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private def siteChk (s : Correction.Site) : Bool :=
  (decide (s.pc < 8006) || (decide (8006 ≤ s.pc) && decide (s.pc ≤ 8446) && s.hasUk) ||
    (Correction.tailR s && s.hasUk) || (decide (8447 ≤ s.pc) && s.noTile) ||
    (decide (8447 ≤ s.pc) && !s.noTile && Progress.Cr.late s &&
      decide ((ptsOf (.arrive 216)).countP (before s) = 1) &&
      decide ((ptsOf (.nb 0)).countP (before s) = 2) &&
      decide ((ptsOf (.arrive 96)).countP (before s) = 2))) &&
  (!s.noTile || decide (CorrWarp.epi s = .exit false)) &&
  (!s.hasUk || decide (CorrWarp.epi s = .ready 0))

private theorem site_chk : Correction.allSites.all siteChk = true := by decide +kernel

private theorem cnt_tab : (ptsOf (.arrive 216)).countP Correction.inRound = 0 ∧
    (ptsOf (.nb 0)).countP Correction.inRound = 1 ∧
    (ptsOf (.arrive 96)).countP Correction.inRound = 1 := by decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : 8 ≤ Prologue.warpIndex L g)
  (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hub hg hw hw1

omit hub hg in
/-- **A lane's events on a named barrier** are at most two more than the tile's rescale rounds. -/
theorem corr_nb_le {R : Nat} (hR : CorrRounds p L g R) (st : Fin 2) :
    ((X.tr g).take k).countP
      (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) ≤ R + 2 := by
  by_contra hlt
  obtain ⟨j, ⟨pc, kd⟩, hj, hget, hb', hcj⟩ := exists_nthEv (X := X) (g := g) (k := k)
    (p := Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) (n := R + 2) (by omega)
  cases kd <;> simp only [Execution.isBarId, beq_iff_eq, Bool.false_eq_true] at hb'
  subst hb'
  rcases corr_bar hp hX hFw hw hw1 hget with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨q, -, -, -, R', hR', hle⟩
  · omega
  · omega
  · obtain rfl := hR.unique hR'
    rw [hcj] at hle
    omega

/-- **The place of a state of a correction lane.** -/
theorem corr_place {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    (Progress.time p L g σ < Progress.scanBase ∧ ∃ s n, σ = (.inl s, n)) ∨
    ∃ d n r, σ = CorrWarp.cinj p L g d n ∧ n .ub = 0 ∧
      (∀ c, c ≠ .st → n (.corr c) = passed (ptsOf c) d.scheduler.site r) ∧
      CorrWarp.CFits p L g d.scheduler (n .shfl) (n .vote) ∧
      (∀ R, CorrRounds p L g R → Reg R d.scheduler.site r ∧ d.scheduler.site.noTile = false) ∧
      ((¬ ∃ R bal, Epilogue.Picked p L g R bal) → d.scheduler.site.pc < 8006 ∨
          d.scheduler.site.noTile = true) := by
  have hG := (corr_good hp hX hFw ⟨hw, hw1⟩ hg k).2 σ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · left
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hG.1
      simp only [StartAt, he] at h1
    exact ⟨Progress.startTime_lt hx, s, n, rfl⟩
  cases i with
  | correction =>
    right
    have hub0 : n .ub = 0 := by
      by_contra h
      obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
      cases kind <;> simp [cls] at hk
      exact hub ⟨(g, j), pc, _, hf⟩
    obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := hG hub0
    have hcnt : ∀ c, c ≠ .st → n (.corr c) = passed (ptsOf c) d.scheduler.site r := hQ.cnt
    refine ⟨d, n, r, rfl, hub0, hcnt, hF, ?_⟩
    have hchk := List.all_eq_true.mp site_chk d.scheduler.site (mem_allSites _)
    simp only [siteChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hchk
    obtain ⟨⟨hreg, hno⟩, hepi⟩ := hchk
    obtain ⟨t1, t2, t3⟩ := cnt_tab
    have tile : d.scheduler.site.hasUk = true →
        CorrRounds p L g ((Correction.Bs p L g d.scheduler.v).toNat - 1) := by
      intro huk
      obtain ⟨rv, -, -, hFE, hu⟩ := hF
      have hep : CorrWarp.epi d.scheduler.site = .ready 0 := hepi.resolve_left (by simp [huk])
      simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
      obtain ⟨R, bal, hC, h0, h1⟩ := hFE
      have hb := CorrWarp.bs_ref hC h0 h1 (hu huk)
      exact ⟨R, bal, hC.1, by rw [hb]; rfl⟩
    have late : (ptsOf (.arrive 216)).countP (before d.scheduler.site) = 1 →
        (ptsOf (.nb 0)).countP (before d.scheduler.site) = 2 →
        (ptsOf (.arrive 96)).countP (before d.scheduler.site) = 2 → CorrRounds p L g r := by
      intro a1 a2 a3
      have h1 := hcnt (.arrive 216) (by simp)
      have h2 := hcnt (.nb 0) (by simp)
      have h3 := hcnt (.arrive 96) (by simp)
      simp only [passed, t1, t2, t3, a1, a2, a3] at h1 h2 h3
      obtain ⟨R, hR, hle⟩ := corr_late_rounds (k := k) hp hX hFw hw hw1 0 (by
        rw [corr_arrivals, count hσ, h1]; omega)
      have h4 := corr_nb_le (k := k) hp hX hFw hw hw1 hR 0
      rw [corr_isBarId hw hw1, count hσ, h2] at h4
      rw [show corrO 0 = 96 from rfl, corr_arrivals, count hσ, h3] at hle
      obtain rfl : R = r := by omega
      exact hR
    constructor
    · intro R hR
      have hpk : ∃ R bal, Epilogue.Picked p L g R bal := let ⟨a, b, h, _⟩ := hR; ⟨a, b, h⟩
      have hnt : d.scheduler.site.noTile = false := by
        rw [Bool.eq_false_iff]
        intro h
        obtain ⟨rv, -, -, hFE, -⟩ := hF
        exact noPicked_of_exit hFE (hno.resolve_left (by simp [h])) hpk
      refine ⟨?_, hnt⟩
      unfold Reg
      rcases hreg with (((h | h) | h) | h) | h
      · exact .inl ⟨h, hQ.pre (by simp [Correction.preR, h])⟩
      · obtain ⟨⟨h1, h2⟩, huk⟩ := h
        obtain ⟨b1, -⟩ := hQ.loop (by simp [Correction.inRound, h1, h2])
        have e := hR.unique (tile huk)
        generalize Correction.Bs p L g d.scheduler.v = x at *
        exact .inr (.inl ⟨⟨h1, h2⟩, by omega⟩)
      · obtain ⟨h1, huk⟩ := h
        have b1 := hQ.tail h1
        have e := hR.unique (tile huk)
        simp only [Correction.tailR, Bool.and_eq_true, decide_eq_true_eq] at h1
        generalize Correction.Bs p L g d.scheduler.v = x at *
        exact .inr (.inr ⟨h1.1, hnt, by omega⟩)
      · rw [h.2] at hnt; cases hnt
      · obtain ⟨⟨⟨⟨⟨h1, -⟩, -⟩, a1⟩, a2⟩, a3⟩ := h
        exact .inr (.inr ⟨h1, hnt, (hR.unique (late a1 a2 a3)).symm⟩)
    · intro hno'
      have tp : ∀ {R}, CorrRounds p L g R → False := fun ⟨a, b, h, _⟩ => hno' ⟨a, b, h⟩
      rcases hreg with (((h | h) | h) | h) | h
      · exact .inl h
      · exact (tp (tile h.2)).elim
      · exact (tp (tile h.2)).elim
      · exact .inr h.2
      · exact (tp (late h.1.1.2 h.1.2 h.2)).elim
  | _ => exact hG.elim

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
