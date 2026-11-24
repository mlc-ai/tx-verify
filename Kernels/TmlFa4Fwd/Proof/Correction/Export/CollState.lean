-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.CollRound
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every state of a correction warp stands in its schedule of collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk slotOf bandC primeBase endBase scanBase bmax
  passTime)
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (RefQ ptsOf passed before inRound preR tailR
  allSites mem_allSites)
open PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp (rvN refV)

open CorrColl

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The collective a correction site is at. -/
def corrTagS (s : Correction.Site) : Option (STag Correction.Site) :=
  if s.wcoll then (if s.isRvote then some (.mid s) else some (.scan (CorrWarp.epi s))) else none

/-- The collective a thread state of a correction warp is at. -/
def corrTag (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) :
    Option (STag Correction.Site) :=
  match σ with
  | (.inl s, _) => match s.site with | .sh j => some (.start j) | _ => none
  | (.inr ⟨.correction, d⟩, _) => corrTagS d.site
  | _ => none

theorem corrTag_isSome (σ : (thread p L g).D) : (corrTag p L g σ).isSome = corrAt p L g σ := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · simp only [corrTag, corrAt]; cases s.site <;> rfl
  all_goals first
    | rfl
    | (simp only [corrTag, corrAt, corrTagS]
       cases d.site.wcoll <;> cases d.site.isRvote <;> rfl)

/-- A scan site. -/
private theorem corr_scan {d : Correction.D} {ns nv : Nat}
    (hF : Epilogue.Fits p L g (CorrWarp.toE d) ns nv) {l : Bool}
    (hpl : Progress.Cr.part d.site = none) (hend : Progress.Cr.endOff d.site = none)
    (hq : d.site ≠ .q0 ∧ d.site ≠ .q1 ∧ d.site ≠ .uk)
    (hs : d.site ≠ .setmax ∧ d.site ≠ .bar1 ∧ ∀ a, d.site ≠ .arr a)
    (hl : Progress.Cr.late d.site = l) :
    ∃ n0 v0, Epilogue.PassStart p L g l n0 v0 ∧ n0 ≤ ns ∧
      nv = v0 + Progress.Out.ballots (Progress.Cr.toE d.site) ∧
      d.site.wcoll = Progress.Out.coll (Progress.Cr.toE d.site) ∧ d.site.isRvote = false ∧
      CorrWarp.epi d.site = Progress.Cr.toE d.site ∧
      (Progress.Cr.toE d.site).late = l := by
  subst hl
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨q1, q2, q3⟩ := hq
  obtain ⟨s1, s2, s3⟩ := hs
  cases s <;> simp only [Progress.Cr.part, Progress.Cr.endOff, reduceCtorEq, ne_eq,
    not_true_eq_false, not_false_eq_true] at hpl hend q1 q2 q3 s1 s2 <;>
    first
      | exact absurd rfl (s3 _)
      | (simp only [Epilogue.Fits, CorrWarp.toE, CorrWarp.epi] at hF
         obtain ⟨r, n0, v0, hP, -, h3, h4, -⟩ := hF
         exact ⟨n0, v0, hP, by omega, by
           simp only [Progress.Cr.toE, Progress.Out.ballots]; omega, rfl, rfl, rfl, rfl⟩)

private theorem corr_end {s : Correction.Site} {l : Bool} {o : Nat}
    (h : Progress.Cr.endOff s = some (l, o)) :
    s.late = l ∧ CorrWarp.epi s = .exit l ∧ corrTagS s = none := by
  cases s <;> simp only [Progress.Cr.endOff, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X)
  (hg : g < L.threads) {w : Nat} (hw8 : 8 ≤ w ∧ w ≤ 11) (hw : Prologue.warpIndex L g = w)
include hp hX hub hg hw8 hw

/-- What a role state's reference gives. -/
theorem corr_open {d : Correction.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) :
    ∃ r ℓ, RefQ p L g d.scheduler (fun c => n (.corr c)) r ℓ ∧
      CorrWarp.CFits p L g d.scheduler (n .shfl) (n .vote) := by
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := (CorrWarp.good hp hX hw8 hg hw k).2 _ hσ hub0
  exact ⟨r, ℓ, hQ, hF⟩

/-- A role state. -/
private theorem corr_role_cls {d : Correction.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) :
    SCls (corrMid hp w (g / L.block)) g 0 (n .shfl + n .vote)
      (Progress.Cr.time p d.scheduler n) (corrTagS d.scheduler.site) := by
  obtain ⟨r, ℓ, hQ, rv, hle, hrv, hFE, hu⟩ := corr_open hp hX hub hg hw8 hw hσ
  generalize d.scheduler = d at *
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
  have hck := rs_ok d.site
  cases hpl : Progress.Cr.part d.site with
  | some x =>
    -- the rounds
    simp only [rsChk, hpl, Bool.and_eq_true, beq_iff_eq] at hck
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, hwc⟩, -⟩, -⟩ := hck
    simp only [Epilogue.Fits, CorrWarp.toE, h1] at hFE
    obtain ⟨R, bal, hC, h5, h6⟩ := hFE
    have hBs := CorrWarp.bs_ref hC h5 h6 (hu h2)
    obtain ⟨hP, -, -, -, -, -, -, hns, hnv⟩ := hC
    obtain ⟨a, hT, a1, a2⟩ := corr_tile hp hg hw hP
    rw [← hBs] at a2
    obtain ⟨-, -, -, hbm, -⟩ := id hT
    have hM := corr_round (n := n) hQ hrv a2 hbm hpl
    have hN : n .shfl + n .vote = 0 + (a.ch + rv) := by omega
    have htg : corrTagS d.site = (if d.site.isRvote then some d.site else none).map .mid := by
      unfold corrTagS
      rw [hwc]
      cases d.site.isRvote <;> rfl
    rw [hN, htg]
    exact .mid a _ _ _ hT hM
  | none =>
    simp only [rsChk, hpl, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hck
    obtain ⟨⟨⟨⟨hnr, hlp⟩, htl⟩, hin⟩, hll⟩ := hck
    cases hlate : Progress.Cr.late d.site with
    | false =>
      have hrv0 : rv = 0 := by
        have hl' : d.site.late = false := by rw [← hll]; exact hlate
        simpa only [CorrWarp.RvAt, hin, htl, hl', Bool.false_eq_true, ite_false] using hrv
      subst hrv0
      rw [Nat.sub_zero] at hFE
      rw [show n .shfl + n .vote = 0 + (n .shfl + n .vote) by omega]
      cases hend : Progress.Cr.endOff d.site with
      | some x =>
        obtain ⟨l, o⟩ := x
        obtain ⟨h1, hsite, h3⟩ := corr_end hend
        rw [← hll, hlate] at h1
        subst h1
        simp only [Epilogue.Fits, hsite] at hFE
        rw [h3]
        exact .end1 _ _ _ hFE
      | none =>
        by_cases hs0 : d.site = .setmax ∨ d.site = .bar1 ∨ ∃ a, d.site = .arr a
        · have hf : n .shfl = 3 ∧ n .vote = 0 := by
            rcases hs0 with h | h | ⟨a, h⟩ <;>
              simpa only [Epilogue.Fits, CorrWarp.toE, h, CorrWarp.epi] using hFE
          have ht : Progress.Cr.time p d n < scanBase + 6 := by
            rcases hs0 with h | h | ⟨a, h⟩ <;>
              simp only [Progress.Cr.time, h, Progress.Cr.part, Progress.Cr.endOff, ite_true,
                ite_false, reduceCtorEq, Progress.Cr.late, passTime, Progress.Cr.toE,
                Progress.Out.coll, Progress.Out.ballots, Epilogue.Site.shfl,
                Epilogue.Site.ballot, Bool.or_self, Bool.false_eq_true, hf.1] <;> omega
          have htg : corrTagS d.site = none := by
            rcases hs0 with h | h | ⟨a, h⟩ <;> rw [h] <;> rfl
          rw [htg, hf.1, hf.2]
          exact .scanOff 3 _ (by omega) (by omega) (by omega)
        · simp only [not_or, not_exists] at hs0
          have ht : Progress.Cr.time p d n = passTime scanBase (n .shfl +
              Progress.Out.ballots (Progress.Cr.toE d.site))
              (Progress.Out.coll (Progress.Cr.toE d.site)) := by
            simp only [Progress.Cr.time, hpl, hend, hs0.1, hs0.2.1, hlate, Bool.false_eq_true,
              ite_false]
          rw [ht]
          by_cases hq : d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk
          · -- the request's reads
            have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (CorrWarp.toE d) (n .shfl)
                (n .vote) := by
              have h2' := hFE
              rcases hq with h | h | h <;>
                simp only [Epilogue.Fits, CorrWarp.toE, h, CorrWarp.epi] at h2'
              · exact h2'
              · obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩
              · obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩
            obtain ⟨R, bal, hC⟩ := hC
            have hbd := Epilogue.chosen_coll_le hp hC
            obtain ⟨hP, -, -, -, -, -, -, hns, hnv⟩ := hC
            obtain ⟨a, hT, a1, -⟩ := corr_tile hp hg hw hP
            have htg : corrTagS d.site = (none : Option Correction.Site).map .mid := by
              rcases hq with h | h | h <;> rw [h] <;> rfl
            rw [htg]
            refine .mid a _ _ none hT (.inl ⟨rfl, by omega, ?_⟩)
            have hc : Progress.Out.coll (Progress.Cr.toE d.site) = false ∧
                Progress.Out.ballots (Progress.Cr.toE d.site) = 0 := by
              rcases hq with h | h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
            rw [hc.1, hc.2]
            simp only [passTime, Bool.false_eq_true, ite_false]
            omega
          · -- the first pass
            simp only [not_or] at hq
            obtain ⟨n0, v0, hps, hn0, hnv, w1, w2, w3, w4⟩ :=
              corr_scan hFE hpl hend hq ⟨hs0.1, hs0.2.1, hs0.2.2⟩ hlate
            have hbd := Epilogue.fits_coll_le hp hFE (by
              show (CorrWarp.epi d.site).late = false
              rw [w3, w4])
            simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps
            cases hco : Progress.Out.coll (Progress.Cr.toE d.site) with
            | true =>
              obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ := Epilogue.coll_pos hFE (by
                show Progress.Out.coll (CorrWarp.epi d.site) = true
                rw [w3]; exact hco)
              have hq' : Epilogue.Pos p (g / L.block) l q (CorrWarp.epi d.site) := hq
              have hlf : l = false := by rw [← hq'.late, w3, w4]
              subst hlf
              simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps'
              have hN : n .shfl + n .vote = 3 + q := by omega
              have ht' : passTime scanBase (n .shfl +
                  Progress.Out.ballots (Progress.Cr.toE d.site)) true =
                  scanBase + 2 * (3 + q) := by simp only [passTime, ite_true]; omega
              have htg : corrTagS d.site = some (.scan (CorrWarp.epi d.site)) := by
                simp [corrTagS, w1, hco, w2]
              rw [hN, ht', htg]
              exact .scan q _ hq' (by omega)
            | false =>
              have htg : corrTagS d.site = none := by simp [corrTagS, w1, hco]
              rw [htg]
              simp only [passTime, Bool.false_eq_true, ite_false]
              exact .scanOff _ _ (by omega) (by omega) (by omega)
    | true =>
      have hlt : d.site.late = true := by rw [← hll]; exact hlate
      simp only [CorrWarp.RvAt, hin, htl, hlt, Bool.false_eq_true, ite_false, ite_true] at hrv
      obtain ⟨R, bal, hP, hrv⟩ := hrv
      obtain ⟨a, hT, a1, a2⟩ := corr_tile hp hg hw hP
      rw [← hrv] at a2
      have hN0 : n .shfl + n .vote = 0 + a.V + (n .shfl + (n .vote - rv)) := by omega
      rw [hN0]
      cases hend : Progress.Cr.endOff d.site with
      | some x =>
        obtain ⟨l, o⟩ := x
        obtain ⟨h1, hsite, h3⟩ := corr_end hend
        rw [hlt] at h1
        subst h1
        simp only [Epilogue.Fits, hsite] at hFE
        rw [h3]
        exact .end2 a _ _ _ hT hFE
      | none =>
        have hs0 : d.site ≠ .setmax ∧ d.site ≠ .bar1 ∧ ∀ a, d.site ≠ .arr a := by
          refine ⟨?_, ?_, fun a => ?_⟩ <;> intro h <;> rw [h] at hlate <;> cases hlate
        have hq : d.site ≠ .q0 ∧ d.site ≠ .q1 ∧ d.site ≠ .uk := by
          refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hlate <;> cases hlate
        obtain ⟨n0, v0, hps, hn0, hnv, w1, w2, w3, w4⟩ := corr_scan hFE hpl hend hq hs0 hlate
        have hv0 := Epilogue.passStart_v0 hps
        simp only [ite_true] at hv0
        have hge : n0 + v0 = a.ch := (corrMid hp w (g / L.block)).pass2 hT hps
        have h12 : 12 ≤ a.ch := (corrMid hp w (g / L.block)).ch_ge hT
        have ht : Progress.Cr.time p d n = passTime (endBase p) (n .shfl +
            Progress.Out.ballots (Progress.Cr.toE d.site))
            (Progress.Out.coll (Progress.Cr.toE d.site)) := by
          simp only [Progress.Cr.time, hpl, hend, hs0.1, hs0.2.1, hlate, ite_true, ite_false]
        rw [ht]
        cases hco : Progress.Out.coll (Progress.Cr.toE d.site) with
        | true =>
          obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ := Epilogue.coll_pos hFE (by
            show Progress.Out.coll (CorrWarp.epi d.site) = true
            rw [w3]; exact hco)
          have hq' : Epilogue.Pos p (g / L.block) l q (CorrWarp.epi d.site) := hq
          have hlf : l = true := by rw [← hq'.late, w3, w4]
          subst hlf
          obtain ⟨rfl, rfl⟩ := Epilogue.PassStart.same rfl hps hps'
          have ht' : passTime (endBase p) (n .shfl +
              Progress.Out.ballots (Progress.Cr.toE d.site)) true =
              endBase p + 2 * (n0 + q) := by simp only [passTime, ite_true]; omega
          have htg : corrTagS d.site = some (.scan (CorrWarp.epi d.site)) := by
            simp [corrTagS, w1, hco, w2]
          rw [hq1, ht', htg]
          exact .scan2 a n0 v0 q _ hT hps hq' hv0
        | false =>
          have htg : corrTagS d.site = none := by simp [corrTagS, w1, hco]
          rw [htg]
          simp only [passTime, Bool.false_eq_true, ite_false]
          exact .scan2Off a _ _ hT (by show a.ch ≤ _; omega) (by omega) (by omega)

/-- **Where a state of a correction warp stands.** -/
theorem corr_cls {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    SCls (corrMid hp w (g / L.block)) g 0 (((X.tr g).take k).countP Sched.isWarpColl)
      (Progress.time p L g σ) (corrTag p L g σ) := by
  rw [corr_cnt_eq hp hX hub hg hw8 hw hσ]
  have hR := (CorrWarp.good hp hX hw8 hg hw k).2 _ hσ
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, hv, -⟩ := hR
    simp only
    rw [hv, Nat.add_zero]
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      rw [hS.1]
      have ht : Progress.time p L g (.inl ⟨.sh j, x1, x2, x3⟩, n) = Progress.shPc j.val := by
        fin_cases j <;> rfl
      rw [ht]
      exact .start j
    case fence =>
      rw [hS.1]
      exact .scanOff 3 _ (by decide) (by show 172 < 256 + 6; decide)
        (by show 172 < _; rw [hprv, hsb]; omega)
    case bar =>
      rw [hS.1]
      exact .scanOff 3 _ (by decide) (by show 173 < 256 + 6; decide)
        (by show 173 < _; rw [hprv, hsb]; omega)
  · exact corr_role_cls hp hX hub hg hw8 hw hσ

/-- **A lane of a correction warp at its return.** -/
theorem corr_exit_cls {d : Correction.Control.D} {n : Cls → Nat} {l : Bool}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hs : d.site = .exit l) : SExitN (corrMid hp w (g / L.block)) g 0
      (((X.tr g).take k).countP Sched.isWarpColl) := by
  rw [corr_cnt_eq hp hX hub hg hw8 hw hσ]
  obtain ⟨r, ℓ, -, rv, hle, hrv, hFE, -⟩ := corr_open hp hX hub hg hw8 hw hσ
  have hs' : d.scheduler.site = .exit l := hs
  have hx : Epilogue.Fits.ExitAt p L g l (n .shfl) (n .vote - rv) := by
    simpa only [Epilogue.Fits, CorrWarp.toE, hs', CorrWarp.epi] using hFE
  have hin : inRound (Correction.Site.exit l).pc = false ∧
      tailR (Correction.Site.exit l) = false := by cases l <;> exact ⟨by decide, by decide⟩
  simp only [CorrWarp.RvAt, hs', hin.1, hin.2, Bool.false_eq_true, ite_false] at hrv
  show SExitN _ _ _ (n .shfl + n .vote)
  cases l with
  | false =>
    have hrv0 : rv = 0 := by simpa [Correction.Site.late] using hrv
    exact .inl ⟨_, _, hx, by omega⟩
  | true =>
    simp only [Correction.Site.late, ite_true] at hrv
    obtain ⟨R, bal, hP, hrv⟩ := hrv
    obtain ⟨a, hT, a1, a2⟩ := corr_tile hp hg hw hP
    refine .inr ⟨a, _, _, hT, hx, ?_⟩
    show _ = 0 + a.V + _
    omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
