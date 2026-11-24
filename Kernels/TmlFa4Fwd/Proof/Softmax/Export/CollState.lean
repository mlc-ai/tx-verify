-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollRound
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.Start0
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every state of a softmax warp stands in its schedule of collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk slotOf bandP primeBase endBase scanBase bmax
  passTime)
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain preR finR
  allSites mem_allSites)

open SoftColl

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The collective a softmax site is at. -/
def softTagS (s : Softmax.Site) : Option (STag Softmax.Site) :=
  if s.wcoll then (if s.rcoll then some (.mid s) else some (.scan (SmWarp.epi s))) else none

/-- The collective a thread state of a softmax warp is at. -/
def softTag (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) :
    Option (STag Softmax.Site) :=
  match σ with
  | (.inl s, _) => match s.site with
    | .sh j => some (.start j) | .elect j => some (.init j) | _ => none
  | (.inr ⟨.softmax, d⟩, _) => softTagS d.site
  | _ => none

theorem softTag_isSome (σ : (thread p L g).D) : (softTag p L g σ).isSome = softAt p L g σ := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · simp only [softTag, softAt]; cases s.site <;> rfl
  all_goals first
    | rfl
    | (simp only [softTag, softAt, softTagS]
       cases d.site.wcoll <;> cases d.site.rcoll <;> rfl)

/-- The stage of softmax warp `w`. -/
def stW (w : Nat) : Nat := if w < 4 then 0 else 1

theorem stW_lt (w : Nat) : stW w < 2 := by unfold stW; split <;> omega

/-- The rounds of softmax warp `w` of CTA `c`. -/
abbrev softR (p : Params) (L : Launch) (w c : Nat) : Mid p L Softmax.Site SoftRun :=
  softMid p L w c (stW w) (stW_lt w)

private theorem end_site {s : Softmax.Site} {l : Bool} {o : Nat}
    (h : Progress.Sm.endOff s = some (l, o)) :
    Progress.Sm.late s = l ∧ SmWarp.epi s = .exit l ∧ softTagS s = none := by
  cases s <;> simp only [Progress.Sm.endOff, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- A scan site. -/
private theorem soft_scan {d : Softmax.D} {ns nv : Nat}
    (hF : Epilogue.Fits p L g (SmWarp.toE d) ns nv) {l : Bool}
    (hs : (Progress.Sm.place (Progress.Sm.stage L g) d.site).isSome = false)
    (hpre : Progress.Sm.pre d.site = none) (hend : Progress.Sm.endOff d.site = none)
    (h1 : d.site ≠ .setmax) (h2 : d.site ≠ .bar1) (hl : Progress.Sm.late d.site = l) :
    ∃ n0 v0, Epilogue.PassStart p L g l n0 v0 ∧ n0 ≤ ns ∧
      nv = v0 + Progress.Out.ballots (Progress.Sm.toE d.site) ∧
      d.site.wcoll = Progress.Out.coll (Progress.Sm.toE d.site) ∧ d.site.rcoll = false ∧
      SmWarp.epi d.site = Progress.Sm.toE d.site ∧
      (Progress.Sm.toE d.site).late = l ∧ d.site.rem = 0 := by
  subst hl
  obtain ⟨s, v, kk, acc⟩ := d
  have hst : Progress.Sm.stage L g = 0 ∨ Progress.Sm.stage L g = 1 := by
    unfold Progress.Sm.stage; split <;> simp
  cases s <;> simp only [Progress.Sm.pre, Progress.Sm.endOff, reduceCtorEq, ne_eq,
    not_true_eq_false] at hpre hend h1 h2 <;>
    first
      | (simp only [Epilogue.Fits, SmWarp.toE, SmWarp.epi] at hF
         obtain ⟨r, n0, v0, hP, -, h3, h4, -⟩ := hF
         exact ⟨n0, v0, hP, by omega, by
           simp only [Progress.Sm.toE, Progress.Out.ballots]; omega, rfl, rfl, rfl, rfl, rfl⟩)
      | (exfalso
         rcases hst with hst | hst <;> rw [hst] at hs <;>
           simp [Progress.Sm.place] at hs)

private theorem late_rem {s : Softmax.Site} (h : Progress.Sm.late s = true) : s.rem = 0 := by
  cases s <;> first | rfl | cases h

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {w : Nat} (hw8 : w < 8)
  (hw : Prologue.warpIndex L g = w)
include hp hX hFw hub hg hw8 hw

omit hFw in
/-- What a role state's reference gives. -/
theorem soft_open {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    ∃ c rb rp, RefQ p L g d.scheduler c rb rp ∧ SmWarp.Linked n c ∧
      SmWarp.SFits p L g d.scheduler (n .shfl) (n .vote) ∧
      ((X.tr g).take k).countP roundColl + d.scheduler.site.rem =
        startEl w + 2 * c (.arrive 96) := by
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  have hI := soft_coll_inv hp hX hub hg hw8 hw k _ hσ
  simp only [CollInv] at hI
  obtain ⟨-, hR⟩ := (SmWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR hub0
  change (_ : Nat) + d.scheduler.site.rem = _ at hI
  have e96 : c (.arrive 96) = n (.soft (.arrive 96)) := hLk _ rfl
  rw [← e96] at hI
  exact ⟨c, rb, rp, hQ, hLk, hF, hI⟩

omit hub hg in
/-- The rounds of a state past them. -/
theorem soft_late_T {d : Softmax.D} {n : Cls → Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hn : σ.2 = n)
    {c : Softmax.Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d c rb rp)
    (hLk : SmWarp.Linked n c) (hlate : Progress.Sm.late d.site = true) :
    SoftRounds p L g (c (.arrive 96)) := by
  subst hn
  have hA := hQ.cnt (.arrive 96) rfl
  obtain ⟨t1, t2, t3, t4⟩ := rnd2 (Softmax.lz L g)
  simp only [passed, t3, t4, Nat.mul_one] at hA
  change c (.arrive 96) = cA (Softmax.lz L g) d.site + rb + rp at hA
  have hbk := List.all_eq_true.mp (late_tab.1 (Softmax.lz L g)) d.site (mem_allSites _)
  rw [hlate] at hbk
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hbk
  obtain ⟨⟨⟨hcB, hcA⟩, hcN⟩, -⟩ := hbk
  have h80 := hQ.cnt (.acquire 80) rfl
  have hnb := hQ.cnt .nb rfl
  obtain ⟨t5, t6⟩ := late_tab.2 (Softmax.lz L g)
  simp only [passed, t1, t2, t5, t6, Nat.mul_one] at h80 hnb
  change c (.acquire 80) = cB (Softmax.lz L g) d.site + rb + rp at h80
  rw [hcB] at h80
  rw [hcA] at hA
  rw [hcN] at hnb
  subst hw
  refine soft_late_rounds hp hX hFw hw8 (k := k) ?_ ?_
  · rw [soft_isBarId hw8, count hσ, ← hLk _ rfl, hnb, hA]; omega
  · rw [sobj, soft_okPolls hw8, count hσ, ← hLk _ rfl, h80, hA]

/-- A role state. -/
private theorem soft_role_cls {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    SCls (softR p L w (g / L.block)) g (startEl w)
      (n .shfl + n .vote + ((X.tr g).take k).countP roundColl)
      (Progress.Sm.time p L g d.scheduler n) (softTagS d.scheduler.site) := by
  obtain ⟨c, rb, rp, hQ, hLk, hF, hI⟩ := soft_open hp hX hub hg hw8 hw hσ
  have e80 : c (.acquire 80) = n (.soft (.acquire 80)) := hLk _ rfl
  generalize ((X.tr g).take k).countP roundColl = E at hI ⊢
  obtain ⟨hFE, hu⟩ := hF
  generalize d.scheduler = d at *
  have hA := hQ.cnt (.arrive 96) rfl
  obtain ⟨t1, t2, t3, t4⟩ := rnd2 (Softmax.lz L g)
  simp only [passed, t3, t4, Nat.mul_one] at hA
  change c (.arrive 96) = cA (Softmax.lz L g) d.site + rb + rp at hA
  have hst : stW w = Progress.Sm.stage L g := by unfold stW Progress.Sm.stage; rw [hw]
  have hst2 : stW w ∈ [0, 1] := by unfold stW; split <;> simp
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
  cases hpl : Progress.Sm.place (stW w) d.site with
  | some x =>
    -- the rounds
    obtain ⟨h1, h2, h3, h4⟩ := place_facts d.site hst2 hpl (Softmax.lz L g)
    simp only [Epilogue.Fits, SmWarp.toE, h1] at hFE
    obtain ⟨R, bal, hC, h5, h6⟩ := hFE
    obtain ⟨eB, eP⟩ := nBP hC h5 h6 (hu h2)
    obtain ⟨hP, -, -, -, -, -, -, hns, hnv⟩ := hC
    obtain ⟨a, hT, a1, a2, a3⟩ := soft_tile hp hg hw hP
    rw [← eB] at a2
    rw [← eP] at a3
    have hM := round_M (n := n) hQ hst a2 a3 hT.2.2.1 e80.symm hpl (E := E - startEl w) (by omega)
    have hN : n .shfl + n .vote + E = startEl w + (a.ch + (E - startEl w)) := by omega
    have htg : softTagS d.site = (if d.site.rcoll then some d.site else none).map .mid := by
      unfold softTagS
      rw [h4]
      cases d.site.rcoll <;> rfl
    rw [hN, htg]
    exact .mid a _ _ _ hT hM
  | none =>
    have hplS : (Progress.Sm.place (Progress.Sm.stage L g) d.site).isSome = false := by
      rw [← hst, hpl]; rfl
    cases hlate : Progress.Sm.late d.site with
    | false =>
      have h0 := List.all_eq_true.mp (List.all_eq_true.mp (none_tab (Softmax.lz L g)) d.site
        (mem_allSites _)) _ hst2
      rw [hpl, hlate] at h0
      simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h0
      obtain ⟨⟨hpreR, hA0⟩, hrem⟩ := h0
      obtain ⟨rfl, rfl⟩ := hQ.pre hpreR
      have hE : E = startEl w := by omega
      subst hE
      rw [show n .shfl + n .vote + startEl w = startEl w + (n .shfl + n .vote) by omega]
      cases hpre : Progress.Sm.pre d.site with
      | some o =>
        -- the request's reads
        have ht : Progress.Sm.time p L g d n = primeBase p + o := by
          simp only [Progress.Sm.time, ← hst, hpl, hpre]
        have ho : o ≤ 3 := by
          revert hpre
          cases d.site <;> simp [Progress.Sm.pre] <;> omega
        have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal (SmWarp.toE d) (n .shfl) (n .vote) := by
          have h2' := hFE
          revert hpre
          cases hs : d.site <;> simp only [Progress.Sm.pre, reduceCtorEq, false_implies] <;>
            intro _ <;> simp only [Epilogue.Fits, SmWarp.toE, hs, SmWarp.epi] at h2'
          · exact h2'
          all_goals (obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩)
        obtain ⟨R, bal, hP, -, -, -, -, -, -, hns, hnv⟩ := hC
        obtain ⟨a, hT, a1, -⟩ := soft_tile hp hg hw hP
        have htg : softTagS d.site = (none : Option Softmax.Site).map .mid := by
          revert hpre
          cases d.site <;> simp [Progress.Sm.pre, softTagS, Softmax.Site.wcoll]
        rw [ht, htg]
        exact .mid a _ _ none hT (.inl ⟨rfl, by omega, by omega⟩)
      | none =>
        cases hend : Progress.Sm.endOff d.site with
        | some x =>
          obtain ⟨l, o⟩ := x
          obtain ⟨hll, hsite⟩ := end_site hend
          rw [hlate] at hll
          subst hll
          simp only [Epilogue.Fits, hsite.1] at hFE
          rw [hsite.2]
          exact .end1 _ _ _ hFE
        | none =>
          by_cases h1 : d.site = .setmax ∨ d.site = .bar1
          · have hf : n .shfl = 3 ∧ n .vote = 0 := by
              rcases h1 with h | h <;>
                simpa only [Epilogue.Fits, SmWarp.toE, h, SmWarp.epi] using hFE
            have ht : Progress.Sm.time p L g d n < scanBase + 6 := by
              rcases h1 with h | h <;>
                simp only [Progress.Sm.time, h, Progress.Sm.place, Progress.Sm.pre,
                  Progress.Sm.endOff, ite_true, ite_false, reduceCtorEq] <;> omega
            have htg : softTagS d.site = none := by rcases h1 with h | h <;> rw [h] <;> rfl
            rw [htg, hf.1, hf.2]
            exact .scanOff 3 _ (by omega) (by omega) (by omega)
          · -- the first pass
            obtain ⟨h1, h2⟩ := not_or.mp h1
            obtain ⟨n0, v0, hps, hn0, hnv, w1, w2, w3, w4, -⟩ :=
              soft_scan hFE hplS hpre hend h1 h2 hlate
            have hbd := Epilogue.fits_coll_le hp hFE (by
              show (SmWarp.epi d.site).late = false
              rw [w3, w4])
            simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps
            have ht : Progress.Sm.time p L g d n = passTime scanBase (n .shfl +
                Progress.Out.ballots (Progress.Sm.toE d.site))
                (Progress.Out.coll (Progress.Sm.toE d.site)) := by
              simp only [Progress.Sm.time, ← hst, hpl, hpre, hend, h1, h2, hlate,
                Bool.false_eq_true, ite_false]
            rw [ht]
            cases hco : Progress.Out.coll (Progress.Sm.toE d.site) with
            | true =>
              obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ := Epilogue.coll_pos hFE (by
                show Progress.Out.coll (SmWarp.epi d.site) = true
                rw [w3]; exact hco)
              have hq' : Epilogue.Pos p (g / L.block) l q (SmWarp.epi d.site) := hq
              have hll : l = false := by rw [← hq'.late, w3, w4]
              subst hll
              simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps'
              have hN : n .shfl + n .vote = 3 + q := by omega
              have ht' : passTime scanBase (n .shfl +
                  Progress.Out.ballots (Progress.Sm.toE d.site)) true =
                  scanBase + 2 * (3 + q) := by simp only [passTime, ite_true]; omega
              have htg : softTagS d.site = some (.scan (SmWarp.epi d.site)) := by
                simp [softTagS, w1, hco, w2]
              rw [hN, ht', htg]
              exact .scan q _ hq' (by omega)
            | false =>
              have htg : softTagS d.site = none := by simp [softTagS, w1, hco]
              rw [htg]
              simp only [passTime, Bool.false_eq_true, ite_false]
              exact .scanOff _ _ (by omega) (by omega) (by omega)
    | true =>
      have hTR : SoftRounds p L g (c (.arrive 96)) :=
        soft_late_T hp hX hFw hw8 hw hσ rfl hQ hLk hlate
      have hrem : d.site.rem = 0 := late_rem hlate
      obtain ⟨R, bal, hP, hTT⟩ := hTR
      obtain ⟨a, hT, a1, a2, a3⟩ := soft_tile hp hg hw hP
      have haT : a.T = c (.arrive 96) := by rw [a3, a2]; exact hTT
      have hpre : Progress.Sm.pre d.site = none := by
        revert hlate; cases d.site <;> simp [Progress.Sm.late, Progress.Sm.pre]
      have hN0 : n .shfl + n .vote + E = startEl w + 2 * a.T + (n .shfl + n .vote) := by
        clear * - hI hrem haT
        omega
      rw [hN0]
      cases hend : Progress.Sm.endOff d.site with
      | some x =>
        obtain ⟨l, o⟩ := x
        obtain ⟨hll, hsite⟩ := end_site hend
        rw [hlate] at hll
        subst hll
        simp only [Epilogue.Fits, hsite.1] at hFE
        rw [hsite.2]
        exact .end2 a _ _ _ hT hFE
      | none =>
        have h1 : d.site ≠ .setmax := by rintro h; rw [h] at hlate; cases hlate
        have h2 : d.site ≠ .bar1 := by rintro h; rw [h] at hlate; cases hlate
        obtain ⟨n0, v0, hps, hn0, hnv, w1, w2, w3, w4, -⟩ :=
          soft_scan hFE hplS hpre hend h1 h2 hlate
        have hv0 := Epilogue.passStart_v0 hps
        simp only [ite_true] at hv0
        have hge : n0 + v0 = a.ch := (softR p L w (g / L.block)).pass2 hT hps
        have h12 : 12 ≤ a.ch := (softR p L w (g / L.block)).ch_ge hT
        have ht : Progress.Sm.time p L g d n = passTime (endBase p) (n .shfl +
            Progress.Out.ballots (Progress.Sm.toE d.site))
            (Progress.Out.coll (Progress.Sm.toE d.site)) := by
          simp only [Progress.Sm.time, ← hst, hpl, hpre, hend, h1, h2, hlate, ite_true, ite_false]
        rw [ht]
        cases hco : Progress.Out.coll (Progress.Sm.toE d.site) with
        | true =>
          obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ := Epilogue.coll_pos hFE (by
            show Progress.Out.coll (SmWarp.epi d.site) = true
            rw [w3]; exact hco)
          have hq' : Epilogue.Pos p (g / L.block) l q (SmWarp.epi d.site) := hq
          have hll : l = true := by rw [← hq'.late, w3, w4]
          subst hll
          obtain ⟨rfl, rfl⟩ := Epilogue.PassStart.same rfl hps hps'
          have ht' : passTime (endBase p) (n .shfl +
              Progress.Out.ballots (Progress.Sm.toE d.site)) true =
              endBase p + 2 * (n0 + q) := by simp only [passTime, ite_true]; omega
          have htg : softTagS d.site = some (.scan (SmWarp.epi d.site)) := by
            simp [softTagS, w1, hco, w2]
          rw [hq1, ht', htg]
          exact .scan2 a n0 v0 q _ hT hps hq' hv0
        | false =>
          have htg : softTagS d.site = none := by simp [softTagS, w1, hco]
          rw [htg]
          simp only [passTime, Bool.false_eq_true, ite_false]
          exact .scan2Off a _ _ hT (by show a.ch ≤ _; omega) (by omega) (by omega)

/-- **Where a state of a softmax warp stands.** -/
theorem soft_cls {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    SCls (softR p L w (g / L.block)) g (startEl w)
      (((X.tr g).take k).countP Sched.isWarpColl) (Progress.time p L g σ) (softTag p L g σ) := by
  rw [soft_cnt_eq hp hX hub hg hw8 hw hσ]
  have hR := (SmWarp.good hp hX hw8 hg hw k).2 _ hσ
  have hI := soft_coll_inv hp hX hub hg hw8 hw k _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, hv, -⟩ := hR
    simp only [CollInv] at hI
    rw [hI]
    simp only
    rw [hv]
    have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
    have hsb : scanBase = 256 := rfl
    obtain ⟨site, x1, x2, x3⟩ := s
    have mid3 : site = .fence ∨ site = .bar → n .shfl = 3 → SCls (softR p L w (g / L.block)) g
        (startEl w) (n .shfl + 0 + startCnt w site)
        (Progress.time p L g (.inl ⟨site, x1, x2, x3⟩, n))
        (softTag p L g (.inl ⟨site, x1, x2, x3⟩, n)) := by
      intro hs h3
      rw [h3, show 3 + 0 + startCnt w site = startEl w + 3 by
        rcases hs with rfl | rfl <;> simp only [startCnt] <;> omega]
      have ht : Progress.time p L g (.inl ⟨site, x1, x2, x3⟩, n) ≤ 173 := by
        rcases hs with rfl | rfl
        · show 172 ≤ 173; decide
        · show 173 ≤ 173; decide
      have htg : softTag p L g (.inl ⟨site, x1, x2, x3⟩, n) = none := by
        rcases hs with rfl | rfl <;> rfl
      rw [htg]
      exact .scanOff 3 _ (by omega) (by omega) (by omega)
    have sh : ∀ j : Fin 3, n .shfl = j.val → SCls (softR p L w (g / L.block)) g
        (startEl w) (n .shfl + 0 + startCnt w (.sh j))
        (Progress.time p L g (.inl ⟨.sh j, x1, x2, x3⟩, n))
        (softTag p L g (.inl ⟨.sh j, x1, x2, x3⟩, n)) := by
      intro j h3
      rw [h3, show j.val + 0 + startCnt w (.sh j) = j.val from rfl]
      have ht : Progress.time p L g (.inl ⟨.sh j, x1, x2, x3⟩, n) = Progress.shPc j.val := by
        fin_cases j <;> rfl
      rw [ht]
      exact .start j
    by_cases h0 : w = 0
    · subst h0
      simp only [SmWarp.StartW, ite_true] at hS
      cases site with
      | sh j => exact sh j hS.1
      | fence => exact mid3 (.inl rfl) hS.1
      | bar => exact mid3 (.inr rfl) hS.1
      | elect j =>
        rw [show n .shfl + 0 + startCnt 0 (.elect j) = 3 + j.val by rw [hS.1]; rfl]
        exact .init j rfl
      | init q =>
        rw [show n .shfl + 0 + startCnt 0 (.init q) = 3 + startCnt 0 (.init q) by rw [hS.1]]
        obtain ⟨q1, q2⟩ := init_pc q
        exact .initOff _ _ rfl q1 q2
      | enter r => simp [StartAt0] at hS
    · simp only [SmWarp.StartW, h0, ite_false] at hS
      cases site <;> simp only [StartAt] at hS
      · exact sh _ hS.1
      · exact mid3 (.inl rfl) hS.1
      · exact mid3 (.inr rfl) hS.1
  · exact soft_role_cls hp hX hFw hub hg hw8 hw hσ

/-- **A lane of a softmax warp at its return.** -/
theorem soft_exit_cls {d : Softmax.Control.D} {n : Cls → Nat} {l : Bool}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)))
    (hs : d.site = .exit l) : SExitN (softR p L w (g / L.block)) g (startEl w)
      (((X.tr g).take k).countP Sched.isWarpColl) := by
  rw [soft_cnt_eq hp hX hub hg hw8 hw hσ]
  obtain ⟨c, rb, rp, hQ, hLk, ⟨hFE, -⟩, hI⟩ := soft_open hp hX hub hg hw8 hw hσ
  have hs' : d.scheduler.site = .exit l := hs
  have hrem : d.scheduler.site.rem = 0 := by rw [hs']; rfl
  have hx : Epilogue.Fits.ExitAt p L g l (n .shfl) (n .vote) := by
    simpa only [Epilogue.Fits, SmWarp.toE, hs', SmWarp.epi] using hFE
  show SExitN _ _ _ (n .shfl + n .vote + _)
  cases l with
  | false =>
    have hb := List.all_eq_true.mp (List.all_eq_true.mp (none_tab (Softmax.lz L g))
      d.scheduler.site (mem_allSites _)) 0 (by simp)
    rw [hs'] at hb
    simp only [Progress.Sm.place, Progress.Sm.late, Option.isSome_none, Bool.false_or,
      Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨⟨hpreR, hA0⟩, -⟩ := hb
    obtain ⟨rfl, rfl⟩ := hQ.pre (by rw [hs']; exact hpreR)
    have hA := hQ.cnt (.arrive 96) rfl
    simp only [passed, Nat.zero_mul, Nat.add_zero] at hA
    change c (.arrive 96) = cA (Softmax.lz L g) d.scheduler.site at hA
    rw [hs', hA0] at hA
    exact .inl ⟨_, _, hx, by clear * - hA hI hrem; omega⟩
  | true =>
    obtain ⟨R, bal, hP, hTT⟩ := soft_late_T hp hX hFw hw8 hw hσ rfl hQ hLk
      (by rw [hs']; rfl)
    obtain ⟨a, hT, a1, a2, a3⟩ := soft_tile hp hg hw hP
    have haT : a.T = c (.arrive 96) := by rw [a3, a2]; exact hTT
    refine .inr ⟨a, _, _, hT, hx, ?_⟩
    show _ = startEl w + 2 * a.T + _
    clear * - hI hrem haT
    omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
