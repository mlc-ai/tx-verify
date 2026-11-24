-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Positions of the correction warps' collectives

The correction warps' collectives are the output warp's scan, its ballot and the second pass,
and between the passes two rescale ballots per round. A state of the scheduler or the end is the
output warp's state of its pass with the ballot count shifted by the rescale ballots of the picked
tile in the second pass (`rvC`), which is the same on every lane of the CTA (`rvC_cta`); a state
of the rounds or the final stage is after the CTA's choice (`nC`) with the first pass's ballot and
at most the tile's rescale ballots, strictly fewer at a rescale ballot (`rt_band`). From these and
the output warp's position lemmas: `cshfl_lt_vote`, `cshfl_lt_exit`, `cvote_exit`, `cshfl_same`,
`cvote_same`, the facts the collective sources need. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (nC eband ePass eColl eEnd)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g h : Nat}

/-- The rescale ballots of the tile the first pass picked. -/
abbrev rvC (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : Nat :=
  rvN (Bs p L g (refV p L g R bal))

theorem rvC_cta (hp : Pre p L m) (hg : g < L.threads) (hh : h < L.threads)
    (hc : g / L.block = h / L.block) {R : Nat} {bal : BitVec 64} :
    rvC p L g R bal = rvC p L h R bal := by
  unfold rvC Bs blocks rowOff coords refV
  rw [ctaR_eq hp hg, ctaR_eq hp hh]
  simp only [Epilogue.ctaW, hc]

/-- The rounds and the final stage are at the output warp's first stage poll, past the used-K
read. -/
def rtSite (s : Site) : Bool := !(inRound s.pc || tailR s) || (epi s == .ready 0 && s.hasUk)

set_option maxRecDepth 100000 in
theorem rt_site_all : allSites.all rtSite = true := by decide +kernel

theorem rt_site {s : Site} (h : (inRound s.pc || tailR s) = true) :
    epi s = .ready 0 ∧ s.hasUk = true := by
  have := List.all_eq_true.mp rt_site_all s (mem_allSites s)
  simp only [rtSite, h, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-- **Where a state of the rounds or the final stage stands**: after the CTA's choice, with the
first pass's ballot and at most the tile's rescale ballots, strictly fewer at a rescale ballot. -/
theorem rt_band {d : D} {ns nv : Nat} (hF : CFits p L g d ns nv)
    (hrt : (inRound d.site.pc || tailR d.site) = true) :
    ∃ R bal, Picked p L g R bal ∧ ns = nC R bal ∧ 1 ≤ nv ∧ nv - 1 ≤ rvC p L g R bal ∧
      (d.site.isRvote = true → nv - 1 < rvC p L g R bal) := by
  obtain ⟨hep, huk⟩ := rt_site hrt
  obtain ⟨rv, hle, hr, hFE, hu⟩ := hF
  have hFE' := hFE
  simp only [Epilogue.Fits, toE, hep] at hFE'
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE'
  have hB := bs_ref hC h0 h1 (hu huk)
  obtain ⟨hPk, -, -, -, -, -, -, hns, hnv⟩ := hC
  refine ⟨R, bal, hPk, hns, by omega, ?_⟩
  have hnv' : nv - 1 = rv := by omega
  rw [hnv']
  unfold rvC
  rw [← hB]
  by_cases hi : inRound d.site.pc = true
  · simp only [RvAt, hi, ↓reduceIte] at hr
    obtain ⟨r, hr1, -, rfl⟩ := hr
    have hsv : sv d.site ≤ 2 := by unfold sv; split <;> split <;> omega
    have hB2 : ¬ Bs p L g d.v < 2 := by omega
    simp only [rvN, hB2, ↓reduceIte]
    refine ⟨by omega, fun hv => ?_⟩
    have : sv d.site ≤ 1 := by
      obtain ⟨s, v, k⟩ := d
      cases s with
      | rvote st => fin_cases st <;> simp [sv, Site.pc]
      | _ => simp [Site.isRvote] at hv
    omega
  · have ht : tailR d.site = true := by simpa [hi] using hrt
    simp only [RvAt, hi, ht, Bool.false_eq_true, ↓reduceIte] at hr
    refine ⟨by omega, fun hv => ?_⟩
    obtain ⟨s, v, k⟩ := d
    cases s with
    | rvote st => fin_cases st <;> exact absurd rfl hi
    | _ => simp [Site.isRvote] at hv

/-- **Where a state of the scheduler or the end stands**: in the first pass the output warp's
state with no rescale ballot; in the second pass with the picked tile's. -/
theorem sched_band {d : D} {ns nv : Nat} (hF : CFits p L g d ns nv)
    (hrt : (inRound d.site.pc || tailR d.site) = false) :
    (d.site.late = false ∧ Epilogue.Fits p L g (toE d) ns nv) ∨
      (d.site.late = true ∧ ∃ R bal, Picked p L g R bal ∧ rvC p L g R bal ≤ nv ∧
        Epilogue.Fits p L g (toE d) ns (nv - rvC p L g R bal)) := by
  obtain ⟨rv, hle, hr, hFE, -⟩ := hF
  simp only [Bool.or_eq_false_iff] at hrt
  rw [rvAt_out hrt.1 hrt.2] at hr
  cases hl : d.site.late <;> simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr
  · subst hr; exact .inl ⟨rfl, by rwa [Nat.sub_zero] at hFE⟩
  · obtain ⟨R, bal, hPk, hrv⟩ := hr
    refine .inr ⟨rfl, R, bal, hPk, ?_, ?_⟩
    · simpa only [rvC, ← hrv] using hle
    · simpa only [rvC, ← hrv] using hFE

/-- The output warp's sites of a correction site of the scheduler or the end are not the start
or the first stage poll; their pass is the site's. -/
def schedOk (s : Site) : Bool :=
  (inRound s.pc || tailR s) ||
    (ePass (epi s) == s.late && (!(Epilogue.Site.shfl (epi s) || Epilogue.Site.ballot (epi s) ||
      eEnd (epi s)) || (epi s != .start && eColl (epi s))))

set_option maxRecDepth 100000 in
theorem sched_ok_all : allSites.all schedOk = true := by decide +kernel

theorem sched_ok {s : Site} (h : (inRound s.pc || tailR s) = false) :
    ePass (epi s) = s.late ∧ ((epi s).shfl = true ∨ (epi s).ballot = true ∨ eEnd (epi s) = true →
      epi s ≠ .start ∧ eColl (epi s) = true) := by
  have := List.all_eq_true.mp sched_ok_all s (mem_allSites s)
  simp only [schedOk, h, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨h1, fun hc => ?_⟩
  rcases h2 with h2 | h2
  · rcases hc with hc | hc | hc <;> simp_all
  · exact h2

/-- A collective or end site of the scheduler is not in the rounds or the final stage. -/
theorem coll_out {s : Site} (h : (epi s).shfl = true ∨ (epi s).ballot = true ∨
    eEnd (epi s) = true) : (inRound s.pc || tailR s) = false := by
  cases s with
  | word k | down k | total k => cases k <;> simp_all [epi, eEnd] <;> decide
  | up k j => cases k <;> fin_cases j <;> decide
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> decide
  | _ => simp_all [epi, eEnd, Epilogue.Site.shfl, Epilogue.Site.ballot]

/-- The band of a collective or end state in the output warp's terms. -/
theorem coll_band {d : D} {ns nv : Nat} (hF : CFits p L g d ns nv)
    (hcol : (epi d.site).shfl = true ∨ (epi d.site).ballot = true ∨ eEnd (epi d.site) = true) :
    (d.site.late = false ∧ Epilogue.Fits p L g (toE d) ns nv ∧ (Epilogue.Site.ballot (epi d.site) =
        true → nv = 0) ∧ ∀ R bal, Picked p L g R bal → ns < nC R bal ∧
          ∀ l, epi d.site ≠ .exit l) ∨
    (d.site.late = true ∧ ∃ R bal, Picked p L g R bal ∧ rvC p L g R bal + 1 ≤ nv ∧
      Epilogue.Fits p L g (toE d) ns (nv - rvC p L g R bal) ∧ nC R bal ≤ ns ∧
      (eEnd (epi d.site) = true → nC R bal + 7 ≤ ns)) := by
  have hrt := coll_out hcol
  obtain ⟨hpass, hco⟩ := sched_ok hrt
  obtain ⟨h0, hcl⟩ := hco hcol
  rcases sched_band hF hrt with ⟨hl, hFE⟩ | ⟨hl, R, bal, hPk, hle, hFE⟩
  · rcases eband hFE h0 with ⟨hp1, hb, hk⟩ | ⟨hp2, -⟩
    · exact .inl ⟨hl, hFE, hb, fun R bal hPk => ⟨(hk R bal hPk).2.1 hcl, (hk R bal hPk).2.2⟩⟩
    · simp only [toE] at hp2; rw [hpass, hl] at hp2; cases hp2
  · rcases eband hFE h0 with ⟨hp1, -⟩ | ⟨hp2, hnv, R', bal', hPk', h6, h7⟩
    · simp only [toE] at hp1; rw [hpass, hl] at hp1; cases hp1
    · obtain ⟨rfl, rfl⟩ := hPk.unique hPk'
      exact .inr ⟨hl, R, bal, hPk, by omega, hFE, h6, h7⟩

/-- The vote sites: the scheduler's ballots and the rescale ballots. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.isVote (s : Site) : Bool :=
  (epi s).ballot || s.isRvote

theorem rvote_rt {s : Site} (h : s.isRvote = true) : (inRound s.pc || tailR s) = true := by
  cases s with
  | rvote st => fin_cases st <;> rfl
  | _ => simp [Site.isRvote] at h

/-- **A shuffle state comes before every ballot state with at least its ballot count.** -/
theorem cshfl_lt_vote (hp : Pre p L m) (hg : g < L.threads) (hh : h < L.threads)
    (hc : g / L.block = h / L.block) {d d' : D} {ns nv ns' nv' : Nat}
    (hF : CFits p L g d ns nv) (hs : (epi d.site).shfl = true)
    (hF' : CFits p L h d' ns' nv') (hs' : d'.site.isVote = true) (hv : nv ≤ nv') : ns < ns' := by
  rcases coll_band hF (.inl hs) with ⟨hl, hFE, -, hk⟩ | ⟨hl, R, bal, hPk, hle, hFE, h6, -⟩
  · by_cases hr : d'.site.isRvote = true
    · obtain ⟨R, bal, hPk, hns, -⟩ := rt_band hF' (rvote_rt hr)
      have := (hk R bal (Epilogue.Picked.cta hc.symm hPk)).1
      omega
    · have hb : (epi d'.site).ballot = true := by simpa [Site.isVote, hr] using hs'
      rcases coll_band hF' (.inr (.inl hb)) with ⟨hl', hFE', -, -⟩ |
        ⟨hl', R, bal, hPk, -, -, h6, -⟩
      · obtain ⟨l, hlv⟩ : ∃ l, (toE d').site = .vote l := by
          simp only [toE]; revert hb; cases epi d'.site <;> simp [Epilogue.Site.ballot]
        exact Epilogue.shfl_lt_vote hFE hFE' hc hs hlv hv
      · have := (hk R bal (Epilogue.Picked.cta hc.symm hPk)).1
        omega
  · by_cases hr : d'.site.isRvote = true
    · obtain ⟨R', bal', hPk', hns, h1, h2, h3⟩ := rt_band hF' (rvote_rt hr)
      obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
      have := h3 hr
      rw [← rvC_cta hp hg hh hc] at this
      omega
    · have hb : (epi d'.site).ballot = true := by simpa [Site.isVote, hr] using hs'
      rcases coll_band hF' (.inr (.inl hb)) with ⟨hl', -, hb0, -⟩ |
        ⟨hl', R', bal', hPk', hle', hFE', -⟩
      · have := hb0 hb; omega
      · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
        rw [← rvC_cta hp hg hh hc] at hle' hFE'
        obtain ⟨l, hlv⟩ : ∃ l, (toE d').site = .vote l := by
          simp only [toE]; revert hb; cases epi d'.site <;> simp [Epilogue.Site.ballot]
        exact Epilogue.shfl_lt_vote hFE hFE' hc hs hlv (by omega)

/-- The return's reference in the output warp's terms. -/
theorem exit_at {d : D} {ns nv : Nat} {l : Bool} (hF : CFits p L g d ns nv)
    (hs : epi d.site = .exit l) : ∃ nvx, Epilogue.Fits.ExitAt p L g l ns nvx := by
  have hcol : (epi d.site).shfl = true ∨ (epi d.site).ballot = true ∨ eEnd (epi d.site) = true :=
    .inr (.inr (by rw [hs]; rfl))
  rcases coll_band hF hcol with ⟨-, hFE, -⟩ | ⟨-, R, bal, -, -, hFE, -⟩ <;>
    simp only [Epilogue.Fits, toE, hs] at hFE <;> exact ⟨_, hFE⟩

/-- **A shuffle state comes before every return.** -/
theorem cshfl_lt_exit (hc : g / L.block = h / L.block) {d d' : D} {ns nv ns' nv' : Nat} {l : Bool}
    (hF : CFits p L g d ns nv) (hs : (epi d.site).shfl = true)
    (hF' : CFits p L h d' ns' nv') (hs' : epi d'.site = .exit l) : ns < ns' := by
  obtain ⟨nvx, hx⟩ := exit_at hF' hs'
  rcases coll_band hF (.inl hs) with ⟨-, hFE, -⟩ | ⟨-, R, bal, -, -, hFE, -⟩ <;>
    exact Epilogue.shfl_lt_exit hFE hc hs hx

/-- **No lane returns before a ballot that another lane of its warp makes.** -/
theorem cvote_exit (hp : Pre p L m) (hg : g < L.threads) (hh : h < L.threads)
    (hc : g / L.block = h / L.block) {d d' : D} {ns nv ns' nv' : Nat} {l : Bool}
    (hF : CFits p L g d ns nv) (hs : d.site.isVote = true)
    (hF' : CFits p L h d' ns' nv') (hs' : epi d'.site = .exit l) (hv : nv' ≤ nv) : False := by
  have hE' : eEnd (epi d'.site) = true := by rw [hs']; rfl
  by_cases hr : d.site.isRvote = true
  · obtain ⟨R, bal, hPk, -, h1, -, h3⟩ := rt_band hF (rvote_rt hr)
    have := h3 hr
    rcases coll_band hF' (.inr (.inr hE')) with ⟨-, -, -, hk⟩ | ⟨-, R', bal', hPk', hle', -⟩
    · exact (hk R bal (Epilogue.Picked.cta hc hPk)).2 l hs'
    · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
      rw [← rvC_cta hp hg hh hc] at hle'
      omega
  · have hb : (epi d.site).ballot = true := by simpa [Site.isVote, hr] using hs
    obtain ⟨l0, hlv⟩ : ∃ l, (toE d).site = .vote l := by
      simp only [toE]; revert hb; cases epi d.site <;> simp [Epilogue.Site.ballot]
    obtain ⟨nvx, hx⟩ := exit_at hF' hs'
    rcases coll_band hF (.inr (.inl hb)) with ⟨hl, hFE, hb0, hk⟩ | ⟨hl, R, bal, hPk, hle, hFE, -⟩
    · rcases coll_band hF' (.inr (.inr hE')) with ⟨-, hFE', -⟩ | ⟨-, R', bal', hPk', hle', -⟩
      · simp only [Epilogue.Fits, toE, hs'] at hFE'
        exact Epilogue.vote_exit hFE hc hlv hFE' hv
      · have := hb0 hb; omega
    · rcases coll_band hF' (.inr (.inr hE')) with ⟨-, -, -, hk'⟩ |
        ⟨-, R', bal', hPk', hle', hFE', -⟩
      · exact (hk' R bal (Epilogue.Picked.cta hc hPk)).2 l hs'
      · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
        rw [← rvC_cta hp hg hh hc] at hle' hFE'
        simp only [Epilogue.Fits, toE, hs'] at hFE'
        exact Epilogue.vote_exit hFE hc hlv hFE' (by omega)

/-- The output warp's site of a scan shuffle determines the correction site. -/
theorem epi_shfl_inj {s s' : Site} (hs : (epi s).shfl = true) (h : epi s' = epi s) : s' = s := by
  cases s <;> simp [epi, Epilogue.Site.shfl] at hs <;> cases s' <;> simp_all [epi]

/-- **Two lanes at shuffle states with one shuffle count are at one site.** -/
theorem cshfl_same (hc : g / L.block = h / L.block) {d d' : D} {ns nv ns' nv' : Nat}
    (hF : CFits p L g d ns nv) (hs : (epi d.site).shfl = true)
    (hF' : CFits p L h d' ns' nv') (hs' : (epi d'.site).shfl = true) (hn : ns = ns') :
    d'.site = d.site := by
  have E : ∀ {k : Nat} {dd : D} {a b : Nat}, CFits p L k dd a b → (epi dd.site).shfl = true →
      ∃ c, Epilogue.Fits p L k (toE dd) a c := by
    intro k dd a b hF hs
    rcases coll_band hF (.inl hs) with ⟨-, hFE, -⟩ | ⟨-, R, bal, -, -, hFE, -⟩ <;> exact ⟨_, hFE⟩
  obtain ⟨_, hFE⟩ := E hF hs
  obtain ⟨_, hFE'⟩ := E hF' hs'
  exact epi_shfl_inj hs (Epilogue.shfl_same hFE hFE' hc hs hs' hn)

/-- **Two ballot states of lanes of one CTA with one ballot count**, the first at a scheduler
ballot, are at one site with one shuffle count. -/
theorem cvote_same (hp : Pre p L m) (hg : g < L.threads) (hh : h < L.threads)
    (hc : g / L.block = h / L.block) {d d' : D} {ns nv ns' nv' : Nat} {l : Bool}
    (hF : CFits p L g d ns nv) (hs : d.site = .vote l)
    (hF' : CFits p L h d' ns' nv') (hs' : d'.site.isVote = true) (hv : nv = nv') :
    d'.site = d.site ∧ ns' = ns := by
  have hb : (epi d.site).ballot = true := by rw [hs]; rfl
  have hlv : (toE d).site = .vote l := by simp [toE, hs, epi]
  by_cases hr : d'.site.isRvote = true
  · exfalso
    obtain ⟨R, bal, hPk, -, h1, h2, h3⟩ := rt_band hF' (rvote_rt hr)
    have := h3 hr
    rcases coll_band hF (.inr (.inl hb)) with ⟨-, -, hb0, -⟩ | ⟨-, R', bal', hPk', hle, -⟩
    · have := hb0 hb; omega
    · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc.symm hPk).unique hPk'
      rw [rvC_cta hp hg hh hc] at hle
      omega
  · have hb' : (epi d'.site).ballot = true := by simpa [Site.isVote, hr] using hs'
    obtain ⟨l', hlv'⟩ : ∃ l, (toE d').site = .vote l := by
      simp only [toE]; revert hb'; cases epi d'.site <;> simp [Epilogue.Site.ballot]
    have fin : ∀ c c', Epilogue.Fits p L g (toE d) ns c → Epilogue.Fits p L h (toE d') ns' c' →
        c = c' → d'.site = d.site ∧ ns' = ns := by
      intro c c' h1 h2 hcc
      obtain ⟨e1, e2⟩ := Epilogue.vote_same h1 h2 hc hlv hlv' hcc
      refine ⟨?_, e2⟩
      have : epi d'.site = epi d.site := by simpa [toE] using e1
      rw [hs] at this ⊢
      obtain ⟨s, v, k⟩ := d'
      cases s <;> simp_all [epi]
    rcases coll_band hF (.inr (.inl hb)) with ⟨hl, hFE, hb0, -⟩ | ⟨hl, R, bal, hPk, hle, hFE, -⟩ <;>
      rcases coll_band hF' (.inr (.inl hb')) with ⟨hl', hFE', hb0', -⟩ |
        ⟨hl', R', bal', hPk', hle', hFE', -⟩
    · exact fin _ _ hFE hFE' hv
    · have := hb0 hb; omega
    · have := hb0' hb'; omega
    · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
      rw [← rvC_cta hp hg hh hc] at hle' hFE'
      exact fin _ _ hFE hFE' (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
