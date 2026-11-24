-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.CtlEv
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Place
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Lib.ThreadTime
import Kernels.TmlFa4Fwd.Proof.Progress.CorrPre
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Lemmas.Kernel.Safety.Schedule
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane short of a barrier event is early

A correction lane that has made no more events on a named barrier than a place of its tile has
passed has not exited and is no later than the place (`corr_bar_lag`); one that has made no
barrier-2 event is no later than its first (`corr_bar2_first`), and one that has made at most one no
later than its last (`corr_bar2_end`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites Reg ordK
  val valT)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem CorrRounds.bmax (hp : Pre p L m) (hg : g < L.threads) {R : Nat}
    (hR : CorrRounds p L g R) : R + 1 ≤ Progress.bmax p :=
  mma_rounds_bmax hp hg (hR.mma hp hg)

/-- The rescale rounds are the CTA's. -/
theorem CorrRounds.cta {y : Nat} (hp : Pre p L m) (hg : g < L.threads) (hy : y < L.threads)
    (hc : y / L.block = g / L.block) {R : Nat}
    (hR : CorrRounds p L g R) : CorrRounds p L y R := by
  obtain ⟨r, bal, hP, -⟩ := id hR
  have hR' : CorrRounds p L y _ := ⟨r, bal, Epilogue.Picked.cta hc.symm hP, rfl⟩
  have h1 := (hR.mma hp hg).cta hc.symm
  rwa [(hR'.mma hp hy).unique h1] at hR'

private theorem nb_pts : allSites.all (fun s => [(0 : Fin 2), 1].all fun st =>
    !(decide (Correction.sig s = some (.nb st))) ||
      (decide (0 < (ptsOf (.nb st)).countP (· = s.pc)) && s.isNb && !s.noTile &&
        decide (Correction.barK s = st))) = true := by decide +kernel

private theorem nb_pt {st : Fin 2} {s : Correction.Site} (hs : Correction.sig s = some (.nb st)) :
    0 < (ptsOf (.nb st)).countP (· = s.pc) ∧ s.isNb = true ∧ s.noTile = false ∧
      Correction.barK s = st := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp nb_pts s (mem_allSites s)) st (by
    fin_cases st <;> simp)
  simp only [hs, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h1
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
  exact ⟨h2, h3, h4, h5⟩

private def endChk (s : Correction.Site) : Bool :=
  (match Progress.Cr.endOff s with
    | some (l, o) => decide (Progress.Cr.late s = l) && decide (s.noTile = !l) &&
        decide (CorrWarp.epi s = .exit l) && (decide (s = .exit l) || decide (o ≤ 4)) &&
        (decide (s = .exit l) || decide (s = .barEnd l) || decide (o ≤ 2)) &&
        (Progress.Cr.part s).isNone && decide (8447 ≤ s.pc)
    | none => !s.noTile && decide ((CorrWarp.epi s).late = Progress.Cr.late s)) &&
  (!Progress.Cr.late s || decide (9089 ≤ s.pc)) &&
  (!(Progress.Cr.part s).isSome || s.hasUk) &&
  (!s.hasUk || decide (CorrWarp.epi s = .ready 0)) &&
  (!(Progress.Cr.part s).isNone || decide (s.pc < 8006) || decide (9089 ≤ s.pc))

private theorem end_chk : allSites.all endChk = true := by decide +kernel

/-- A state before the end is before every end, and before the prime region's end when its CTA
picked no tile. -/
theorem corr_early_time (hp : Pre p L m) {d : Correction.D} {n : Cls → Nat}
    (hF : CorrWarp.CFits p L g d (n .shfl) (n .vote)) (he : Progress.Cr.endOff d.site = none) :
    Progress.Cr.time p d n < Progress.doneBase p ∧
      ((Progress.Cr.part d.site).isNone = true → d.site.pc < 8006 →
        Progress.Cr.time p d n < Progress.primeBase p) ∧
      ((¬ ∃ R bal, Epilogue.Picked p L g R bal) → d.site.pc < 8006 →
        Progress.Cr.time p d n < Progress.endT p false 0) := by
  have hprv : Progress.primeBase p = Progress.scanBase + 2 * Progress.cmax p + 4 := rfl
  have hend : Progress.primeBase p + 1024 ≤ Progress.endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold Progress.endBase Progress.tailBase; omega
  have hdone : Progress.doneBase p = Progress.endBase p + 4 * Progress.cmax p + 8 := rfl
  have htl : Progress.tailBase p ≤ Progress.endBase p := Nat.le_add_right _ _
  have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
  have he0 : Progress.endT p false 0 = Progress.primeBase p + 1000 := by simp [Progress.endT]
  have hchk := List.all_eq_true.mp end_chk d.site (mem_allSites _)
  simp only [endChk, he, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨-, hl⟩, hlate⟩, hpk⟩, hepi⟩, -⟩ := hchk
  obtain ⟨rv, hrv, -, hFE, -⟩ := hF
  simp only [Progress.Cr.time, he]
  split
  · rename_i st past hpt
    have h1 := Progress.clk_lt_tail (p := p) (a := n (.corr (.nb st)) - if past then 1 else 0)
      (Progress.Cr.off_lt st d.site)
    refine ⟨by unfold Progress.Cr.slot; omega, fun h => by rw [hpt] at h; simp at h,
      fun hno _ => ?_⟩
    exfalso
    have huk : d.site.hasUk = true := hpk.resolve_left (by simp [hpt])
    have hep := hepi.resolve_left (by simp [huk])
    simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
    obtain ⟨R, bal, hC, -⟩ := hFE
    exact hno ⟨R, bal, hC.1⟩
  · have h7 : Progress.Out.ballots (Progress.Cr.toE d.site) ≤ 1 := by
      unfold Progress.Out.ballots; split <;> omega
    split_ifs with h1 h2 h3
    · exact ⟨by omega, fun _ _ => by omega, fun _ _ => by omega⟩
    · exact ⟨by omega, fun _ _ => by omega, fun _ _ => by omega⟩
    · have h6 := Epilogue.fits_coll_le_all hp hFE
      have h8 : ∀ b c co, Progress.passTime b c co ≤ b + 2 * c := fun b c co => by
        unfold Progress.passTime; split <;> omega
      have h9 := h8 (Progress.endBase p) (n .shfl + Progress.Out.ballots (Progress.Cr.toE d.site))
        (Progress.Out.coll (Progress.Cr.toE d.site))
      have hlp : d.site.pc < 8006 → False := fun h => by
        rcases hlate with h' | h'
        · rw [h3] at h'; cases h'
        · omega
      exact ⟨by omega, fun _ h => (hlp h).elim, fun _ h => (hlp h).elim⟩
    · have h6 := Epilogue.fits_coll_le hp hFE (hl.trans (by simpa using h3))
      have h8 := Progress.pass_lt_prime (p := p)
        (c := n .shfl + Progress.Out.ballots (Progress.Cr.toE d.site))
        (by unfold Progress.cmax; omega) (Progress.Out.coll (Progress.Cr.toE d.site))
      exact ⟨by omega, fun _ _ => by omega, fun _ _ => by omega⟩

/-- **The time of a state at a site of the rounds or the final stage.** -/
theorem corr_round_time {d : Correction.D} {n : Cls → Nat} {r : Nat}
    (hc : ∀ c, c ≠ .st → n (.corr c) = passed (ptsOf c) d.site r) {a : Nat × Nat}
    (ha : val d.site = some a) :
    Progress.Cr.time p d n ≤ valT p r a ∧
      (r + 1 ≤ Progress.bmax p → Progress.Cr.time p d n = valT p r a) := by
  obtain ⟨st, past, hpt, h1, h2, h3⟩ := Correction.slot_of ha r
  have hn := hc (.nb st) (by simp)
  have ht : Progress.Cr.time p d n = Progress.clk p (Progress.slotOf p (r + a.1)) a.2 := by
    simp only [Progress.Cr.time, hpt, Progress.Cr.slot, hn, h2, h1]
  have hm := Nat.mul_le_mul_left 4096
    (show Progress.slotOf p (r + a.1) ≤ r + a.1 from Nat.min_le_left _ _)
  rw [ht]
  refine ⟨?_, fun hb => ?_⟩
  · unfold Progress.clk valT Progress.span
    omega
  · rw [Progress.slotOf_eq (by omega)]
    unfold Progress.clk valT Progress.span
    omega

/-- A state of a tile before the final stage's end that is at no site of the rounds is in the first
scan or the prime region. -/
theorem corr_early_val (hp : Pre p L m) {d : Correction.D} {n : Cls → Nat}
    (hF : CorrWarp.CFits p L g d (n .shfl) (n .vote)) (hv : val d.site = none)
    (hpc : d.site.pc < 9089) : Progress.Cr.time p d n < Progress.primeBase p := by
  have hpn : (Progress.Cr.part d.site).isNone = true := by
    unfold val at hv
    split at hv
    · cases hv
    · rename_i h; rw [h]; rfl
  have hchk := List.all_eq_true.mp end_chk d.site (mem_allSites _)
  simp only [endChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hchk
  have hlt : d.site.pc < 8006 := by
    rcases hchk.2 with (h' | h') | h'
    · rw [hpn] at h'; cases h'
    · exact h'
    · omega
  have he : Progress.Cr.endOff d.site = none := by
    cases he : Progress.Cr.endOff d.site with
    | none => rfl
    | some lo =>
      obtain ⟨l, o⟩ := lo
      have h3 := hchk.1.1.1.1
      simp only [he, Bool.and_eq_true, decide_eq_true_eq] at h3
      omega
  exact (corr_early_time hp hF he).2.1 hpn hlt

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : 8 ≤ Prologue.warpIndex L g)
  (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hub hg hw hw1

omit hg in
private theorem ev_of {d : Correction.Control.D} {n : Cls → Nat} {e : Event}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (he : X.get (g, k) = some e) : Correction.Control.Ev p L g d e ∧ ∀ f, e.kind ≠ .ub f := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  refine ⟨?_, hne⟩
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hne with ⟨s, n', hσ', -⟩ |
    ⟨d', n', hσ', -, -, -, hev, -⟩
  · rw [hσ] at hσ'; cases hσ'
  · rw [hσ] at hσ'; cases hσ'; exact hev

omit hub hg in
private theorem exit_at {j pc : Nat} (hx : X.get (g, j) = some ⟨pc, .exit⟩) :
    ∃ d n l, Frame.stateAt (thread p L) X g j = some (some (CorrWarp.cinj p L g d n)) ∧
      d.scheduler.site = .exit l := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 hx (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, -, -, -, hev, -⟩
  · exfalso
    have hx : exit L g s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  · obtain ⟨l, hs⟩ := corr_exit_at (corr_ctl_ev hev (by simp))
    exact ⟨d, n, l, hσ, hs⟩

/-- **A lane with no more events on a named barrier than a place of its tile has passed** has not
exited and is no later than the place. -/
theorem corr_bar_lag {R : Nat} (hR : CorrRounds p L g R) {st : Fin 2} {s0 : Correction.Site}
    {r0 : Nat} {a : Nat × Nat} (hs : Correction.sig s0 = some (.nb st)) (ha : val s0 = some a)
    (hR0 : Reg R s0 r0)
    (hle : (X.tr g).countP (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) ≤
      passed (ptsOf (.nb st)) s0 r0) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ valT p r0 a := by
  obtain ⟨h0, hnb, hn0, hbk⟩ := nb_pt hs
  have hpb : Progress.primeBase p + 1024 ≤ valT p r0 a := by
    unfold valT Progress.pipeBase; omega
  have hsp := Progress.scanBase_le_primeBase p
  have hk : ∀ k, ((X.tr g).take k).countP
      (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) ≤
      passed (ptsOf (.nb st)) s0 r0 := fun k =>
    le_trans (List.take_sublist _ _).countP_le hle
  -- the place of a state
  have place : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      (Progress.time p L g σ < valT p r0 a) ∨ ∃ d n, σ = CorrWarp.cinj p L g d n ∧
        d.scheduler.site = s0 ∧ Progress.time p L g σ ≤ valT p r0 a ∧
        n (.corr (.nb st)) = passed (ptsOf (.nb st)) s0 r0 := by
    intro k σ hσ
    rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨h1, -⟩ |
      ⟨d, n, r, rfl, -, hc, hF, hreg, -⟩
    · left; omega
    obtain ⟨hr, ht⟩ := hreg R hR
    have h1 := hc (.nb st) (by simp)
    have h2 := hk k
    rw [corr_isBarId hw hw1, count hσ, h1] at h2
    show Progress.Cr.time p d.scheduler n < _ ∨ ∃ d' n', _ ∧ _ ∧ Progress.Cr.time p d.scheduler n ≤
        _ ∧ _
    rcases Nat.lt_trichotomy (ordK d.scheduler.site r) (ordK s0 r0) with h | h | h
    · left
      cases hv : val d.scheduler.site with
      | some b =>
        have := (corr_round_time (p := p) hc hv).1
        have := Correction.val_lt hv ha hnb hr hR0 h p
        omega
      | none =>
        have hs0 : s0.pc < 9089 := by
          have h1 : allSites.all (fun s => !s.isNb || decide (s.pc < 9089)) = true := by
            decide +kernel
          have := List.all_eq_true.mp h1 s0 (mem_allSites _)
          simpa [hnb] using this
        have := corr_early_val hp hF hv (by
          have := Correction.pc_le d.scheduler.site
          unfold ordK at h
          unfold Reg at hr hR0
          omega)
        omega
    · right
      obtain ⟨e1, rfl⟩ := Correction.ordK_eq hnb h
      have h3 := (corr_round_time (p := p) hc (a := a) (by rw [e1]; exact ha)).1
      exact ⟨d, n, rfl, e1, h3, by rw [← e1]; exact h1⟩
    · have := Correction.passed_lt hR0 hr hn0 ht h (ptsOf (.nb st))
      omega
  constructor
  · intro j pc hx
    obtain ⟨d, n, l, hσ, hs'⟩ := exit_at hp hX hFw hw hw1 hx
    rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨-, _, _, h⟩ |
      ⟨d', n', r, h, -, hc, -, hreg, -⟩
    · cases h
    cases h
    obtain ⟨hr, ht⟩ := hreg R hR
    have h1 := hc (.nb st) (by simp)
    have h2 := hk j
    rw [corr_isBarId hw hw1, count hσ, h1] at h2
    have hK : ordK s0 r0 < ordK d.scheduler.site r := by
      have hs0 : s0.pc < 9089 := by
        have h1 : allSites.all (fun s => !s.isNb || decide (s.pc < 9089)) = true := by
          decide +kernel
        have := List.all_eq_true.mp h1 s0 (mem_allSites _)
        simpa [hnb] using this
      have hpe : d.scheduler.site.pc = 9205 := by rw [hs']; rfl
      unfold ordK
      unfold Reg at hr hR0
      omega
    have := Correction.passed_lt hR0 hr hn0 ht hK (ptsOf (.nb st))
    omega
  · refine threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_
    · rcases place hσ with h | ⟨_, _, -, -, h, -⟩ <;> omega
    · rcases place hσ with h | ⟨d, n, rfl, hs', -, hn⟩
      · omega
      exfalso
      obtain ⟨hev, hne⟩ := ev_of hp hX hFw hub hw hw1 hσ he
      have hkd : e.kind = .bar (Correction.nbOf L g st).toNat (some 64) .sync := by
        have hnb' : ∀ q : Fin 2, (Correction.nbW L g q) = Correction.nbOf L g q := fun q => by
          fin_cases q <;> rfl
        rw [← hbk, ← hnb']
        obtain ⟨site, v, kk⟩ := d
        change site = s0 at hs'
        subst hs'
        cases site <;> simp only [Correction.Site.isNb, Bool.false_eq_true] at hnb <;> exact hev
      have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP
          (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) <
          (X.tr g).countP (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) :=
        Frame.countP_take_lt_countP (es := X.tr g) he (by
          simp [Execution.isBarId, hkd, corr_nbW hw hw1])
      rw [corr_isBarId hw hw1, count hσ, hn] at h2
      omega


/-! ### Barrier 2 -/

omit hp hX hFw hub hg hw hw1 in
private theorem bar2_tab : allSites.all (fun s =>
    (decide (s = .setmax) || decide (s = .bar1) ||
      decide (1 ≤ (ptsOf .bar2).countP (before s))) &&
    ((decide ((ptsOf .bar2).countP (before s) ≤ 1) ==
      !(decide (s = .exit true) || decide (s = .exit false))))) = true := by decide +kernel

omit hp hX hFw hub hg hw hw1 in
private theorem bar2_rnd : (ptsOf .bar2).countP Correction.inRound = 0 := by decide +kernel

omit hp hX hFw hub hg hw hw1 in
/-- The sites with barrier-2 counts. -/
private theorem bar2_site {d : Correction.Control.D} {n : Cls → Nat} {r : Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hc : n (.corr .bar2) = passed (ptsOf .bar2) d.scheduler.site r) :
    (((X.tr g).take k).countP (Execution.isBarId 2) = 0 → d.scheduler.site = .setmax ∨
        d.scheduler.site = .bar1) ∧
      (((X.tr g).take k).countP (Execution.isBarId 2) ≤ 1 → ∀ l, d.scheduler.site ≠ .exit l) := by
  have h1 := List.all_eq_true.mp bar2_tab d.scheduler.site (mem_allSites _)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  simp only [passed, bar2_rnd, Nat.mul_zero, Nat.add_zero] at hc
  have h2 : ((X.tr g).take k).countP (Execution.isBarId 2) = n (.corr .bar2) := by
    rw [← count hσ]; exact corr_isBar2
  rw [h2, hc]
  obtain ⟨h3, h4⟩ := h1
  refine ⟨fun h => ?_, fun h l hl => ?_⟩
  · rcases h3 with h3 | h3
    · exact h3
    · omega
  · rw [hl] at h4 h
    simp only [h, decide_true] at h4
    cases l <;> simp at h4

omit hub hg hw in
private theorem nexit (h : (X.tr g).countP (Execution.isBarId 2) ≤ 1) :
    ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩ := by
  intro j pc hx
  have := sc_exit_bar2 hp hX hFw hx (by omega)
  omega

/-- **A correction lane with no barrier-2 event** is no later than its first. -/
theorem corr_bar2_first (h : (X.tr g).countP (Execution.isBarId 2) = 0) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ Progress.scanBase + 3 := by
  have hk : ∀ k, ((X.tr g).take k).countP (Execution.isBarId 2) = 0 := fun k => by
    have := (List.take_sublist k (X.tr g)).countP_le (p := Execution.isBarId 2)
    omega
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ < Progress.scanBase + 3 ∨ ∃ d n, σ = CorrWarp.cinj p L g d n ∧
        d.scheduler.site = .bar1 ∧ Progress.time p L g σ = Progress.scanBase + 3 := by
    intro k σ hσ
    rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨h1, -⟩ | ⟨d, n, r, rfl, -, hc, -⟩
    · left; omega
    · rcases (bar2_site hσ (hc .bar2 (by simp))).1 (hk k) with hs | hs
      · left
        show Progress.Cr.time p d.scheduler n < _
        simp [Progress.Cr.time, hs, Progress.Cr.part, Progress.Cr.endOff]
      · right
        refine ⟨d, n, rfl, hs, ?_⟩
        show Progress.Cr.time p d.scheduler n = _
        simp [Progress.Cr.time, hs, Progress.Cr.part, Progress.Cr.endOff]
  refine ⟨nexit hp hX hFw hw1 (by omega), threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_⟩
  · rcases key hσ with h | ⟨_, _, -, -, h⟩ <;> omega
  · rcases key hσ with h | ⟨d, n, rfl, hs, h⟩
    · omega
    · exfalso
      obtain ⟨hev, -⟩ := ev_of hp hX hFw hub hw hw1 hσ he
      replace hev := corr_ctl_ev_site hev (fun st h => by
        rw [show d.site = _ from hs] at h; cases h)
      simp only [Correction.Ev, hs] at hev
      have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) <
          (X.tr g).countP (Execution.isBarId 2) :=
        Frame.countP_take_lt_countP (P := Execution.isBarId 2) (es := X.tr g) he
          (by simp [Execution.isBarId, hev])
      omega

/-- **A correction lane with at most one barrier-2 event** is no later than its last, the second
pass's exactly when its CTA picked a tile. -/
theorem corr_bar2_end {l : Bool} (hl : l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal)
    (h : (X.tr g).countP (Execution.isBarId 2) ≤ 1) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ Progress.endT p l 4 := by
  have hk : ∀ k, ((X.tr g).take k).countP (Execution.isBarId 2) ≤ 1 := fun k =>
    le_trans (List.take_sublist k (X.tr g)).countP_le h
  have hdone : Progress.doneBase p ≤ Progress.endT p true 0 := by simp [Progress.endT]
  have hT : ∀ a b, a < b → Progress.endT p l a < Progress.endT p l b := fun a b hab => by
    unfold Progress.endT; split <;> omega
  have h04 := hT 0 4 (by omega)
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ < Progress.endT p l 4 ∨ ∃ d n l', σ = CorrWarp.cinj p L g d n ∧
        d.scheduler.site = .barEnd l' ∧ Progress.time p L g σ = Progress.endT p l 4 ∧
        ((X.tr g).take k).countP (Execution.isBarId 2) = 1 := by
    intro k σ hσ
    rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨h1, -⟩ |
      ⟨d, n, r, rfl, -, hc, hF, hreg, hno⟩
    · left; have := Progress.endT_ge p l 4; omega
    show Progress.Cr.time p d.scheduler n < _ ∨ _
    have hchk := List.all_eq_true.mp end_chk d.scheduler.site (mem_allSites _)
    cases hend : Progress.Cr.endOff d.scheduler.site with
    | none =>
      left
      obtain ⟨t1, -, t2⟩ := corr_early_time hp hF hend
      cases l with
      | true => omega
      | false =>
        have hn : ¬ ∃ R bal, Epilogue.Picked p L g R bal := fun h => by
          have := hl.mpr h; cases this
        simp only [endChk, hend, Bool.and_eq_true, Bool.not_eq_true'] at hchk
        have h1 := (hno hn).resolve_right (by rw [hchk.1.1.1.1.1]; simp)
        have := t2 hn h1
        omega
    | some lo =>
      obtain ⟨l', o⟩ := lo
      simp only [endChk, hend, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hnt⟩, -⟩, -⟩, ho⟩, hpn⟩, hpc⟩, -⟩, -⟩, -⟩, -⟩ := hchk
      have hll : l' = l := by
        cases l with
        | true =>
          obtain ⟨R, bal, hP⟩ := hl.mp rfl
          have hR : CorrRounds p L g _ := ⟨R, bal, hP, rfl⟩
          have := (hreg _ hR).2
          rw [hnt] at this
          simpa using this
        | false =>
          cases l' with
          | false => rfl
          | true =>
            exfalso
            have hn : ¬ ∃ R bal, Epilogue.Picked p L g R bal := fun h => by
              have := hl.mpr h; cases this
            rcases hno hn with h1 | h1
            · omega
            · rw [hnt] at h1; cases h1
      subst hll
      have ht : Progress.Cr.time p d.scheduler n = Progress.endT p l' o := by
        simp only [Progress.Cr.time, Option.isNone_iff_eq_none.mp hpn, hend]
      have hb := bar2_site hσ (hc .bar2 (by simp))
      have hx := hb.2 (hk k)
      rcases ho with (ho | ho) | ho
      · exact absurd ho (hx l')
      · right
        refine ⟨d, n, l', rfl, ho, ?_, ?_⟩
        · show Progress.Cr.time p d.scheduler n = _
          rw [ht]
          rw [ho] at hend
          simp only [Progress.Cr.endOff, Option.some.injEq, Prod.mk.injEq] at hend
          rw [← hend.2]
        · have h2 := hk k
          by_contra h3
          rcases hb.1 (by omega) with h4 | h4 <;> rw [ho] at h4 <;> cases h4
      · left
        rw [ht]
        exact hT o 4 (by omega)
  refine ⟨nexit hp hX hFw hw1 h, threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_⟩
  · rcases key hσ with h | ⟨_, _, _, -, -, h, -⟩ <;> omega
  · rcases key hσ with h | ⟨d, n, l', rfl, hs, h', hc⟩
    · omega
    · exfalso
      obtain ⟨hev, hne⟩ := ev_of hp hX hFw hub hw hw1 hσ he
      replace hev := corr_ctl_ev_site hev (fun st h => by
        rw [show d.site = _ from hs] at h; cases h)
      simp only [Correction.Ev, hs] at hev
      rcases hev with hev | ⟨f, hev⟩
      · have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 2) <
            (X.tr g).countP (Execution.isBarId 2) :=
          Frame.countP_take_lt_countP (P := Execution.isBarId 2) (es := X.tr g) he
            (by simp [Execution.isBarId, hev])
        omega
      · exact hne f hev

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
