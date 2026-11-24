-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Stage
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Correction.Export.BarAt
import Kernels.TmlFa4Fwd.Proof.Lib.ThreadTime
import Kernels.TmlFa4Fwd.Proof.Mma.Export.BarLag
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BarAt
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Lemmas.Kernel.Safety.Schedule
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The named barriers in the time table

A barrier event of a lane is fired from the startup's barrier or from a barrier site of its role
(`bar_open`); it leads to a later state (`bar_after`). A lane of a participant warp with no more
events on the barrier than the lane before its event has not exited and is no later (`bar_lag`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g y j : Nat}

/-- The participant warps of a named barrier. -/
def barGroup (id w : Nat) : Prop :=
  if id = 0 then w < 16 else if id = 2 then w < 13
  else if 11 ≤ id then w / 4 = id - 11 ∧ w < 8
  else w + 3 = id ∨ w = 8 + (id - 3) % 4

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Every named barrier has its group.** -/
theorem bar_group {i pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (g, i) = some ⟨pc, .bar id cnt md⟩) :
    ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id ∧
      ∀ w ∈ q, barGroup id w := by
  rcases bar_cases hp hX hFw he with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨hid, rfl, -⟩ |
    ⟨st, k, hst, hk, rfl, rfl, -⟩
  · exact ⟨_, shape0 hp, srcs0 hp hX (table_shape_of hp hFw) (table_followed hp hX hFw),
      fun w hw => by simpa [barGroup] using hw⟩
  · exact ⟨_, shape2 hp, srcs2 hp hX (table_shape_of hp hFw) (table_followed hp hX hFw),
      fun w hw => by simpa [barGroup] using hw⟩
  · obtain ⟨st, hst, rfl⟩ : ∃ st < 2, id = stageId st := by
      rcases hid with rfl | rfl
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
    refine ⟨_, stage_shape hp hst, stage_sources hp hX hFw hst, fun w hw => ?_⟩
    have := mem_stageWarps.mp hw
    unfold barGroup stageId
    split_ifs <;> omega
  · refine ⟨_, stat_shape hp hst hk, stat_sources hp hX hFw hst hk, fun w hw => ?_⟩
    simp only [statPair, Finset.mem_insert, Finset.mem_singleton] at hw
    unfold barGroup statId
    split_ifs <;> omega

/-- A startup state's barrier event is the CTA's, at the barrier site. -/
theorem start_bar_open {pc id : Nat} {cnt : Option Nat} {md : BarMode} {s : Startup.D}
    {n : Cls → Nat} (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g j = some (some (.inl s, n)))
    (hg : g < L.threads) (hx : exit L g s = none)
    (hev : Startup.Ev L g s ⟨pc, .bar id cnt md⟩) : s.site = .bar ∧ id = 0 ∧
      ((X.tr g).take j).countP (Execution.isBarId id) = 0 := by
  have hs : s.site = .bar := by
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case bar => rfl
    case enter r => simp [exit] at hx
    case sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
    all_goals simp only [Startup.Ev] at hev
    all_goals first
      | (cases hev; done)
      | (rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk)
  refine ⟨hs, ?_, ?_⟩
  · simp only [Startup.Ev, hs, Kind.bar.injEq] at hev
    exact hev.1
  · have h1 : n (.mma .bar) = 0 := bar_count hp hX hFw hg j _
      (Frame.noUbBefore_of_get hX he) hσ
    rw [← count hσ, cls_bar] at h1
    refine Nat.eq_zero_of_le_zero (h1 ▸ List.countP_mono_left fun e _ h => ?_)
    obtain ⟨_, kd⟩ := e
    cases kd <;> simp_all [Execution.isBarId, Execution.isBar]

/-- **A barrier event** is fired from the startup's barrier or from a state of a softmax, correction
or MMA lane. -/
theorem bar_open {pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ)) :
    (∃ s n, σ = (.inl s, n) ∧ s.site = .bar ∧ id = 0 ∧
      ((X.tr g).take j).countP (Execution.isBarId id) = 0) ∨
    (∃ d n, σ = SmWarp.sinj p L g d n ∧ Prologue.warpIndex L g < 8) ∨
    (∃ d n, σ = CorrWarp.cinj p L g d n ∧ 8 ≤ Prologue.warpIndex L g ∧
      Prologue.warpIndex L g ≤ 11) ∨
    ∃ d n, σ = Mma.minj p L g d n ∧ Prologue.warpIndex L g = 12 := by
  have hg := Frame.lt_of_get hX he
  have h16 := Prologue.warpIndex_lt hp g
  rcases show Prologue.warpIndex L g < 8 ∨ (8 ≤ Prologue.warpIndex L g ∧
      Prologue.warpIndex L g ≤ 11) ∨ Prologue.warpIndex L g = 12 ∨
      13 ≤ Prologue.warpIndex L g by omega with hw | hw | hw | hw
  · rcases soft_fired hp hX hFw hw he (fun f h => by cases h) hσ with ⟨s, n, rfl, hx, hev⟩ |
      ⟨d, n, rfl⟩
    · exact .inl ⟨s, n, rfl, start_bar_open hp hX hFw he hσ hg hx hev⟩
    · exact .inr (.inl ⟨d, n, rfl, hw⟩)
  · rcases corr_fired hp hX hFw hw.1 hw.2 he (fun f h => by cases h) hσ with ⟨s, n, rfl, hx, hev⟩ |
      ⟨d, n, rfl⟩
    · exact .inl ⟨s, n, rfl, start_bar_open hp hX hFw he hσ hg hx hev⟩
    · exact .inr (.inr (.inl ⟨d, n, rfl, hw⟩))
  · rcases Mma.mma_bar_open hp hX hFw hw he hσ with ⟨s, n, rfl, hx, hev⟩ | ⟨d, n, rfl⟩
    · exact .inl ⟨s, n, rfl, start_bar_open hp hX hFw he hσ hg hx hev⟩
    · exact .inr (.inr (.inr ⟨d, n, rfl, hw⟩))
  obtain ⟨σ', n, hσ', -, -, hi, hev⟩ := ev_open hp hX hFw he (fun f h => by cases h)
  rw [hσ] at hσ'
  cases hσ'
  rcases σ' with s | ⟨i, d⟩
  · exact .inl ⟨s, n, rfl, start_bar_open hp hX hFw he hσ hg hi.2 hev⟩
  exfalso
  -- the output and loader warps make the CTA's barrier event alone
  have hs := bar_sched hp hX hFw hg he
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  by_cases h0 : ((X.tr g).take j).countP Execution.isBar = 0
  · have h1 := role_bar0 hp hX j hσ
    have h2 : ((X.tr g).take j).countP (Execution.isBarId 0) ≤
        ((X.tr g).take j).countP Execution.isBar := List.countP_mono_left fun e _ h => by
      obtain ⟨_, kd⟩ := e
      cases kd <;> simp_all [Execution.isBarId, Execution.isBar]
    omega
  · have h8 : ¬ Prologue.warpIndex L g < 8 := by omega
    have h12 : Prologue.warpIndex L g = 12 ∨ Prologue.warpIndex L g = 13 ∨
        Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15 := by omega
    simp only [schedB, h8, h12, h0, ite_true, ite_false, Prod.mk.injEq] at hs
    obtain ⟨rfl, -, -⟩ := hs
    have h3 := (srcs2 hp hX hT hF (g, j) pc cnt ⟨md, he⟩ hg).1
    simp only [Finset.mem_range, Prologue.warpIndex] at h3 hw
    omega

/-- **A barrier event leads to a later state.** -/
theorem bar_after (hub : ¬ HasUb X) {pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ)) :
    ∃ σ', Frame.stateAt (thread p L) X g (j + 1) = some (some σ') ∧
      Progress.time p L g σ < Progress.time p L g σ' := by
  rcases bar_open hp hX hFw he hσ with ⟨s, n, rfl, hs, -, -⟩ | ⟨d, n, rfl, hw⟩ |
    ⟨d, n, rfl, hw, hw1⟩ | ⟨d, n, rfl, hw⟩
  · have hen : ∃ r, exit L g (Startup.enterOf s) = some r := by
      unfold Startup.enterOf
      split_ifs <;> simp only [exit] <;> split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := hen
    refine ⟨(.inr ⟨r, (frag p L g r).init⟩, Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩), ?_, ?_⟩
    · rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[j]? = _ from he), hσ]
      obtain ⟨site, x1, x2, x3⟩ := s
      simp only at hs
      subst hs
      have h1 : (thread p L g).next (.inl ⟨.bar, x1, x2, x3⟩, n) ⟨pc, .bar id cnt md⟩ =
          some (some (.inr ⟨r, (frag p L g r).init⟩,
            Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)) := by
        simp [thread, glued, Code.counted, Code.glue, Startup.code, Startup.succ, Code.enter, hr]
      exact h1
    · have h1 : Progress.time p L g (.inl s, n) = 173 := by
        show s.site.pc = 173
        rw [hs]; rfl
      have h2 : Progress.scanBase = 256 := rfl
      have h3 := Progress.roleTime_ge (p := p) (L := L) (g := g) r (frag p L g r).init
        (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
      rw [h1]
      show 173 < Progress.roleTime p L g r _ _
      omega
  · exact soft_bar_next hp hX hFw hub hw he hσ
  · exact corr_bar_next hp hX hFw hub hw hw1 he hσ
  · exact Mma.mma_bar_next hp hX hFw hub hw he hσ

/-! ### The lanes short of a barrier event -/

omit hp hX hFw in
private theorem nbsb_pts : ∀ b : Bool, Softmax.ptsOf b .nb = Softmax.ptsOf true .nb ∧
    Softmax.ptsOf b .sb = Softmax.ptsOf true .sb := by decide +kernel

/-- **A lane with no barrier-2 event** is no later than its first. -/
theorem bar2_first (hub : ¬ HasUb X) (hy : y < L.threads) (hw : Prologue.warpIndex L y < 13)
    (h : (X.tr y).countP (Execution.isBarId 2) = 0) :
    (∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X y ≤ Progress.scanBase + 3 := by
  rcases show Prologue.warpIndex L y < 8 ∨ (8 ≤ Prologue.warpIndex L y ∧
      Prologue.warpIndex L y ≤ 11) ∨ Prologue.warpIndex L y = 12 by omega with h1 | h1 | h1
  · exact soft_bar2_first hp hX hFw hub hy h1 h
  · exact corr_bar2_first hp hX hFw hub hy h1.1 h1.2 h
  · exact Mma.mma_bar2_first hp hX hFw hub hy h1 h

/-- **A lane with at most one barrier-2 event** is no later than its last. -/
theorem bar2_end (hub : ¬ HasUb X) (hy : y < L.threads) (hw : Prologue.warpIndex L y < 13) {l :
    Bool}
    (hl : l = true ↔ ∃ R bal, Epilogue.Picked p L y R bal)
    (h : (X.tr y).countP (Execution.isBarId 2) ≤ 1) :
    (∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X y ≤ Progress.endT p l 4 := by
  rcases show Prologue.warpIndex L y < 8 ∨ (8 ≤ Prologue.warpIndex L y ∧
      Prologue.warpIndex L y ≤ 11) ∨ Prologue.warpIndex L y = 12 by omega with h1 | h1 | h1
  · exact soft_bar2_end hp hX hFw hub hy h1 hl h
  · exact corr_bar2_end hp hX hFw hub hy h1.1 h1.2 hl h
  · exact Mma.mma_bar2_end hp hX hFw hub hy h1 hl h

omit hp hX hFw in
private theorem start_pc {s : Startup.D} (hx : ∀ r, s.site ≠ .enter r) :
    s.site.pc ≤ 173 ∧ (s.site ≠ .bar → s.site.pc < 173) := by
  have h1 : ∀ j, (Startup.Site.sh j).pc < 173 := by decide
  have h2 : ∀ j, (Startup.Site.elect j).pc < 173 := by decide
  have h3 : ∀ j, (Startup.Site.init j).pc < 173 := by decide
  cases hs : s.site with
  | sh j => exact ⟨(h1 j).le, fun _ => h1 j⟩
  | elect j => exact ⟨(h2 j).le, fun _ => h2 j⟩
  | init n => exact ⟨(h3 n).le, fun _ => h3 n⟩
  | fence => exact ⟨by decide, fun _ => by decide⟩
  | bar => exact ⟨le_rfl, fun h => absurd rfl h⟩
  | enter r => exact absurd hs (hx r)

/-- **A lane with no CTA-barrier event** is no later than the startup's barrier. -/
theorem bar0_lag (hub : ¬ HasUb X) (hy : y < L.threads)
    (h : (X.tr y).countP (Execution.isBarId 0) = 0) :
    (∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X y ≤ 173 := by
  have hk : ∀ k, ((X.tr y).take k).countP (Execution.isBarId 0) = 0 := fun k => by
    have := (List.take_sublist k (X.tr y)).countP_le (p := Execution.isBarId 0)
    omega
  have key : ∀ {k σ}, Frame.stateAt (thread p L) X y k = some (some σ) →
      Progress.time p L y σ ≤ 173 ∧ (Progress.time p L y σ < 173 ∨
        ∃ s n, σ = (.inl s, n) ∧ s.site = .bar) := by
    intro k σ hσ
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨r, d⟩
    · obtain ⟨h1, h2⟩ := start_pc (s := s) (jr_start_site ((goodR hp hX hFw hy k).2 _ hσ))
      refine ⟨h1, ?_⟩
      by_cases hs : s.site = .bar
      · exact .inr ⟨s, n, rfl, hs⟩
      · exact .inl (h2 hs)
    · have := role_bar0 hp hX k hσ
      rw [hk k] at this
      omega
  constructor
  · intro j pc hx
    have := exit_bar0 hp hX (table_shape_of hp hFw) (table_followed hp hX hFw) hx
    rw [hk j] at this
    omega
  · refine threadTime_le (fun σ hσ => (key hσ).1) fun σ e hσ he => ?_
    rcases (key hσ).2 with h1 | ⟨s, n, rfl, hs⟩
    · exact h1
    · exfalso
      obtain ⟨σ', n', hσ', -, hJ, hi, hev⟩ := ev_open hp hX hFw he (fun f hf =>
        hub ⟨(y, _), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩)
      rw [hσ] at hσ'
      cases hσ'
      have hev' : Startup.Ev L y s e := hev
      simp only [Startup.Ev, hs] at hev'
      have h2 : ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId 0) <
          (X.tr y).countP (Execution.isBarId 0) :=
        Frame.countP_take_lt_countP (P := Execution.isBarId 0) (es := X.tr y) he
          (by simp [Execution.isBarId, hev'])
      omega

omit hp hX hFw in
/-- The places of the softmax lanes' arrivals on the named barrier of a correction lane's wait. -/
private theorem soft_place_of {st : Fin 2} {s : Correction.Site} {R r : Nat} {a : Nat × Nat}
    (hnb : s.isNb = true) (hs : Correction.sig s = some (.nb st)) (ha : Correction.val s = some a)
    (hr : Correction.Reg R s r) {B P : Nat} (hBP : B + P = R) (p : Params) :
    ∃ s0 rb rp b, Softmax.sig s0 = some .nb ∧ Softmax.val st.val s0 = some b ∧
      Softmax.Reg B P s0 rb rp ∧ s0.noTile = false ∧ s0.pos ≤ 15232 ∧
      (∀ z, Correction.passed (Correction.ptsOf (.nb st)) s r =
        Softmax.passed (Softmax.ptsOf z .nb) s0 rb rp) ∧
      Softmax.valT p (rb + rp) b ≤ Correction.valT p r a := by
  have t : ∀ st : Fin 2, Correction.val (.nb st) = some (0, Progress.bandC st.val) ∧
      Correction.val (.rbar st) = some (1, Progress.bandC st.val) ∧
      Correction.val (.fbar st) = some (1, Progress.bandC st.val + 102) ∧
      (Correction.ptsOf (.nb st)).countP (Correction.before (.nb st)) = 0 ∧
      (Correction.ptsOf (.nb st)).countP (Correction.before (.rbar st)) = 1 ∧
      (Correction.ptsOf (.nb st)).countP (Correction.before (.fbar st)) = 1 ∧
      (Correction.ptsOf (.nb st)).countP Correction.inRound = 1 ∧
      8006 ≤ (Correction.Site.rbar st).pc ∧ (Correction.Site.rbar st).pc ≤ 8446 ∧
      8447 ≤ (Correction.Site.fbar st).pc ∧ (Correction.Site.nb st).pc < 8006 := by decide +kernel
  have u : ∀ z : Bool, (Softmax.ptsOf z .nb).countP (Softmax.before (.narr .first)) = 0 ∧
      (Softmax.ptsOf z .nb).countP (Softmax.before (.narr .bias)) = 1 ∧
      (Softmax.ptsOf z .nb).countP (Softmax.before (.narr .plain)) = 1 ∧
      (Softmax.ptsOf z .nb).countP (Softmax.before .finarr) = 1 ∧
      (Softmax.ptsOf z .nb).countP Softmax.inBias = 1 ∧
      (Softmax.ptsOf z .nb).countP Softmax.inPlain = 1 := by decide +kernel
  have w : ∀ st : Fin 2, Softmax.val st.val (.narr .first) = some (0, Progress.bandS st.val + 42) ∧
      Softmax.val st.val (.narr .bias) = some (1, Progress.bandS st.val + 42) ∧
      Softmax.val st.val (.narr .plain) = some (1, Progress.bandS st.val + 42) := by decide +kernel
  have w0 : Softmax.val 0 .finarr = some (0, Progress.bandP 0 + 30) ∧
      Softmax.val 1 .finarr = some (1, Progress.bandS 1 + 104) := by decide +kernel
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := t st
  obtain ⟨w1, w2, w3⟩ := w st
  have hst := st.isLt
  cases s <;> simp only [Correction.Site.isNb, Bool.false_eq_true] at hnb
  case nb q =>
    obtain rfl : q = st := by simpa [Correction.sig] using hs
    obtain rfl := Option.some.inj (ha.symm.trans t1)
    have hr0 : r = 0 := by unfold Correction.Reg at hr; omega
    subst hr0
    refine ⟨.narr .first, 0, 0, _, rfl, w1, .inl ⟨by decide, rfl, rfl⟩, rfl, by decide,
      fun z => ?_, ?_⟩
    · simp [Correction.passed, Softmax.passed, t4, (u z).1]
    · simp only [Softmax.valT, Correction.valT, Progress.bandS, Progress.bandC]; omega
  case rbar q =>
    obtain rfl : q = st := by simpa [Correction.sig] using hs
    obtain rfl := Option.some.inj (ha.symm.trans t2)
    have hrR : r < R := by unfold Correction.Reg at hr; omega
    rcases Nat.lt_or_ge r B with hB | hB
    · refine ⟨.narr .bias, r, 0, _, rfl, w2, .inr (.inl ⟨by decide, hB, rfl⟩), rfl, by decide,
        fun z => ?_, ?_⟩
      · obtain ⟨-, u2, -, -, u5, u6⟩ := u z
        simp [Correction.passed, Softmax.passed, t5, t7, u2, u5, u6]
      · simp only [Softmax.valT, Correction.valT, Progress.bandS, Progress.bandC]; omega
    · refine ⟨.narr .plain, B, r - B, _, rfl, w3, .inr (.inr (.inl ⟨by decide, rfl, by omega⟩)),
        rfl, by decide, fun z => ?_, ?_⟩
      · obtain ⟨-, -, u3, -, u5, u6⟩ := u z
        simp only [Correction.passed, Softmax.passed, t5, t7, u3, u5, u6]
        omega
      · simp only [Softmax.valT, Correction.valT, Progress.bandS, Progress.bandC]; omega
  case fbar q =>
    obtain rfl : q = st := by simpa [Correction.sig] using hs
    obtain rfl := Option.some.inj (ha.symm.trans t3)
    have hrR : r = R := by unfold Correction.Reg at hr; omega
    have hp' : ∀ z, Correction.passed (Correction.ptsOf (.nb q)) (.fbar q) r =
        Softmax.passed (Softmax.ptsOf z .nb) .finarr B P := fun z => by
      obtain ⟨-, -, -, u4, u5, u6⟩ := u z
      simp only [Correction.passed, Softmax.passed, t6, t7, u4, u5, u6]
      omega
    have hR' : Softmax.Reg B P .finarr B P := .inr (.inr (.inr ⟨by decide, rfl, rfl, rfl⟩))
    obtain rfl | rfl : q = 0 ∨ q = 1 := by fin_cases q <;> simp
    · refine ⟨.finarr, B, P, _, rfl, w0.1, hR', rfl, by decide, hp', ?_⟩
      simp only [Softmax.valT, Correction.valT, Progress.bandP, Progress.bandC]
      omega
    · refine ⟨.finarr, B, P, _, rfl, w0.2, hR', rfl, by decide, hp', ?_⟩
      simp only [Softmax.valT, Correction.valT, Progress.bandS, Progress.bandC]
      omega

/-- **A participant lane short of a barrier event** has not exited and is no later than the lane
before the event: for a `bar.sync` every lane of the barrier's group, else the lanes of the warp. -/
theorem bar_lag (hub : ¬ HasUb X) {pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ)) (hy : y < L.threads)
    (hc : y / L.block = g / L.block)
    (hG : (md = .sync ∧ barGroup id (Prologue.warpIndex L y)) ∨
      Prologue.warpIndex L y = Prologue.warpIndex L g)
    (hle : (X.tr y).countP (Execution.isBarId id) ≤
      ((X.tr g).take j).countP (Execution.isBarId id)) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X y ≤ Progress.time p L g σ := by
  have hg := Frame.lt_of_get hX he
  have hpk : ∀ {l : Bool}, (l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal) →
      (l = true ↔ ∃ R bal, Epilogue.Picked p L y R bal) := fun h =>
    h.trans ⟨fun ⟨R, bal, hP⟩ => ⟨R, bal, Epilogue.Picked.cta hc.symm hP⟩,
      fun ⟨R, bal, hP⟩ => ⟨R, bal, Epilogue.Picked.cta hc hP⟩⟩
  have hG2 : id = 2 → Prologue.warpIndex L g < 13 → Prologue.warpIndex L y < 13 := by
    rintro rfl h
    rcases hG with ⟨-, h1⟩ | h1
    · simpa [barGroup] using h1
    · omega
  rcases bar_open hp hX hFw he hσ with ⟨s, n, rfl, hs, rfl, h0⟩ | ⟨d, n, rfl, hw⟩ |
    ⟨d, n, rfl, hw, hw1⟩ | ⟨d, n, rfl, hw⟩
  · have h1 : Progress.time p L g (.inl s, n) = 173 := by
      show s.site.pc = 173
      rw [hs]; rfl
    rw [h1]
    exact bar0_lag hp hX hFw hub hy (by omega)
  · show _ ∧ _ ≤ Progress.Sm.time p L g d n
    rcases soft_bar_at hp hX hFw hub hw he hσ with ⟨rfl, -, -, h0, ht⟩ |
      ⟨l, rfl, -, -, h0, hl, ht⟩ |
      ⟨c, B, P, rb, rp, a, hcc, rfl, hm1, hm2, hT, hsig, ha, hr, hnt, hpos, ht, hcn⟩
    · rw [ht]
      exact bar2_first hp hX hFw hub hy (hG2 rfl (by omega)) (by omega)
    · rw [ht]
      exact bar2_end hp hX hFw hub hy (hG2 rfl (by omega)) (hpk hl) (by omega)
    · have hsame : Prologue.warpIndex L y < 8 ∧
          Prologue.warpIndex L y / 4 = Prologue.warpIndex L g / 4 ∧
          softBarId L y c = softBarId L g c := by
        rcases hG with ⟨hm, hG⟩ | hG
        · rcases hcc with rfl | rfl
          · have := hm2 rfl; rw [hm] at this; cases this
          · have e : ∀ z, softBarId L z .sb = 11 + Prologue.warpIndex L z / 4 := fun z => rfl
            unfold barGroup at hG
            rw [e g] at hG
            rw [e y, e g]
            split_ifs at hG <;> omega
        · refine ⟨by omega, by rw [hG], ?_⟩
          rcases hcc with rfl | rfl <;> simp only [softBarId, hG]
      obtain ⟨hwy, hs4, hid⟩ := hsame
      have hst : Progress.Sm.stage L y = Progress.Sm.stage L g := by
        unfold Progress.Sm.stage
        split_ifs <;> omega
      have hpts : Softmax.ptsOf (Softmax.lz L y) c = Softmax.ptsOf (Softmax.lz L g) c := by
        rcases hcc with rfl | rfl
        · rw [(nbsb_pts (Softmax.lz L y)).1, (nbsb_pts (Softmax.lz L g)).1]
        · rw [(nbsb_pts (Softmax.lz L y)).2, (nbsb_pts (Softmax.lz L g)).2]
      rw [ht]
      refine soft_bar_lag hp hX hFw hub hy hwy
        (SoftTile.cta hc hw hwy hs4 hT)
        (by rcases hcc with h | h <;> simp [h]) hsig (by rw [hst]; exact ha) hr hnt hpos ?_
      rw [hid, hpts, ← hcn]
      exact hle
  · show _ ∧ _ ≤ Progress.Cr.time p d n
    rcases corr_bar_at hp hX hFw hub hw hw1 he hσ with ⟨rfl, -, -, h0, ht⟩ |
      ⟨l, rfl, -, -, h0, hl, ht⟩ | ⟨st, R, r, a, rfl, -, hR, hnb, hsig, ha, hr, ht, -, hcn⟩
    · rw [ht]
      exact bar2_first hp hX hFw hub hy (hG2 rfl (by omega)) (by omega)
    · rw [ht]
      exact bar2_end hp hX hFw hub hy (hG2 rfl (by omega)) (hpk hl) (by omega)
    · rw [ht]
      have hst := st.isLt
      rcases show Prologue.warpIndex L y = Prologue.warpIndex L g ∨
          (Prologue.warpIndex L y < 8 ∧ Prologue.warpIndex L y + 3 =
            Prologue.warpIndex L g - 5 + 4 * st.val) by
        rcases hG with ⟨-, hG⟩ | hG
        · unfold barGroup at hG
          split_ifs at hG <;> omega
        · exact .inl hG with hwy | ⟨hwy, hid⟩
      · refine corr_bar_lag hp hX hFw hub hy (by omega) (by omega)
          (hR.cta hp hg hy hc) hsig ha hr ?_
        rw [hwy, ← hcn]
        exact hle
      · obtain ⟨R0, bal, hP, -⟩ := id hR
        obtain ⟨B, P, hT⟩ := exists_softTile (p := p) (L := L) (g := y)
          ⟨R0, bal, Epilogue.Picked.cta hc.symm hP⟩
        have hBP := hT.rounds.corr hp hg hc hR
        obtain ⟨s0, rb, rp, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
          soft_place_of hnb hsig ha hr (show B + P = R by omega) p
        have hsy : Progress.Sm.stage L y = st.val := by
          unfold Progress.Sm.stage
          split_ifs <;> omega
        have h8 := soft_bar_lag hp hX hFw hub hy hwy hT (.inl rfl) h1 (by rw [hsy]; exact h2) h3 h4
          h5 (by
            show (X.tr y).countP (Execution.isBarId (Prologue.warpIndex L y + 3)) ≤ _
            rw [hid, ← h6, ← hcn]
            exact hle)
        exact ⟨h8.1, h8.2.trans h7⟩
  · show _ ∧ _ ≤ Progress.Mm.time p d n
    rcases Mma.mma_bar_at hp hX hFw hub hw he hσ with ⟨rfl, -, h0, ht⟩ | ⟨l, rfl, -, h0, hl, ht⟩
    · rw [ht]
      exact bar2_first hp hX hFw hub hy (hG2 rfl (by omega)) (by omega)
    · rw [ht]
      exact bar2_end hp hX hFw hub hy (hG2 rfl (by omega)) (hpk hl) (by omega)

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
