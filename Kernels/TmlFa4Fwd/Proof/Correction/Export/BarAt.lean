-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.BarLag
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane's barrier events in the time table

`corr_bar_at`: a barrier event of a correction lane at a role state is its first or last on barrier
2, or on a named barrier at a place of its tile, whose time is the state's; `corr_bar_next`: it
leads
to a later state. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites Reg ordK
  val valT)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem bar2_tab : (ptsOf .bar2).countP (before .bar1) = 0 ∧
    (∀ l, (ptsOf .bar2).countP (before (.barEnd l)) = 1) ∧
    (ptsOf .bar2).countP Correction.inRound = 0 := by decide +kernel

private theorem nb_chk : allSites.all (fun s => !s.isNb || ((val s).isSome && s.hasUk &&
    !s.noTile && decide (Correction.sig s = some (.nb (Correction.barK s))) &&
    decide (CorrWarp.epi s = .ready 0))) = true := by decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hub hw hw1

/-- **A barrier event of a correction lane at a role state.** -/
theorem corr_bar_at {pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : Correction.Control.D}
    {n : Cls → Nat} (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) :
    (id = 2 ∧ md = .sync ∧ d.scheduler.site = .bar1 ∧
        ((X.tr g).take k).countP (Execution.isBarId id) = 0 ∧
        Progress.Cr.time p d.scheduler n = Progress.scanBase + 3) ∨
    (∃ l, id = 2 ∧ md = .arrive ∧ d.scheduler.site = .barEnd l ∧
        ((X.tr g).take k).countP (Execution.isBarId id) = 1 ∧
        (l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal) ∧
        Progress.Cr.time p d.scheduler n = Progress.endT p l 4) ∨
    ∃ (st : Fin 2) (R r : Nat) (a : Nat × Nat),
      id = Prologue.warpIndex L g - 5 + 4 * st.val ∧ md = .sync ∧ CorrRounds p L g R ∧
      d.scheduler.site.isNb = true ∧ Correction.sig d.scheduler.site = some (.nb st) ∧ val
          d.scheduler.site = some a ∧
      Reg R d.scheduler.site r ∧ Progress.Cr.time p d.scheduler n = valT p r a ∧ n (.corr (.nb 0)) =
        passed (ptsOf (.nb 0)) d.scheduler.site r ∧
      ((X.tr g).take k).countP (Execution.isBarId id) = passed (ptsOf (.nb st)) d.scheduler.site r
          := by
  have hg := Frame.lt_of_get hX he
  have hev : Correction.Ev p L g d.scheduler ⟨pc, .bar id cnt md⟩ := by
    rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with ⟨s, n', hσ', -⟩ |
      ⟨d', n', hσ', -, -, -, hev, -⟩
    · rw [hσ] at hσ'; cases hσ'
    · rw [hσ] at hσ'; cases hσ'; exact corr_ctl_ev hev (by simp)
  rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨-, s, n', h1⟩ |
    ⟨d', n', r, h1, -, hc, hF, hreg, hno⟩
  · cases h1
  cases h1
  -- a named barrier's place
  have named : d.scheduler.site.isNb = true → (⟨id, cnt, md⟩ : Nat × Option Nat × BarMode) =
        ⟨(Correction.nbW L g (Correction.barK d.scheduler.site)).toNat, some 64, .sync⟩ →
      ∃ (st : Fin 2) (R r : Nat) (a : Nat × Nat),
      id = Prologue.warpIndex L g - 5 + 4 * st.val ∧ md = .sync ∧ CorrRounds p L g R ∧
      d.scheduler.site.isNb = true ∧ Correction.sig d.scheduler.site = some (.nb st) ∧ val
          d.scheduler.site = some a ∧
      Reg R d.scheduler.site r ∧ Progress.Cr.time p d.scheduler n = valT p r a ∧ n (.corr (.nb 0)) =
        passed (ptsOf (.nb 0)) d.scheduler.site r ∧
      ((X.tr g).take k).countP (Execution.isBarId id) = passed (ptsOf (.nb st)) d.scheduler.site r
          := by
    intro hnb hk
    simp only [Prod.mk.injEq] at hk
    obtain ⟨hid, -, hmd⟩ := hk
    have h1 := List.all_eq_true.mp nb_chk d.scheduler.site (mem_allSites _)
    simp only [hnb, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h1
    obtain ⟨⟨⟨⟨h2, huk⟩, -⟩, hsig⟩, hep⟩ := h1
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h2
    have hpk : ∃ R bal, Epilogue.Picked p L g R bal := by
      obtain ⟨rv, -, -, hFE, -⟩ := hF
      simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
      obtain ⟨R, bal, hC, -⟩ := hFE
      exact ⟨R, bal, hC.1⟩
    obtain ⟨R, bal, hP⟩ := hpk
    have hR : CorrRounds p L g _ := ⟨R, bal, hP, rfl⟩
    obtain ⟨hr, ht⟩ := hreg _ hR
    have hrb := hR.bmax hp hg
    have hid' : id = Prologue.warpIndex L g - 5 + 4 * (Correction.barK d.scheduler.site).val := by
      rw [hid, ← corr_nbW hw hw1]
      generalize Correction.barK d.scheduler.site = q
      fin_cases q <;> rfl
    refine ⟨_, _, r, a, hid', hmd, hR, hnb, hsig, ha, hr, (corr_round_time hc ha).2 ?_,
      hc (.nb 0) (by simp), ?_⟩
    · generalize (Correction.Bs p L g (corrRef p L g R bal)).toNat - 1 = R' at hr hrb
      unfold Reg at hr
      omega
    · rw [hid', corr_isBarId hw hw1, count hσ]
      exact hc _ (by simp)
  have hcount2 : id = 2 → ((X.tr g).take k).countP (Execution.isBarId id) =
      (ptsOf .bar2).countP (before d.scheduler.site) := by
    rintro rfl
    have h1 := hc .bar2 (by simp)
    simp only [passed, bar2_tab.2.2, Nat.mul_zero, Nat.add_zero] at h1
    rw [← h1, ← count hσ]
    exact corr_isBar2
  obtain ⟨s, v, kk⟩ := d
  cases s
  all_goals try simp only [Correction.Control.D.scheduler] at hev
  case bar1 =>
    simp only [Correction.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    left
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · rw [hcount2 rfl]; exact bar2_tab.1
    · simp [Correction.Control.D.scheduler, Progress.Cr.time, Progress.Cr.part, Progress.Cr.endOff]
  case barEnd l =>
    simp only [Correction.Ev, Kind.bar.injEq, reduceCtorEq, exists_false, or_false] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    right; left
    refine ⟨l, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hcount2 rfl]; exact bar2_tab.2.1 l
    · cases l with
      | true =>
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        by_contra hn
        rcases hno hn with h | h
        · exact absurd h (by simp [Correction.Control.D.scheduler, Correction.Site.pc])
        · cases h
      | false =>
        refine ⟨fun h => (by cases h), fun h => ?_⟩
        obtain ⟨R, bal, hP⟩ := h
        have hR : CorrRounds p L g _ := ⟨R, bal, hP, rfl⟩
        have := (hreg _ hR).2
        cases this
    · simp [Correction.Control.D.scheduler, Progress.Cr.time, Progress.Cr.part, Progress.Cr.endOff]
  case nb | rbar | fbar =>
    simp only [Correction.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    exact .inr (.inr (named rfl rfl))
  all_goals exfalso
  all_goals simp only [Correction.Ev, Correction.rdOrUb, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals cases ‹Kind.bar _ _ _ = _›

omit hp hX hFw hub hw hw1 in
private theorem erase_time (d : Correction.D) (n : Cls → Nat) :
    Progress.time p L g (CorrWarp.cinj p L g (Correction.Control.erase d) n) =
      Progress.Cr.time p d n := rfl

omit hub in
/-- **An event of a correction lane** is fired from the startup or from a role state. -/
theorem corr_fired {e : Event} (he : X.get (g, k) = some e) (hne : ∀ f, e.kind ≠ .ub f)
    {σ : (thread p L g).D} (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    (∃ s n, σ = (.inl s, n) ∧ exit L g s = none ∧ Startup.Ev L g s e) ∨
      ∃ d n, σ = CorrWarp.cinj p L g d n := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hne with ⟨s, n, hσ', -, -, hi, hev⟩ | ⟨d, n, hσ', -⟩
  · rw [hσ] at hσ'; cases hσ'; exact .inl ⟨s, n, rfl, hi.2, hev⟩
  · rw [hσ] at hσ'; cases hσ'; exact .inr ⟨d, n, rfl⟩

/-- **A barrier event of a correction lane leads to a later state.** -/
theorem corr_bar_next {pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : Correction.Control.D}
    {n : Cls → Nat} (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n))) :
    ∃ σ', Frame.stateAt (thread p L) X g (k + 1) = some (some σ') ∧
      Progress.Cr.time p d.scheduler n < Progress.time p L g σ' := by
  have hctl : Correction.Control.succ p L g d ⟨pc, .bar id cnt md⟩ =
      (Correction.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩).map
        (Option.map Correction.Control.erase) := by
    have hcl : d.site = .bar1 ∨ (∃ l, d.site = .barEnd l) ∨ d.site.isNb = true := by
      rcases corr_bar_at hp hX hFw hub hw hw1 he hσ with ⟨-, -, hs, -⟩ | ⟨l, -, -, hs, -⟩ |
        ⟨_, _, _, _, -, -, -, hnb, -⟩
      · exact .inl hs
      · exact .inr (.inl ⟨l, hs⟩)
      · exact .inr (.inr hnb)
    obtain ⟨s, v, kk⟩ := d
    cases s <;> first
      | rfl
      | (exfalso; simp [Correction.Site.isNb] at hcl)
  have hstep : ∀ d', Correction.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩ = some (some d') →
      Frame.stateAt (thread p L) X g (k + 1) = some (some (CorrWarp.cinj p L g
        (Correction.Control.erase d')
        (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩))) := fun d' h => by
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = _ from he), hσ]
    refine (CorrWarp.next_cinj d n _).trans ?_
    rw [hctl, h]
    rfl
  have hshfl : d.scheduler.site = .bar1 → n .shfl = 3 := fun hs => by
    rcases corr_place hp hX hFw hub (Frame.lt_of_get hX he) hw hw1 hσ with ⟨-, s, n', h1⟩ |
      ⟨d', n', r, h1, -, -, hF, -⟩
    · cases h1
    · cases h1
      obtain ⟨rv, -, -, hFE, -⟩ := hF
      simp only [Epilogue.Fits, hs, CorrWarp.epi] at hFE
      exact hFE.1
  have hb : Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩ .shfl = n .shfl := by
    simp [Code.bump, cls, Execution.isShfl]
  have hnbc : ∀ q, Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩ (.corr (.nb q)) =
      n (.corr (.nb q)) + if decide (id = (Correction.nbOf L g q).toNat) then 1 else 0 := fun q =>
          by
    simp [Code.bump, cls, Correction.cls]
  -- the state after an event of the lane's barrier `q`
  have slot : ∀ (q : Fin 2) s' v', id = (Correction.nbOf L g q).toNat →
      Progress.Cr.part d.scheduler.site = some (q, false) → Progress.Cr.part s' = some (q, true) →
      (Progress.Cr.tailOff d.scheduler.site).getD (Progress.Cr.roundOff d.scheduler.site) <
        (Progress.Cr.tailOff s').getD (Progress.Cr.roundOff s') →
      Correction.succ p L g d.scheduler ⟨pc, .bar id cnt md⟩ = some (some (Correction.D.mk' s' v'))
          →
      ∃ σ', Frame.stateAt (thread p L) X g (k + 1) = some (some σ') ∧
        Progress.Cr.time p d.scheduler n < Progress.time p L g σ' := by
    intro q s' v' hid h1 h2 h3 h4
    refine ⟨_, hstep _ h4, ?_⟩
    show _ < Progress.Cr.time p (Correction.D.mk' s' v')
      (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
    have hq : Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩ (.corr (.nb q)) =
        n (.corr (.nb q)) + 1 := by rw [hnbc q, hid]; simp
    simp only [Progress.Cr.time, h1, h2, Progress.Cr.slot, hq, ite_true,
      Bool.false_eq_true, ite_false, Nat.sub_zero, Nat.add_sub_cancel]
    unfold Progress.clk
    omega
  rcases corr_bar_at hp hX hFw hub hw hw1 he hσ with ⟨-, -, hs, -, ht⟩ | ⟨l, -, -, hs, -, -, ht⟩ |
    ⟨st, R, r, a, hid, -, hR, hnb, hsig, ha, hr, ht, hn0, hcn⟩
  · refine ⟨_, hstep (Correction.D.mk' (.arr 0) d.scheduler.v) (by simp only [Correction.succ, hs]),
      ?_⟩
    rw [ht]
    show _ < Progress.Cr.time p (Correction.D.mk' (.arr 0) d.scheduler.v)
      (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
    have := hshfl hs
    simp [Progress.Cr.time, Progress.Cr.part, Progress.Cr.endOff, Progress.Cr.late,
      Progress.passTime, hb, Progress.Out.ballots, Progress.Out.coll, Progress.Cr.toE,
      Epilogue.Site.shfl, Epilogue.Site.ballot, this]
  · refine ⟨_, hstep (Correction.D.mk' (.exit l) d.scheduler.v) (by simp only [Correction.succ,
      hs]), ?_⟩
    rw [ht]
    show _ < Progress.Cr.time p (Correction.D.mk' (.exit l) d.scheduler.v)
      (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩)
    simp only [Progress.Cr.time, Progress.Cr.part, Progress.Cr.endOff]
    unfold Progress.endT
    split <;> omega
  · have hidn : id = (Correction.nbOf L g st).toNat := by rw [corr_nbW hw hw1, hid]
    have hg := Frame.lt_of_get hX he
    have hbm := hR.bmax hp hg
    obtain ⟨s, v, kk⟩ := d
    simp only [Correction.Control.D.scheduler] at hnb hsig ha hr ht hn0 slot ⊢
    cases s <;> simp only [Correction.Site.isNb, Bool.false_eq_true] at hnb
    case rbar q =>
      obtain rfl : q = st := by simpa [Correction.Control.D.scheduler, Correction.sig] using hsig
      exact slot q (.rscale q) v.scheduler hidn rfl rfl
        (by simp [Progress.Cr.tailOff, Progress.Cr.roundOff]) rfl
    case fbar q =>
      obtain rfl : q = st := by simpa [Correction.Control.D.scheduler, Correction.sig] using hsig
      exact slot q (.fsum q) v.scheduler hidn rfl rfl (by simp [Progress.Cr.tailOff]) rfl
    case nb q =>
      obtain rfl : q = st := by simpa [Correction.Control.D.scheduler, Correction.sig] using hsig
      obtain rfl | rfl : q = 0 ∨ q = 1 := by fin_cases q <;> simp
      · exact slot 0 .free v.scheduler hidn rfl rfl
          (by simp [Progress.Cr.tailOff, Progress.Cr.roundOff]) rfl
      · have hr0 : r = 0 := by
          rcases hr with ⟨-, h⟩ | ⟨⟨h, -⟩, -⟩ | ⟨h, -⟩
          · exact h
          · exact absurd h (by simp [Correction.Site.pc])
          · exact absurd h (by simp [Correction.Site.pc])
        subst hr0
        have h0 : n (.corr (.nb 0)) = 1 := by
          rw [hn0]; show passed (ptsOf (.nb 0)) (.nb 1) 0 = 1; decide
        have hne : id ≠ (Correction.nbOf L g 0).toNat := by
          rw [hid, corr_nbW hw hw1]
          simp
        refine ⟨_, hstep (Correction.enterRounds p L g ⟨.nb 1, v.scheduler, kk⟩) rfl, ?_⟩
        have hT : ∀ s', Progress.Cr.part s' = some (0, false) →
            ∀ v', Progress.Cr.time p ⟨.nb 1, v.scheduler, kk⟩ n < Progress.Cr.time p
              (Correction.D.mk' s' v') (Code.bump (cls L g) n ⟨pc, .bar id cnt md⟩) := by
          intro s' h1 v'
          rw [ht]
          simp only [Progress.Cr.time, h1, Progress.Cr.slot, hnbc 0, hne, decide_false,
            Bool.false_eq_true, ite_false, h0, Nat.add_zero, Nat.sub_zero]
          rw [Progress.slotOf_eq (by omega)]
          have ha' : a = (0, Progress.bandC 1) := by
            have : val (.nb 1) = some (0, Progress.bandC 1) := by decide
            exact Option.some.inj (ha.symm.trans this)
          rw [ha']
          unfold valT Progress.clk Progress.span
          simp only [Progress.bandC]
          omega
        refine lt_of_lt_of_eq ?_ (erase_time (L := L) (g := g) _ _).symm
        have he' : ∃ s' v', Correction.enterRounds p L g ⟨.nb 1, v.scheduler, kk⟩ = Correction.D.mk'
            s' v' ∧
            Progress.Cr.part s' = some (0, false) := by
          simp only [Correction.enterRounds, Correction.D.ite]
          split
          · exact ⟨.farr0, _, rfl, rfl⟩
          · exact ⟨.rbar 0, _, rfl, rfl⟩
        obtain ⟨s', v', e1, e2⟩ := he'
        rw [e1]
        exact hT s' e2 v'

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
