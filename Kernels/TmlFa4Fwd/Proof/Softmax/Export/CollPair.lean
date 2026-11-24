-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollReady
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollSite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collectives of two lanes of a softmax warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (nexts lz allSites mem_allSites)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

private theorem epi_inj {s s' : Softmax.Site} (hs : s.wcoll = true) (hr : s.rcoll = false)
    (hs' : s'.wcoll = true) (hr' : s'.rcoll = false) (h : SmWarp.epi s = SmWarp.epi s') :
    s = s' := by
  cases s <;> simp [Softmax.Site.wcoll, Softmax.Site.rcoll] at hs hr <;>
    cases s' <;> simp [Softmax.Site.wcoll, Softmax.Site.rcoll] at hs' hr' <;>
    simp [SmWarp.epi] at h <;> simp_all

/-- What a state of a tag is. -/
private theorem soft_tag {x : Nat} {σ : (thread p L x).D} {a : STag Softmax.Site}
    (h : softTag p L x σ = some a) :
    (∃ s n, σ = (.inl s, n) ∧ ((∃ j, s.site = .sh j ∧ a = .start j) ∨
        ∃ j, s.site = .elect j ∧ a = .init j)) ∨
      ∃ d n, σ = (.inr ⟨.softmax, d⟩, n) ∧ d.site.wcoll = true ∧
        ((d.site.rcoll = true ∧ a = .mid d.site) ∨
          (d.site.rcoll = false ∧ a = .scan (SmWarp.epi d.site))) := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · left
    refine ⟨s, n, rfl, ?_⟩
    simp only [softTag] at h
    cases hs : s.site <;> rw [hs] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
    · exact .inl ⟨_, rfl, h.symm⟩
    · exact .inr ⟨_, rfl, h.symm⟩
  all_goals first
    | (simp [softTag] at h; done)
    | (right
       refine ⟨d, n, rfl, ?_⟩
       simp only [softTag, softTagS] at h
       split at h
       · rename_i hw
         refine ⟨hw, ?_⟩
         split at h
         · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
         · rename_i hr
           exact .inr ⟨by simpa using hr, (Option.some.inj h).symm⟩
       · cases h)

/-- The lanes of softmax warp `w` of CTA `c`. -/
def SoftLane (L : Launch) (w c x : Nat) : Prop :=
  x < L.threads ∧ Prologue.warpIndex L x = w ∧ x / L.block = c

private theorem softSiteShape_eq {s : Softmax.Site} (h : ¬ ∃ l, s = .pre l ∨ s = .tiles l)
    (b b' : BitVec 64) : softSiteShape s b = softSiteShape s b' := by
  unfold softSiteShape
  split
  · exact absurd ⟨_, .inl rfl⟩ h
  · exact absurd ⟨_, .inr rfl⟩ h
  · rfl

/-- A site whose event may block. -/
private def blkS : Softmax.Site → Bool
  | .setmax | .bar1 | .bsync _ | .narr _ | .finarr | .barEnd _ => true
  | s => s.tcS

/-- The blocking events that lead to a collective. -/
private def blkNext (s s' : Softmax.Site) : Bool :=
  !s'.wcoll || match s with
    | .bar1 => s' == .down .first
    | .finarr => s' == .down .second
    | .pwst r k => k.val == 1 && s' == .pws r
    | s => !blkS s

private theorem blk_next : [false, true].all (fun b => allSites.all fun s =>
    (nexts b s).all (blkNext s)) = true := by decide +kernel

private theorem soft_unblock {d : Softmax.D} {e : Event} (hev : Softmax.EvS p L g d e)
    (hs : blkS d.site = false) : Sched.Unblocking e.kind := by
  obtain ⟨hev, -⟩ := hev
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [blkS, Softmax.Site.tcS, reduceCtorEq] at hs <;>
    simp only [Softmax.Ev] at hev
  all_goals (try simp only [Epilogue.Ev, Softmax.Site.toE] at hev)
  all_goals shape_destruct hev
  all_goals (subst_vars; trivial)

/-- A blocking event of a softmax state leads to a state. -/
private theorem blk_live {d : Softmax.Control.D} {e : Event}
    (hev : Softmax.EvS p L g d.scheduler e) (hs : blkS d.site = true)
    (hw : ∀ c, d.site = .sldw c → d.k = 1) :
    ∃ d', Softmax.Control.succ p L g d e = some (some d') := by
  obtain ⟨hev, hub⟩ := hev
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [blkS, Softmax.Site.tcS, Bool.false_eq_true] at hs
  case sld r c =>
    simp only [Softmax.Ev, Softmax.Control.D.scheduler] at hev
    rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
    · simp only at h
      subst h
      cases r <;> exact ⟨_, rfl⟩
    · exact absurd h (hub f)
  case pst r q =>
    cases r <;> fin_cases q <;> by_cases hk : kk = 0 <;>
      simp [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ, hk]
  case sldw c =>
    have hk : kk = 1 := hw c rfl
    subst hk
    exact ⟨_, rfl⟩
  all_goals exact ⟨_, rfl⟩

/-- **The classification of a softmax warp's states** by their collectives. -/
def softCls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) {w : Nat} (hw8 : w < 8) (c : Nat) :
    CollCls p L X (SoftLane L w c) (softShape p L) (STag Softmax.Site) where
  tag := softTag p L
  role t := (∃ s, t = .mid s) ∨ ∃ s, t = .scan s
  cls x := SCls (softR p L w c) x (startEl w)
  at_ := fun {_ _ σ} hA hσ => (soft_collAt hp hX hA.1 hw8 hA.2.1 hσ).trans
    (by rw [softTag_isSome σ])
  pos := fun {_ _ σ} hA hP => (softTag_isSome σ).trans (soft_isP hp hX hub hA.1 hw8 hA.2.1 hP)
  ok := fun hA hσ => by
    have := soft_cls hp hX (launchFollow hp hX) hub hA.1 hw8 hA.2.1 hσ
    rwa [hA.2.2] at this
  order := fun hA hA' h1 h2 hle => h1.order hp hA'.1 (hA'.2.2.trans hA.2.2.symm) h2 hle
  static := by
    intro x y k k' σ σ' a hA hA' hσ hσ' hx hy
    rcases soft_tag hx with ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl, hw, hd⟩ <;>
      rcases soft_tag hy with ⟨s', n', rfl, hs'⟩ | ⟨d', n', rfl, hw', hd'⟩
    · have : s.site = s'.site := by
        rcases hs with ⟨j, h1, rfl⟩ | ⟨j, h1, rfl⟩ <;>
          rcases hs' with ⟨j', h2, h3⟩ | ⟨j', h2, h3⟩ <;> cases h3 <;> rw [h1, h2]
      refine ⟨show s.site.pc = s'.site.pc by rw [this], ?_⟩
      show pcShape s.site.pc = pcShape s'.site.pc
      rw [this]
    · exfalso
      rcases hs with ⟨j, h1, rfl⟩ | ⟨j, h1, rfl⟩ <;> rcases hd' with ⟨-, h3⟩ | ⟨-, h3⟩ <;> cases h3
    · exfalso
      rcases hs' with ⟨j, h1, rfl⟩ | ⟨j, h1, rfl⟩ <;> rcases hd with ⟨-, h3⟩ | ⟨-, h3⟩ <;> cases h3
    · have hsite : d.site = d'.site := by
        rcases hd with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases hd' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
          simp only [STag.mid.injEq, STag.scan.injEq, reduceCtorEq] at h3
        · exact h3
        · exact epi_inj hw h1 hw' h2 h3
      refine ⟨show d.site.pc = d'.site.pc by rw [hsite], ?_⟩
      show softSiteShape d.site d.v.sc.bal = softSiteShape d'.site d'.v.sc.bal
      rw [← hsite]
      by_cases hl : ∃ l, d.site = .pre l ∨ d.site = .tiles l
      · obtain ⟨l, hl⟩ := hl
        have hz : ∀ {x k : Nat} {d : Softmax.Control.D} {n : Cls → Nat}, SoftLane L w c x →
            Frame.stateAt (thread p L) X x k = some (some (SmWarp.sinj p L x d n)) →
            (d.site = .pre l ∨ d.site = .tiles l) →
            ∃ ns nv, Epilogue.Fits p L x (SmWarp.toE d.scheduler) ns nv ∧
              ((SmWarp.toE d.scheduler).site = .pre l ∨
                (SmWarp.toE d.scheduler).site = .tiles l) := by
          intro x k d n hA hσ hl
          obtain ⟨c, rb, rp, -, -, ⟨hFE, -⟩, -⟩ := soft_open hp hX hub hA.1 hw8 hA.2.1 hσ
          refine ⟨_, _, hFE, ?_⟩
          rcases hl with h | h
          · left; show SmWarp.epi d.site = _; rw [h]; rfl
          · right; show SmWarp.epi d.site = _; rw [h]; rfl
        obtain ⟨_, _, hF, h1⟩ := hz hA hσ hl
        obtain ⟨_, _, hF', -⟩ := hz hA' hσ' (by rw [← hsite]; exact hl)
        have hb : d.v.sc.bal = d'.v.sc.bal :=
          Epilogue.bal_same (d := SmWarp.toE d.scheduler) (d' := SmWarp.toE d'.scheduler)
            (hA.2.2.trans hA'.2.2.symm) hF hF' h1 (by
              show SmWarp.epi d'.site = SmWarp.epi d.site; rw [hsite])
        rw [hb]
      · exact softSiteShape_eq hl _ _
  exit := by
    intro x y N t a k pc σ hA hA' h1 hσ he
    refine h1.lt_exit (hA'.2.2.trans hA.2.2.symm) ?_
    have hw8' : Prologue.warpIndex L y < 8 := by rw [hA'.2.1]; exact hw8
    rcases SmWarp.open_ev hp hX (launchFollow hp hX) hw8' he (fun f h => by cases h) with
      ⟨s', n, -, -, -, hi, hev⟩ | ⟨d, n, hσ1, h0, hR, -, hev⟩
    · exact (start_not_exit hi.2 hev).elim
    · obtain ⟨l, hl⟩ := soft_exit_site' hev.1
      have := soft_exit_cls hp hX (launchFollow hp hX) hub hA'.1 hw8 hA'.2.1 hσ1 hl
      rwa [hA'.2.2] at this
  entry := by
    intro x k σ a hA hσ hx hr
    rcases soft_tag hx with ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl, hw, hd⟩
    · exfalso
      rcases hs with ⟨j, h1, rfl⟩ | ⟨j, h1, rfl⟩ <;> rcases hr with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · refine ⟨_, d, n, rfl, fun hE => ?_⟩
      have hE' : d.site = .setmax := hE
      rw [hE'] at hw
      cases hw
  last := by
    intro x k σ e hA he hσ hb
    have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    have hFw := launchFollow hp hX
    have hR := (SmWarp.good hp hX hw8 hA.1 hA.2.1 k).2 _ hσ
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · have key : (thread p L x).next (.inl s, n) e ≠ none ∧ ∀ σ',
          (thread p L x).next (.inl s, n) e = some (some σ') →
          (∃ s' : Startup.D, σ'.1 = .inl s' ∧ startAt s'.site = false) ∨
            ∃ i, σ'.1 = .inr ⟨i, (frag p L x i).init⟩ := by
        by_cases h0 : w = 0
        · subst h0
          obtain ⟨h1, h2⟩ := start_last0 hp hX he hσ hR.1 hne hb
          refine ⟨h1, fun σ' hσ' => ?_⟩
          rcases bar_last h2 hσ' with ⟨s', hs', r, hr⟩ | h
          · exact .inl ⟨s', hs', by rw [hr]; rfl⟩
          · exact .inr h
        · have hS : StartAt L w s n := by
            have := hR.1
            simpa only [SmWarp.StartW, h0, ite_false] using this
          obtain ⟨h1, h2⟩ := start_last hp hX hA.2.1 h0 (by omega) he hσ hS hb
          have hbar : s.site = .bar := by
            have hev := (start_fired hp hX he hσ).1
            by_contra hnb
            apply hb
            obtain ⟨site, x1, x2, x3⟩ := s
            cases site <;> simp only [StartAt] at hS
            case sh j =>
              fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;>
                rw [hk] <;> trivial
            case fence => simp only [Startup.Ev] at hev; rw [hev]; trivial
            case bar => exact absurd rfl hnb
          refine ⟨h1, fun σ' hσ' => ?_⟩
          rcases bar_last hbar hσ' with ⟨s', hs', r, hr⟩ | h
          · exact .inl ⟨s', hs', by rw [hr]; rfl⟩
          · exact .inr h
      refine ⟨key.1, fun σ' hσ' => .inl ?_⟩
      obtain ⟨σ', n'⟩ := σ'
      rcases key.2 _ hσ' with ⟨s', hs', hj⟩ | ⟨i, hi⟩
      · simp only at hs'
        subst hs'
        simp only [softTag]
        revert hj
        cases s'.site <;> simp [startAt]
      · simp only at hi
        subst hi
        cases i <;> rfl
    · have hev := (SmWarp.fired_soft hp hX he hσ hne).1
      have hblk : blkS d.site = true := by
        by_contra h
        exact hb (soft_unblock hev (Bool.eq_false_iff.mpr h))
      have hnx := SmWarp.next_sinj (p := p) (L := L) (g := x) d n e
      obtain ⟨d', hd'⟩ : ∃ d', Softmax.Control.succ p L x d e = some (some d') := by
        refine blk_live hev hblk fun c' hc' => ?_
        obtain ⟨_, _, _, hQ, -⟩ := soft_open hp hX hub hA.1 hw8 hA.2.1 hσ
        exact hQ.wait c' hc'
      rw [hd'] at hnx
      refine ⟨fun hc => ?_, fun σ' hσ' => ?_⟩
      · have h0 := hnx.symm.trans hc
        cases h0
      obtain rfl := Option.some.inj (Option.some.inj (hnx.symm.trans hσ'))
      by_cases hw' : d'.site.wcoll = true
      swap
      · left
        show softTagS d'.site = none
        unfold softTagS; rw [ite_eq_right hw']
      right
      have hmv := soft_move hd'
      rcases hmv with ⟨-, hc, -⟩ | ⟨hs, hd, -⟩ | ⟨hs, -⟩
      · exfalso
        apply hb
        rcases hc with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ <;> rw [hk] <;> trivial
      · exfalso
        rw [hs] at hw'
        revert hd hw'
        cases d.site <;> simp [Softmax.Site.delayed, Softmax.Site.wcoll]
      have hm := List.all_eq_true.mp (List.all_eq_true.mp
        (List.all_eq_true.mp blk_next (lz L x) (by cases lz L x <;> simp)) d.site
        (mem_allSites _)) d'.site hs
      simp only [blkNext, hw', Bool.not_true, Bool.false_or] at hm
      have hcase : (d.site = .bar1 ∧ d'.site = .down .first) ∨
          (d.site = .finarr ∧ d'.site = .down .second) ∨
          ∃ r k, d.site = .pwst r k ∧ d'.site = .pws r := by
        cases hs0 : d.site <;> rw [hs0] at hm hblk <;>
          simp only [Bool.and_eq_true, beq_iff_eq, hblk, Bool.not_true, Bool.false_eq_true] at hm
        · exact .inl ⟨rfl, hm⟩
        · exact .inr (.inr ⟨_, _, rfl, hm.2⟩)
        · exact .inr (.inl ⟨rfl, hm⟩)
      have epiS : ∀ (k : Epilogue.Scan) (dy : Softmax.Control.D), dy.site.wcoll = true →
          dy.site.rcoll = false → (STag.scan (.down k) : STag Softmax.Site) =
            .scan (SmWarp.epi dy.site) → dy.site = .down k := fun k dy h1 h2 h3 =>
        (epi_inj (s := .down k) rfl rfl h1 h2 (STag.scan.inj h3)).symm
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨r, kk, h1, h2⟩
      · refine ⟨.scan (.down .first), by show softTagS d'.site = _; rw [h2]; rfl, .inr ⟨_, rfl⟩,
          .inr fun y σy hAy hsw hlen hy hty hn hrel hnx => ?_⟩
        rcases soft_tag hty with ⟨s, n', rfl, ⟨_, _, hs⟩ | ⟨_, _, hs⟩⟩ |
          ⟨dy, ny, rfl, h3, ⟨_, h5⟩ | ⟨h4, h5⟩⟩
        · cases hs
        · cases hs
        · cases h5
        · refine soft_ready_bar1 hp hX hFw hub hw8 hsw hAy.2.1 hrel hnx he hσ hy h1
            (epiS _ _ h3 h4 h5) ?_
          have hs0 : d.scheduler.site = .bar1 := h1
          simpa only [Softmax.Ev, hs0] using hev.1
      · refine ⟨.scan (.down .second), by show softTagS d'.site = _; rw [h2]; rfl, .inr ⟨_, rfl⟩,
          .inr fun y σy hAy hsw hlen hy hty hn hrel hnx => ?_⟩
        rcases soft_tag hty with ⟨s, n', rfl, ⟨_, _, hs⟩ | ⟨_, _, hs⟩⟩ |
          ⟨dy, ny, rfl, h3, ⟨_, h5⟩ | ⟨h4, h5⟩⟩
        · cases hs
        · cases hs
        · cases h5
        · refine soft_ready_fin hp hX hFw hub hw8 hsw hAy.2.1 hrel hnx he hσ hy h1
            (epiS _ _ h3 h4 h5) ?_
          have hs0 : d.scheduler.site = .finarr := h1
          have := hev.1
          simp only [Softmax.Ev, hs0] at this
          exact ⟨_, _, this⟩
      · refine ⟨.mid (.pws r), by show softTagS d'.site = _; rw [h2]; rfl, .inl ⟨_, rfl⟩,
          .inr fun y σy hAy hsw hlen hy hty hn hrel hnx => ?_⟩
        rcases soft_tag hty with ⟨s, n', rfl, ⟨_, _, hs⟩ | ⟨_, _, hs⟩⟩ |
          ⟨dy, ny, rfl, h3, ⟨_, h5⟩ | ⟨h4, h5⟩⟩
        · cases hs
        · cases hs
        · have hc : isTcColl e = true := by
            rw [soft_isTc hev]
            show d.site.tcS = true
            rw [h1]; rfl
          have hσ1 : Frame.stateAt (thread p L) X x (X.tr x).length =
              some (some (SmWarp.sinj p L x d' (Code.bump (cls L x) n e))) := by
            rw [← hlen, Frame.stateAt_succ (C := thread p L)
              (show (X.tr x)[k]? = some e from he), hσ]
            exact hσ'
          exact soft_ready_wait hp hX hFw hub hw8 hsw hAy.2.1 hrel he hc hlen hσ1 hy h2
            (STag.mid.inj h5).symm hn
        · cases h5

/-- **The collectives of two lanes of a softmax warp.** -/
theorem soft_pair (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hs : SameWarp L g h) (hw8 : Prologue.warpIndex L g < 8) :
    Sched.WarpPair m (Progress.timed p L) X (CollAt p L) (softShape p L) g h :=
  warpPair_of_cls hp hX hub (softCls hp hX hub hw8 (g / L.block)) hs ⟨hs.1.1, rfl, rfl⟩
    ⟨hs.1.2.1, hs.2.symm, hs.1.2.2.symm⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
