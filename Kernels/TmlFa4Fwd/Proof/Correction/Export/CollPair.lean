-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.CollSite
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollOfCls
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collectives of two lanes of a correction warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (nexts allSites mem_allSites)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

private theorem epi_inj {s s' : Correction.Site} (hs : s.wcoll = true) (hr : s.isRvote = false)
    (hs' : s'.wcoll = true) (hr' : s'.isRvote = false) (h : CorrWarp.epi s = CorrWarp.epi s') :
    s = s' := by
  cases s <;> simp [Correction.Site.wcoll, Correction.Site.isRvote] at hs hr <;>
    cases s' <;> simp [Correction.Site.wcoll, Correction.Site.isRvote] at hs' hr' <;>
    simp [CorrWarp.epi] at h <;> simp_all

/-- What a state of a tag is. -/
private theorem corr_tag {x : Nat} {σ : (thread p L x).D} {a : STag Correction.Site}
    (h : corrTag p L x σ = some a) :
    (∃ s n, σ = (.inl s, n) ∧ ∃ j, s.site = .sh j ∧ a = .start j) ∨
      ∃ d n, σ = (.inr ⟨.correction, d⟩, n) ∧ d.site.wcoll = true ∧
        ((d.site.isRvote = true ∧ a = .mid d.site) ∨
          (d.site.isRvote = false ∧ a = .scan (CorrWarp.epi d.site))) := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · left
    refine ⟨s, n, rfl, ?_⟩
    simp only [corrTag] at h
    cases hs : s.site <;> rw [hs] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
    exact ⟨_, rfl, h.symm⟩
  all_goals first
    | (simp [corrTag] at h; done)
    | (right
       refine ⟨d, n, rfl, ?_⟩
       simp only [corrTag, corrTagS] at h
       split at h
       · rename_i hw
         refine ⟨hw, ?_⟩
         split at h
         · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
         · rename_i hr
           exact .inr ⟨by simpa using hr, (Option.some.inj h).symm⟩
       · cases h)

/-- The lanes of correction warp `w` of CTA `c`. -/
def CorrLane (L : Launch) (w c x : Nat) : Prop :=
  x < L.threads ∧ Prologue.warpIndex L x = w ∧ x / L.block = c

private theorem corrSiteShape_eq {s : Correction.Site} (h : ¬ ∃ l, s = .pre l ∨ s = .tiles l)
    (b b' : BitVec 64) : corrSiteShape s b = corrSiteShape s b' := by
  unfold corrSiteShape
  split
  · exact absurd ⟨_, .inl rfl⟩ h
  · exact absurd ⟨_, .inr rfl⟩ h
  · rfl

/-- A site whose event may block. -/
private def blkS : Correction.Site → Bool
  | .setmax | .bar1 | .barEnd _ | .nb _ | .rbar _ | .fbar _ | .rld _ _ | .rldw _ _ | .rst _ _
  | .rwait _ | .fld _ _ | .fwl _ _ => true
  | _ => false

private theorem blk_next : allSites.all (fun s =>
    (nexts s).all fun s' => !blkS s || !s'.wcoll) = true := by decide +kernel

private theorem corr_unblock {d : Correction.Control.D} {e : Event}
    (hev : Correction.Control.Ev p L g d e) (hs : blkS d.site = false) :
    Sched.Unblocking e.kind := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [blkS, reduceCtorEq] at hs <;>
    simp only [Correction.Control.Ev, Correction.Ev, Correction.Control.D.scheduler,
      Correction.rdOrUb, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals trivial

/-- A blocking event of a correction state leads to a state. -/
private theorem blk_live {d : Correction.Control.D} {e : Event}
    (hev : Correction.Control.Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hs : blkS d.site = true) :
    ∃ o, Correction.Control.succ p L g d e = some o := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [blkS, Bool.false_eq_true] at hs
  case rld st c | fld st c =>
    simp only [Correction.Control.Ev, Correction.Ev, Correction.Control.D.scheduler] at hev
    rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
    · subst h
      exact ⟨_, rfl⟩
    · exact absurd h (hub f)
  case rldw st c =>
    by_cases hk : kk = 1
    · subst hk; exact ⟨_, rfl⟩
    · exact ⟨none, by
        simp [Correction.Control.succ, Correction.succ, Correction.Control.D.scheduler, hk]⟩
  case rst st c =>
    by_cases hc : c.val = 7 <;>
      simp [Correction.Control.succ, Correction.succ, Correction.Control.D.scheduler, hc]
  case nb st => fin_cases st <;> exact ⟨_, rfl⟩
  all_goals exact ⟨_, rfl⟩

/-- The return's site. -/
private theorem corr_exit_kind {d : Correction.Control.D} {pc : Nat}
    (hev : Correction.Control.Ev p L g d ⟨pc, .exit⟩) : ∃ l, d.site = .exit l := by
  obtain ⟨s, v, kk⟩ := d
  cases s
  case exit l => exact ⟨l, rfl⟩
  all_goals exfalso
  all_goals simp only [Correction.Control.Ev, Correction.Ev, Correction.Control.D.scheduler,
    Correction.rdOrUb, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals contradiction

/-- **The classification of a correction warp's states** by their collectives. -/
def corrCls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) {w : Nat} (hw8 : 8 ≤ w ∧ w ≤ 11) (c : Nat) :
    CollCls p L X (CorrLane L w c) (corrShape p L) (STag Correction.Site) where
  tag := corrTag p L
  role t := (∃ s, t = .mid s) ∨ ∃ s, t = .scan s
  cls x := SCls (corrMid hp w c) x 0
  at_ := fun {_ _ σ} hA hσ => (corr_collAt hp hX hA.1 hw8 hA.2.1 hσ).trans
    (by rw [corrTag_isSome σ])
  pos := fun {_ _ σ} hA hP => (corrTag_isSome σ).trans (corr_isP hp hX hub hA.1 hw8 hA.2.1 hP)
  ok := fun hA hσ => by
    have := corr_cls hp hX hub hA.1 hw8 hA.2.1 hσ
    rwa [hA.2.2] at this
  order := fun hA hA' h1 h2 hle => h1.order hp hA'.1 (hA'.2.2.trans hA.2.2.symm) h2 hle
  static := by
    intro x y k k' σ σ' a hA hA' hσ hσ' hx hy
    rcases corr_tag hx with ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl, hw, hd⟩ <;>
      rcases corr_tag hy with ⟨s', n', rfl, hs'⟩ | ⟨d', n', rfl, hw', hd'⟩
    · have : s.site = s'.site := by
        obtain ⟨j, h1, rfl⟩ := hs
        obtain ⟨j', h2, h3⟩ := hs'
        cases h3
        rw [h1, h2]
      refine ⟨show s.site.pc = s'.site.pc by rw [this], ?_⟩
      show pcShape s.site.pc = pcShape s'.site.pc
      rw [this]
    · exfalso
      obtain ⟨j, h1, rfl⟩ := hs
      rcases hd' with ⟨-, h3⟩ | ⟨-, h3⟩ <;> cases h3
    · exfalso
      obtain ⟨j, h1, rfl⟩ := hs'
      rcases hd with ⟨-, h3⟩ | ⟨-, h3⟩ <;> cases h3
    · have hsite : d.site = d'.site := by
        rcases hd with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases hd' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
          simp only [STag.mid.injEq, STag.scan.injEq, reduceCtorEq] at h3
        · exact h3
        · exact epi_inj hw h1 hw' h2 h3
      refine ⟨show d.site.pc = d'.site.pc by rw [hsite], ?_⟩
      show corrSiteShape d.site d.v.sc.bal = corrSiteShape d'.site d'.v.sc.bal
      rw [← hsite]
      by_cases hl : ∃ l, d.site = .pre l ∨ d.site = .tiles l
      · obtain ⟨l, hl⟩ := hl
        have hz : ∀ {x k : Nat} {d : Correction.Control.D} {n : Cls → Nat}, CorrLane L w c x →
            Frame.stateAt (thread p L) X x k = some (some (CorrWarp.cinj p L x d n)) →
            (d.site = .pre l ∨ d.site = .tiles l) →
            ∃ ns nv, Epilogue.Fits p L x (CorrWarp.toE d.scheduler) ns nv ∧
              ((CorrWarp.toE d.scheduler).site = .pre l ∨
                (CorrWarp.toE d.scheduler).site = .tiles l) := by
          intro x k d n hA hσ hl
          obtain ⟨_, _, -, _, -, -, hFE, -⟩ := corr_open hp hX hub hA.1 hw8 hA.2.1 hσ
          refine ⟨_, _, hFE, ?_⟩
          rcases hl with h | h
          · left; show CorrWarp.epi d.site = _; rw [h]; rfl
          · right; show CorrWarp.epi d.site = _; rw [h]; rfl
        obtain ⟨_, _, hF, h1⟩ := hz hA hσ hl
        obtain ⟨_, _, hF', -⟩ := hz hA' hσ' (by rw [← hsite]; exact hl)
        have hb : d.v.sc.bal = d'.v.sc.bal :=
          Epilogue.bal_same (d := CorrWarp.toE d.scheduler) (d' := CorrWarp.toE d'.scheduler)
            (hA.2.2.trans hA'.2.2.symm) hF hF' h1 (by
              show CorrWarp.epi d'.site = CorrWarp.epi d.site; rw [hsite])
        rw [hb]
      · exact corrSiteShape_eq hl _ _
  exit := by
    intro x y N t a k pc σ hA hA' h1 hσ he
    refine h1.lt_exit (hA'.2.2.trans hA.2.2.symm) ?_
    have hw8' : 8 ≤ Prologue.warpIndex L y ∧ Prologue.warpIndex L y ≤ 11 := by
      rw [hA'.2.1]; exact hw8
    rcases CorrWarp.open_ev hp hX (launchFollow hp hX) hw8'.1 hw8'.2 he (fun f h => by cases h) with
      ⟨s', n, -, -, -, hi, hev⟩ | ⟨d, n, hσ1, h0, hR, -, hev, -⟩
    · exact (start_not_exit hi.2 hev).elim
    · have hl : ∃ l, d.site = .exit l := by
        have hk := corr_exit_kind hev
        exact hk
      obtain ⟨l, hl⟩ := hl
      have := corr_exit_cls hp hX hub hA'.1 hw8 hA'.2.1 hσ1 hl
      rwa [hA'.2.2] at this
  entry := by
    intro x k σ a hA hσ hx hr
    rcases corr_tag hx with ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl, hw, hd⟩
    · exfalso
      obtain ⟨j, h1, rfl⟩ := hs
      rcases hr with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · refine ⟨_, d, n, rfl, fun hE => ?_⟩
      have hE' : d.site = .setmax := hE
      rw [hE'] at hw
      cases hw
  last := by
    intro x k σ e hA he hσ hb
    have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    have hR := (CorrWarp.good hp hX hw8 hA.1 hA.2.1 k).2 _ hσ
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · obtain ⟨h1, h2⟩ := start_last hp hX hA.2.1 (by omega) (by omega) he hσ hR.1 hb
      refine ⟨h1, fun σ' hσ' => .inl ?_⟩
      obtain ⟨σ', n'⟩ := σ'
      rcases h2 _ hσ' with ⟨s', hs', hj⟩ | ⟨i, hi⟩
      · simp only at hs'
        subst hs'
        simp only [corrTag]
      · simp only at hi
        subst hi
        cases i <;> rfl
    · have hev := (CorrWarp.fired_both hp hX he hσ hne).1
      have hblk : blkS d.site = true := by
        by_contra h
        exact hb (corr_unblock hev (Bool.eq_false_iff.mpr h))
      obtain ⟨o, ho⟩ := blk_live hev hne hblk
      have hnx := CorrWarp.next_cinj (p := p) (L := L) (g := x) d n e
      rw [ho] at hnx
      refine ⟨fun hc => ?_, fun σ' hσ' => .inl ?_⟩
      · have h0 := hnx.symm.trans hc
        cases h0
      cases o with
      | none => exact absurd (hnx.symm.trans hσ') (by simp)
      | some d' =>
        obtain rfl := Option.some.inj (Option.some.inj (hnx.symm.trans hσ'))
        have hub0 : n .ub = 0 := ub_zero hX he hσ
        obtain ⟨hJ, -⟩ := hR hub0
        obtain ⟨a, ev, -, -, hs, hsite, -⟩ := Correction.Control.represents
          (d := d) (n := CorrWarp.rc n) hJ.counts hev hne ho
        show corrTagS d'.site = none
        unfold corrTagS
        have hw : d'.site.wcoll = false := by
          rw [← hsite]
          have hnx' : ∀ s', s' ∈ nexts d.site → s'.wcoll = false := by
            intro s' hm
            have := List.all_eq_true.mp (List.all_eq_true.mp blk_next d.site (mem_allSites _)) s' hm
            simpa [hblk] using this
          have hself : d.site.wcoll = false := by
            revert hblk
            cases d.site <;> simp [blkS, Correction.Site.wcoll]
          rcases Correction.succ_cases hs with ⟨rfl, -⟩ | ⟨-, -, rfl⟩ | hM
          · exact hself
          · exact hself
          · exact hnx' _ hM.1
        rw [ite_eq_right (by rw [hw]; simp)]

/-- **The collectives of two lanes of a correction warp.** -/
theorem corr_pair (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hs : SameWarp L g h)
    (hw8 : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11) :
    Sched.WarpPair m (Progress.timed p L) X (CollAt p L) (corrShape p L) g h :=
  warpPair_of_cls hp hX hub (corrCls hp hX hub hw8 (g / L.block)) hs ⟨hs.1.1, rfl, rfl⟩
    ⟨hs.1.2.1, hs.2.symm, hs.1.2.2.symm⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
