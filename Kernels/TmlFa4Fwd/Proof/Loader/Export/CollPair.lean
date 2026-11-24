-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollSite
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollOfCls
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Exit
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collectives of two lanes of a loader warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader (CollTag tagOf tagS LCls ld_cls ld_exit_cls wOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

private theorem tagS_some {s s' : Loader.Site} (h : tagS s = some (.site s')) :
    s = s' ∧ s.wcoll = true := by
  unfold tagS at h
  split at h
  · simp only [Option.some.injEq, CollTag.site.injEq] at h; exact ⟨h, ‹_›⟩
  · cases h

private theorem tag_start {x : Nat} {σ : (thread p L x).D} {j : Fin 3}
    (h : tagOf p L x σ = some (.start j)) : ∃ x1 x2 x3 n, σ = (.inl ⟨.sh j, x1, x2, x3⟩, n) := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp [tagOf] at h
    subst h
    exact ⟨_, _, _, _, rfl⟩
  all_goals first
    | (simp [tagOf] at h; done)
    | (simp only [tagOf, tagS] at h
       split at h <;> simp at h)

private theorem tag_site {x : Nat} {σ : (thread p L x).D} {s : Loader.Site}
    (h : tagOf p L x σ = some (.site s)) :
    ∃ b d n, σ = (.inr ⟨.loader b, d⟩, n) ∧ d.site = s ∧ s.wcoll = true := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s' | ⟨_ | _ | _ | _ | r | _, d⟩
  · obtain ⟨site, x1, x2, x3⟩ := s'
    cases site <;> simp [tagOf] at h
  all_goals first
    | (simp [tagOf] at h; done)
    | (obtain ⟨h1, h2⟩ := tagS_some (s := d.site) h
       exact ⟨_, d, n, rfl, h1, h1 ▸ h2⟩)

/-- A blocking event of a loader state is its register request. -/
private theorem block_set {w : Nat} {d : Loader.D} {e : Event} (hev : Loader.Ev p L g w d e)
    (hub : ∀ f, e.kind ≠ .ub f) (hb : ¬ Sched.Unblocking e.kind) :
    d.site = .setmax ∧ ∃ inc n i, e.kind = .setMaxReg inc n i := by
  have hk := ld_ev_kind hev hub
  by_cases hs : d.site = .setmax
  · refine ⟨hs, ?_⟩
    simpa only [Loader.Ev, hs] using hev
  · exfalso
    apply hb
    obtain ⟨s, v, kk⟩ := d
    obtain ⟨pc, kind⟩ := e
    simp only at hk hs ⊢
    revert hk
    generalize Loader.Site.wcoll s = bb
    intro hk
    cases hk <;> first
      | exact trivial
      | (exfalso
         cases s <;> first
           | exact hs rfl
           | (simp [Loader.Ev, Epilogue.Ev, Loader.Site.toE] at hev))

private theorem ldSiteShape_eq {s : Loader.Site} (h : ¬ ∃ l, s = .pre l ∨ s = .tiles l)
    (b b' : BitVec 64) : ldSiteShape s b = ldSiteShape s b' := by
  unfold ldSiteShape
  split
  · exact absurd ⟨_, .inl rfl⟩ h
  · exact absurd ⟨_, .inr rfl⟩ h
  · rfl

/-- The lanes of loader warp `b` of CTA `c`. -/
def LdLane (L : Launch) (b : Bool) (c x : Nat) : Prop :=
  x < L.threads ∧ Prologue.warpIndex L x = wOf b ∧ x / L.block = c

/-- **The classification of a loader warp's states** by their collectives. -/
def ldCls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (b : Bool) (c : Nat) :
    CollCls p L X (LdLane L b c) (ldShape p L) CollTag where
  tag := tagOf p L
  role t := ∃ s, t = .site s
  cls x := LCls p L x b
  at_ := fun {_ _ σ} hA hσ => (ld_collAt hp hX hA.1 hA.2.1 hσ).trans
    (by rw [Loader.tagOf_isSome σ])
  pos := fun {_ _ σ} hA hP => (Loader.tagOf_isSome σ).trans (ld_isP hp hX hub hA.1 hA.2.1 hP)
  ok := fun hA hσ => ld_cls hp hX hub hA.1 hA.2.1 hσ
  order := fun hA hA' h1 h2 hle =>
    h1.order hp hA'.1 (hA'.2.2.trans hA.2.2.symm) h2 hle
  static := by
    intro x y k k' σ σ' a hA hA' hσ hσ' hx hy
    cases a with
    | start j =>
      obtain ⟨x1, x2, x3, n, rfl⟩ := tag_start hx
      obtain ⟨y1, y2, y3, n', rfl⟩ := tag_start hy
      exact ⟨rfl, rfl⟩
    | site s =>
      obtain ⟨b1, d, n, rfl, hd, hsw⟩ := tag_site hx
      obtain ⟨b2, d', n', rfl, hd', -⟩ := tag_site hy
      have hsite : d.site = d'.site := hd.trans hd'.symm
      refine ⟨show d.site.pc = d'.site.pc by rw [hsite], ?_⟩
      show Top.ldSiteShape d.site d.v.sc.bal = Top.ldSiteShape d'.site d'.v.sc.bal
      rw [← hsite]
      by_cases hl : ∃ l, d.site = .pre l ∨ d.site = .tiles l
      · obtain ⟨l, hl⟩ := hl
        have hz : ∀ {x k : Nat} {b1 : Bool} {d : Loader.D} {n : Cls → Nat}, LdLane L b c x →
            Frame.stateAt (thread p L) X x k = some (some (.inr ⟨.loader b1, d⟩, n)) →
            (d.site = .pre l ∨ d.site = .tiles l) →
            ∃ ns nv, Epilogue.Fits p L x (Loader.toE d) ns nv ∧
              ((Loader.toE d).site = .pre l ∨ (Loader.toE d).site = .tiles l) := by
          intro x k b1 d n hA hσ hl
          have hub0 : n .ub = 0 := by
            by_contra h
            obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
            cases kind <;> simp [cls] at hk
            exact hub ⟨(x, j), pc, _, hf⟩
          obtain ⟨-, hR⟩ := (LdWarp.good hp hX Loader.wOf_or hA.1 hA.2.1 k).2 _ hσ
          obtain ⟨-, hF⟩ := hR hub0
          have h2 : (Loader.toE d).site = .pre l ∨ (Loader.toE d).site = .tiles l := by
            rcases hl with h | h
            · left; show d.site.epi = _; rw [h]; rfl
            · right; show d.site.epi = _; rw [h]; rfl
          have hlc : Loader.lc d.site = if l then .p2 else .p1 := by
            rcases hl with h | h <;> rw [h] <;> rfl
          cases l <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hlc <;>
            simp only [Loader.LFits, hlc] at hF
          · exact ⟨_, _, hF.2, h2⟩
          · exact ⟨_, _, hF.2.1, h2⟩
        obtain ⟨_, _, hF, h1⟩ := hz hA hσ hl
        obtain ⟨_, _, hF', -⟩ := hz hA' hσ' (by rw [← hsite]; exact hl)
        have hb : d.v.sc.bal = d'.v.sc.bal :=
          Epilogue.bal_same (d := Loader.toE d) (d' := Loader.toE d')
            (hA.2.2.trans hA'.2.2.symm) hF hF' h1 (by
              show d'.site.epi = d.site.epi; rw [hsite])
        rw [hb]
      · exact ldSiteShape_eq hl _ _
  exit := by
    intro x y N t a k pc σ hA hA' h1 hσ he
    refine h1.lt_exit (hA'.2.2.trans hA.2.2.symm) ?_
    have hwy := Loader.wb hA'.2.1
    rcases LdWarp.open_ev hp hX (launchFollow hp hX) hwy he (fun f h => by cases h) with
      ⟨s', n, -, -, -, hi, hev⟩ | ⟨b', d, n, hσ1, h0, hR, -, hev⟩
    · exact (start_not_exit hi.2 hev).elim
    · have hb' : b' = b := by
        have := ((LdWarp.good hp hX Loader.wOf_or hA'.1 hA'.2.1 k).2 _ hσ1).1
        cases b' <;> cases b <;> first | rfl | (simp [wOf] at this)
      subst hb'
      exact ld_exit_cls hp hX hub hA'.1 hA'.2.1 hσ1 (ld_exit_at hev rfl)
  entry := by
    intro x k σ a hA hσ hx hr
    obtain ⟨s, rfl⟩ := hr
    obtain ⟨b', d, n, rfl, hd, hw⟩ := tag_site hx
    refine ⟨_, d, n, rfl, fun hE => ?_⟩
    have hE' : d.site = .setmax := hE
    rw [← hd, hE'] at hw
    cases hw
  last := by
    intro x k σ e hA he hσ hb
    have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    have hR := (LdWarp.good hp hX Loader.wOf_or hA.1 hA.2.1 k).2 _ hσ
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · obtain ⟨h1, h2⟩ := start_last hp hX hA.2.1 (by cases b <;> decide) (by cases b <;> decide)
        he hσ hR.1 hb
      refine ⟨h1, fun σ' hσ' => .inl ?_⟩
      obtain ⟨σ', n'⟩ := σ'
      rcases h2 _ hσ' with ⟨s', hs', hj⟩ | ⟨i, hi⟩
      · simp only at hs'
        subst hs'
        simp only [tagOf]
      · simp only at hi
        subst hi
        cases i <;> rfl
    · rename_i b'
      have hev := (LdWarp.lfired hp hX he hσ).1
      obtain ⟨hs, inc, n1, i1, hk⟩ := block_set hev hne hb
      have hsucc : Loader.succ p L x (wOf b') d e =
          some (some (Loader.passStart p L x false d)) := by
        obtain ⟨s, v, kk⟩ := d
        obtain ⟨pc, kd⟩ := e
        simp only at hs hk
        subst hs hk
        rfl
      have hnx : (thread p L x).next (LdWarp.linj p L x b' d n) e =
          some (some (LdWarp.linj p L x b' (Loader.passStart p L x false d)
            (Code.bump (cls L x) n e))) := by
        rw [LdWarp.next_linj, show (Loader.F p L x b').next d e = _ from hsucc]; rfl
      refine ⟨fun hc => ?_, fun σ' hσ' => ?_⟩
      · have h0 := hnx.symm.trans hc
        cases h0
      · obtain rfl := Option.some.inj (Option.some.inj (hnx.symm.trans hσ'))
        by_cases hw : (Loader.passStart p L x false d).site.wcoll = true
        · exact .inr ⟨.site _, by
            show tagS _ = _
            unfold tagS; rw [ite_eq_left hw], ⟨_, rfl⟩, .inl ⟨inc, n1, i1, hk⟩⟩
        · left
          show tagS _ = none
          unfold tagS; rw [ite_eq_right hw]

/-- **The collectives of two lanes of a loader warp.** -/
theorem ld_pair (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hs : SameWarp L g h) {b : Bool} (hw : Prologue.warpIndex L g = wOf b) :
    Sched.WarpPair m (Progress.timed p L) X (CollAt p L) (ldShape p L) g h :=
  warpPair_of_cls hp hX hub (ldCls hp hX hub b (g / L.block)) hs ⟨hs.1.1, hw, rfl⟩
    ⟨hs.1.2.1, hs.2.symm.trans hw, hs.1.2.2.symm⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
