-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemSite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAccSite
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemLoad
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemStore
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' Tensor Memory operations, on their traces

A score load of tile `u` (`soft_ld`) reads 32 columns of its stage's scores, after `u + 1` S-full
polls and `u` P-full arrivals, and is waited for before the lane's next P-full arrival. A P store of
tile `u` (`soft_st`) writes 16 columns of its stage's probabilities; the store `q = 3` of the tile
follows the tile's P-full arrival, the others precede it; every later event of the lane that is not
a `tcgen05` event comes after a `wait::st` of the tile that follows the store. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- No undefined behaviour before a followed state with none counted. -/
theorem no_ub_before {k u pc : Nat} {f : Fault} {σ : (glued p L g).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (σ, n))) (h0 : n .ub = 0) (hu : u < k)
    (he : X.get (g, u) = some ⟨pc, .ub f⟩) : False := by
  have hc := count hσ .ub
  rw [h0, List.countP_eq_zero] at hc
  have hmem : (⟨pc, .ub f⟩ : Event) ∈ (X.tr g).take k := by
    have : ((X.tr g).take k)[u]? = some ⟨pc, .ub f⟩ := by
      rw [List.getElem?_take, ite_eq_left hu]; exact he
    exact List.mem_of_getElem? this
  exact hc _ hmem (by simp [Proof.cls])

/-- The softmax state an event past the startup is fired from. -/
theorem role_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hk : (∃ a vals sh, e.kind = .tc (.ld a vals sh)) ∨
      (∃ a vals sh, e.kind = .tc (.st a vals sh)) ∨ ∃ l tx c r sc, e.kind = .arrive l tx c r sc) :
    ∃ d n c rb rp, Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)) ∧
      n .ub = 0 ∧ RefQ p L g d c rb rp ∧ SmWarp.Linked n c ∧ Ev p L g d e := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    rintro f hf
    rcases hk with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> rw [h] at hf <;> cases hf
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hin, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    have hx : exit L g s = none := hin.2
    obtain ⟨site, x1, x2, x3⟩ := s
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    rcases hk with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> cases site
    case inl.enter | inr.inl.enter | inr.inr.enter => simp [exit] at hx
    case inl.sh j | inr.inl.sh j | inr.inr.sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, -⟩ := hR.2 h0
    exact ⟨d, n, c, rb, rp, hσ, h0, hQ, hLk, hev.1⟩

/-- **A score load of a softmax lane.** -/
theorem soft_ld (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k a : Nat} {vals : List Value}
    {sh : TcShape} (hl : X.TLd (g, k) a vals sh) :
    sh = .s32x32b ∧ vals.length = 32 ∧
      (∃ c : Fin 4, a % 65536 = 128 * (Prologue.warpIndex L g / 4) + 32 * c.val) ∧
      Tm.pArr L X g (Prologue.warpIndex L g / 4) k + 1 =
        Tm.sPolls L X g (Prologue.warpIndex L g / 4) k ∧
      Tm.stN X g k + 4 = 4 * Tm.sPolls L X g (Prologue.warpIndex L g / 4) k ∧
      ∀ e pc tx cnt rel sc, k < e → X.get (g, e) =
          some ⟨pc, .arrive (Tm.pFull L (g / L.block) (Prologue.warpIndex L g / 4)) tx cnt rel sc⟩ →
        ∃ w pc', k < w ∧ w < e ∧ X.get (g, w) = some ⟨pc', .tc .waitLd⟩ := by
  obtain ⟨pc, he⟩ := hl
  obtain ⟨d, n, cc, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inl ⟨_, _, _, rfl⟩)
  have hs : ∃ r c, d.site = .sld r c := by
    rcases soft_ld_site hev with h | ⟨c, hs, hk1⟩
    · exact h
    · exact absurd (hQ.wait c hs) hk1
  obtain ⟨r, c, hs⟩ := hs
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨site, v, kk, acc⟩ := d
  change site = _ at hs
  subst hs
  obtain ⟨rfl, hcol, hlen⟩ := sld_col hat hc hf rfl
  obtain ⟨t1, t2, t3⟩ := tm_counts hw hσ
  obtain ⟨c1, c2⟩ := (site_counts hQ).1 r c rfl
  rw [hLk _ rfl, hLk _ rfl] at c1 c2
  refine ⟨rfl, hlen, ⟨c, by rw [hcol, colS_eq hw]; rfl⟩, by rw [t1, t2]; exact c1,
    by rw [t1, t3]; exact c2, ?_⟩
  intro e pc' tx cnt rel sc hke hae
  obtain ⟨d', n', c', rb', rp', hσ', h0', -, -, hev'⟩ :=
    role_state hp hX hFw hw hae (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
  have hel : e ≤ (X.tr g).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[e]? = _ from hae)).1.le
  rcases soft_ld_pend hp hX hσ e hke hel _ hσ' with
    ⟨w, h1, h2, pcw, h3⟩ | ⟨u, -, h2, pcu, f, h3⟩ | ⟨d2, n2, h2, hp2⟩
  · exact ⟨w, pcw, h1, h2, h3⟩
  · exact (no_ub_before hσ' h0' h2 h3).elim
  · exfalso
    simp only [SmWarp.sinj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at h2
    obtain ⟨rfl, -⟩ := h2
    obtain ⟨site', v', kk', acc'⟩ := d'
    have hne : (Tm.pFull L (g / L.block) (Prologue.warpIndex L g / 4)) ≠ bl L g 336 := by
      rw [bl_eq hw 336]
      intro h
      simp only [Tm.pFull, Tm.bar, Loc.mk.injEq] at h
      omega
    rcases hp2 with hm | ⟨hs, hk, -⟩ | ⟨c, hs, hk, -⟩
    · cases r <;> simp only [ldSites, List.mem_append, List.mem_map, List.mem_finRange, true_and,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      · rcases hm with (((⟨c, rfl⟩ | rfl) | ⟨c, rfl⟩) | rfl | rfl | rfl | rfl) <;>
          simp [Control.D.scheduler, Ev, rdOrUb, tcLdOrUb, arrOff] at hev'
        exact hne hev'.1
      · rcases hm with (((⟨c, rfl⟩ | rfl) | ⟨c, rfl⟩) | rfl | rfl | rfl | rfl | rfl) <;>
          simp [Control.D.scheduler, Ev, rdOrUb, tcLdOrUb, arrOff] at hev'
        exact hne hev'.1
    · simp only at hs hk
      subst hs hk
      simp only [Control.D.scheduler, Ev] at hev'
      split_ifs at hev'; simp at hev'
    · simp only at hs hk
      subst hs hk
      simp [Control.D.scheduler, Ev] at hev'

/-- **A P store of a softmax lane.** -/
theorem soft_st (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k a : Nat} {vals : List Value}
    {sh : TcShape} (hl : X.TSt (g, k) a vals sh) :
    sh = .s32x32b ∧ vals.length = 16 ∧ ∃ q : Fin 4,
      a % 65536 = 128 * (Prologue.warpIndex L g / 4) + 64 + 16 * q.val ∧
      1 ≤ Tm.sPolls L X g (Prologue.warpIndex L g / 4) k ∧
      Tm.pArr L X g (Prologue.warpIndex L g / 4) k + (if q.val < 3 then 1 else 0) =
        Tm.sPolls L X g (Prologue.warpIndex L g / 4) k ∧
      Tm.stN X g k + 4 = 4 * Tm.sPolls L X g (Prologue.warpIndex L g / 4) k + q.val := by
  obtain ⟨pc, he⟩ := hl
  obtain ⟨d, n, cc, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inr (.inl ⟨_, _, _, rfl⟩))
  obtain ⟨r, q, hs⟩ := soft_st_site hev
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨site, v, kk, acc⟩ := d
  change site = _ at hs
  subst hs
  obtain ⟨rfl, hcol, hlen⟩ := pst_col (p := p) (L := L) (g := g) (r := r) (q := q)
    (v := v.scheduler) (k := kk) (acc := acc) hat hc hf rfl
  obtain ⟨t1, t2, t3⟩ := tm_counts hw hσ
  obtain ⟨c1, c2⟩ := (site_counts hQ).2 r q rfl
  rw [hLk _ rfl, hLk _ rfl] at c1 c2
  refine ⟨rfl, hlen, q, ?_, by rw [t1]; omega, by rw [t1, t2]; exact c1, by rw [t1, t3]; exact c2⟩
  have e1 := colS_eq (L := L) (g := g) hw
  rw [hcol, e1]
  show _ = 128 * (g % L.block / 32 / 4) + 64 + 16 * q.val
  omega

/-- **A P store is waited for in its tile** before every later event of its lane that is not a
`tcgen05` event. -/
theorem soft_st_wait (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k a : Nat} {vals : List Value}
    {sh : TcShape} (hl : X.TSt (g, k) a vals sh) {e : Nat} (hne : Tm.NonTcAfter X g k e) :
    ∃ w pc, k < w ∧ w < e ∧ X.get (g, w) = some ⟨pc, .tc .waitSt⟩ ∧
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) w =
        Tm.sPolls L X g (Prologue.warpIndex L g / 4) k := by
  obtain ⟨pc, he⟩ := hl
  obtain ⟨d, n, cc, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inr (.inl ⟨_, _, _, rfl⟩))
  obtain ⟨r, q, hs⟩ := soft_st_site hev
  obtain ⟨site, v, kk, acc⟩ := d
  change site = _ at hs
  subst hs
  obtain ⟨hke, ev, hget, htc, hub⟩ := hne
  -- every later event up to `e` before which the lane has not waited is a `tcgen05` event
  have key : ∀ i ev', k ≤ i → i ≤ e → X.get (g, i) = some ev' →
      (∀ w, k < w → w < i → ∀ pc, X.get (g, w) ≠ some ⟨pc, .tc .waitSt⟩) →
      (∀ u, u < i → ∀ pc f, X.get (g, u) ≠ some ⟨pc, .ub f⟩) → (∀ f, ev'.kind ≠ .ub f) →
      ∃ tk, ev'.kind = .tc tk := by
    intro i ev' hki hie hi hnw hnu hub'
    rcases Nat.eq_or_lt_of_le hki with rfl | hlt
    · rw [he] at hi; cases hi; exact ⟨_, rfl⟩
    have hil : i ≤ (X.tr g).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr g)[i]? = _ from hi)).1.le
    rcases SmWarp.open_ev hp hX hFw hw hi hub' with ⟨s, n', hσ', -⟩ | ⟨d, n', hσ', -, -, -, hev'⟩
    · rcases soft_st_pend hp hX hσ i hlt hil _ hσ' with
        ⟨w, h1, h2, pcw, h3⟩ | ⟨u, -, h2, pcu, f, h3⟩ | ⟨d2, n2, h2, -⟩
      · exact absurd h3 (hnw w h1 h2 pcw)
      · exact absurd h3 (hnu u h2 pcu f)
      · simp [SmWarp.sinj] at h2
    · rcases soft_st_pend hp hX hσ i hlt hil _ hσ' with
        ⟨w, h1, h2, pcw, h3⟩ | ⟨u, -, h2, pcu, f, h3⟩ | ⟨d2, n2, h2, hp2⟩
      · exact absurd h3 (hnw w h1 h2 pcw)
      · exact absurd h3 (hnu u h2 pcu f)
      · simp only [SmWarp.sinj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
          true_and] at h2
        obtain ⟨rfl, -⟩ := h2
        obtain ⟨site', v', kk', acc'⟩ := d
        obtain ⟨hev1, -⟩ := hev'
        cases site' <;> simp only [PstPend, Bool.false_eq_true] at hp2
        · simp only [Control.D.scheduler, Ev] at hev1
          have whenDelayed (b : Bool)
              (h : if b then ev'.kind = .tc .waitLd else
                (∃ a vals sh, ev'.kind = .tc (.st a vals sh)) ∨ ∃ f, ev'.kind = .ub f) :
              ∃ tk, ev'.kind = .tc tk := by
            cases b
            · rcases h with ⟨_,_,_,hk⟩ | ⟨f,hk⟩
              · exact ⟨_,hk⟩
              · exact absurd hk (hub' f)
            · exact ⟨_,h⟩
          exact whenDelayed _ hev1
        · simp only [Control.D.scheduler, Ev] at hev1
          rcases hev1 with h | ⟨f, h⟩
          · exact ⟨_, h⟩
          · exact absurd h (hub' f)
  have hel : e ≤ (X.tr g).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[e]? = _ from hget)).1.le
  have hnub : ∀ u, u < e → ∀ pc f, X.get (g, u) ≠ some ⟨pc, .ub f⟩ := by
    intro u hu pc f h
    rcases SmWarp.open_ev hp hX hFw hw hget hub with ⟨s, n', hσ', h0', -⟩ | ⟨d, n', hσ', h0', -⟩
    · exact no_ub_before hσ' h0' hu h
    · exact no_ub_before hσ' h0' hu h
  have hex : ∃ w, k < w ∧ w < e ∧ ∃ pc, X.get (g, w) = some ⟨pc, .tc .waitSt⟩ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨tk, h⟩ := key e ev hke.le le_rfl hget (fun w h1 h2 pc h => hcon w h1 h2 pc h) hnub hub
    exact htc tk h
  classical
  obtain ⟨h1, h2, pcw, h3⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, pcw, h1, h2, h3, ?_⟩
  unfold Tm.sPolls okPolls
  refine Tm.countP_take_eq h1.le (by omega) fun i ev' hki hiw hi => ?_
  obtain ⟨tk, htk⟩ := key i ev' hki (by omega) hi
    (fun w hw1 hw2 pc h => Nat.find_min hex (show w < Nat.find hex by omega)
      ⟨hw1, by omega, pc, h⟩) (fun u hu => hnub u (by omega)) fun f hf => by
      obtain ⟨pc', kd⟩ := ev'
      simp only at hf
      subst hf
      exact hnub i (by omega) pc' f hi
  obtain ⟨pc', kd⟩ := ev'
  simp only at htk
  subst htk
  rfl

/-- **A P-full arrival of a softmax lane** follows one S-full poll more than its earlier
arrivals. -/
theorem soft_p (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) {k pc tx cnt : Nat} {rel : Bool}
    {sc : MbarScope} (he : X.get (g, k) = some ⟨pc,
      .arrive (Tm.pFull L (g / L.block) (Prologue.warpIndex L g / 4)) tx cnt rel sc⟩) :
    Tm.pArr L X g (Prologue.warpIndex L g / 4) k + 1 =
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) k := by
  obtain ⟨d, n, c, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
  have hs : ∃ r, d.site = .parr r := by
    obtain ⟨st, v, kk, acc⟩ := d
    have hne : ∀ o, o = 112 ∨ o = 336 →
        Tm.pFull L (g / L.block) (Prologue.warpIndex L g / 4) ≠ bl L g o := by
      intro o ho h
      rw [bl_eq hw o] at h
      simp only [Tm.pFull, Tm.bar, Loc.mk.injEq] at h
      omega
    cases st
    case parr r => exact ⟨r, rfl⟩
    case parr2 r =>
      simp only [Ev, arrOff, Kind.arrive.injEq] at hev
      exact absurd hev.1 (hne 112 (.inl rfl))
    case barr b =>
      simp only [Ev, arrOff, Kind.arrive.injEq] at hev
      exact absurd hev.1 (hne 336 (.inr rfl))
    all_goals exfalso
    all_goals simp only [Control.D.scheduler, Ev] at hev
    all_goals try simp only [Epilogue.Ev, Site.toE] at hev
    all_goals (try split at hev)
    all_goals shape_destruct hev
    all_goals (try subst_vars)
    all_goals simp_all [rdOrUb, tcLdOrUb]
  obtain ⟨r, hs⟩ := hs
  obtain ⟨t1, t2, -⟩ := tm_counts hw hσ
  have h := parr_counts hQ hs
  rw [hLk _ rfl, hLk _ rfl] at h
  rw [t1, t2]
  exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
