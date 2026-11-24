-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Lemmas.Flow.AllocTmpl
import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The sources of the correction warps' returned values, and the never-dropped theorem

`cshfl_recv` and `cvote_bits` are the output warp's `shfl_recv` and `vote_bits` for a correction
lane: the source lanes of a shuffle or ballot at a role state are lanes of the same warp at the
same instance, which the positions of `Pos.lean` place at the same site. `cexpect` assembles the
reference's expectations; `good` is `Frame.followedOn` for the lanes of correction warp `w`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- The induction hypothesis: the lanes of warp `w` are followed at the positions with at most
`n` collectives before them. -/
abbrev GoodUpTo (p : Params) (L : Launch) (w : Nat) (X : Execution) (n : Nat) : Prop :=
  Proof.GoodUpTo (Ref p L w) X w n

theorem cfits_three {d : D} {ns nv : Nat} (hF : CFits p L g d ns nv) : 3 ≤ ns := by
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  exact Epilogue.fits_three hFE

/-- The output warp's shape of a scan shuffle event. -/
theorem ev_toE {d : Control.D} {e : Event} (hs : (epi d.site).shfl = true) (hev : Control.Ev p L g
    d e) :
    Epilogue.Ev p L g (toE d) e := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [epi, Epilogue.Site.shfl, Bool.false_eq_true] at hs <;> exact hev

/-- **What a lane's shuffle receives**: the value its source lane sends at the same site. -/
theorem cshfl_recv (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {d : Control.D} {pc : Nat}
    {mode : ShflMode} {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (cinj p L g d n)))
    (hF : CFits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L w X (n .shfl + n .vote)) :
    ∃ d' nv', Epilogue.Fits p L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)
        (toE d') (n .shfl) nv' ∧ (toE d').site = (toE d).site ∧
      recv = .bits 32 (Epilogue.opnd L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)
        (toE d')) := by
  have hsite := (ev_class (fired_both hp hX he hσ).1).1 rfl
  have h3 := cfits_three hF
  have hsC := (lane_facts hp hg hw
    (Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c)).2.2.1
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs, -⟩ := shfl_src hp hX hg hw he (counts hσ).1 IH
    (fun h j0 e0 ⟨hh, _⟩ hc he0 hv0 hG hs0 hc0 => by
      simp only [Frame.cnt] at hs0 hc0
      obtain ⟨d0, n0, -, -, hF0, hE0, hs0', hv0'⟩ := role_at hp hX he0 hG (.inr (.inl hv0))
      have := cshfl_lt_vote hp hg hh hc.symm hF hsite hF0 ((ev_class hE0).2.1 hv0) (by omega)
      omega)
    (fun h kx pcx _ hc hx hG hsx hvx => by
      simp only [Frame.cnt] at hsx
      obtain ⟨dx, nx, -, -, hFx, hEx, hsx', -⟩ := role_at hp hX hx hG (.inr (.inr rfl))
      obtain ⟨l, hl⟩ := (ev_class hEx).2.2 rfl
      have := cshfl_lt_exit hc.symm hF hsite hFx hl
      omega)
  simp only [Frame.cnt] at hjs
  obtain ⟨d', n', -, -, hF', hE', hs', -⟩ := role_at hp hX hj hG (.inl ⟨rfl, by omega⟩)
  have hsite' := (ev_class hE').1 rfl
  have hns : n .shfl = n' .shfl := by omega
  rw [← hns] at hF'
  have hsame := cshfl_same hsC.symm hF hsite hF' hsite' rfl
  obtain ⟨rv', -, -, hFE', -⟩ := hF'
  refine ⟨d', _, hFE', by simp only [toE, hsame], ?_⟩
  exact Epilogue.ev_opnd (ev_toE hsite' hE')

/-- The role's first-pass ballot predicate is the output warp's on the launch's CTA index. -/
theorem votePredR_eq (hp : Pre p L m) (hg : g < L.threads) (c : Epilogue.D) (s : Epilogue.Site) :
    votePredR p L g c = Epilogue.votePred p L g { c with site := s } := by
  unfold votePredR Epilogue.votePred
  rw [ctaR_eq hp hg]

/-- **A ballot's bits are the predicates of all lanes at the same ballot.** -/
theorem cvote_bits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {d : Control.D} {pc mask : Nat}
    {a : Bool} {bv : BitVec 32} {l : Bool} (hl : d.site = .vote l)
    (he : X.get (g, k) = some ⟨pc, .vote mask a bv⟩)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (cinj p L g d n)))
    (hF : CFits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L w X (n .shfl + n .vote)) :
    ∀ i < 32, ∃ di nvi, Epilogue.Fits p L (g - laneOf L g + i) (toE di) (n .shfl) nvi ∧
      (toE di).site = (toE d).site ∧
      bv.getLsbD i = Epilogue.votePred p L (g - laneOf L g + i) (toE di) := by
  have hev := (fired_both hp hX he hσ).1
  have hsv : d.site.isVote = true := by rw [hl]; rfl
  have hmask : mask = 2 ^ 32 - 1 := by
    obtain ⟨s, v, kk⟩ := d
    simp only at hl
    subst hl
    simp only [Control.Ev, Control.D.scheduler, Ev] at hev
    obtain ⟨_, h⟩ := hev
    simp only [Kind.vote.injEq] at h
    exact h.1
  subst hmask
  intro i hi
  exact vote_src (P := fun h b => ∃ di nvi, Epilogue.Fits p L h (toE di) (n .shfl) nvi ∧
      (toE di).site = (toE d).site ∧ b = Epilogue.votePred p L h (toE di))
    hp hX hg hw he (counts hσ).2 IH
    (fun h j1 e1 ⟨hh, _⟩ hc he1 hs1 hG hv1 hc1 => by
      simp only [Frame.cnt] at hv1 hc1
      obtain ⟨d1, n1, -, -, hF1, hE1, hs1', hv1'⟩ :=
        role_at hp hX he1 hG (.inl ⟨hs1, by have := cfits_three hF; omega⟩)
      have := cshfl_lt_vote hp hh hg hc hF1 ((ev_class hE1).1 hs1) hF hsv (by omega)
      omega)
    (fun h kx pcx ⟨hh, _⟩ hc hx hG hsx hvx => by
      simp only [Frame.cnt] at hsx hvx
      obtain ⟨dx, nx, -, -, hFx, hEx, -, hvx'⟩ := role_at hp hX hx hG (.inr (.inr rfl))
      obtain ⟨lx, hlx⟩ := (ev_class hEx).2.2 rfl
      exact cvote_exit hp hg hh hc.symm hF hsv hFx hlx (by omega))
    (fun h j ej ⟨hh, _⟩ hc hej hfv hG hsj hcnt => by
      simp only [Frame.cnt] at hsj hcnt
      obtain ⟨di, ni, -, -, hFi, hEi, -, hvi⟩ := role_at hp hX hej hG (.inr (.inl hfv))
      obtain ⟨hsite, hns⟩ := cvote_same hp hg hh hc.symm hF hl hFi ((ev_class hEi).2.1 hfv)
        (by omega)
      rw [hns] at hFi
      obtain ⟨pcj, kj⟩ := ej
      obtain ⟨si, vi, ki⟩ := di
      simp only [Control.D.scheduler] at hsite
      rw [hl] at hsite
      subst hsite
      have hEi' := hEi
      simp only [Control.Ev, Control.D.scheduler, Ev] at hEi'
      obtain ⟨bj, hkj⟩ := hEi'
      subst hkj
      obtain ⟨rvi, -, -, hFEi, -⟩ := hFi
      exact ⟨pcj, _, bj, rfl, _, _, hFEi, by simp only [toE, Control.D.scheduler, hl],
          votePredR_eq hp hh _ _⟩) i hi

/-- The output warp's second pass is the correction warps' second pass. -/
theorem epi_late (s : Site) : (epi s).late = s.late := by
  cases s <;> rfl

/-- **A correction state of the first pass outside the rescale rounds and the final stage is
past at most `7 (batch + 3) + 6` warp collectives** (the output warp's bound: no rescale ballot
precedes it). -/
theorem ccoll_le (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : CFits p L g d ns nv)
    (hr : inRound d.site.pc = false) (ht : tailR d.site = false) (hl : d.site.late = false) :
    ns + nv ≤ 7 * (p.batch + 3) + 6 := by
  obtain ⟨rv, hle, hR, hFE, -⟩ := hF
  rw [rvAt_out hr ht, hl] at hR
  simp only [Bool.false_eq_true, ↓reduceIte] at hR
  subst hR
  have := Epilogue.fits_coll_le hp hFE (by rw [epi_late]; exact hl)
  omega

/-! ### What the events return -/

/-- The Correction lane's expectations from the reference's. -/
theorem expectD_of {d : D} {e : Event} {ns nv : Nat} (hF : CFits p L g d ns nv)
    (hE : CExpect p L g d ns e) (hD : d.site.data = true → ExpectD d e) : ExpectD d e := by
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case word k' =>
    rintro a bs hk; simp only at hk; subst hk
    have hE' := hE rfl
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hR hns⟩
  case down k' =>
    rintro md a b c v' ok hk; simp only at hk; subst hk
    have hE' := hE rfl
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hR hns⟩
  case up k' j =>
    rintro md a b c v' ok hk; simp only at hk; subst hk
    have hE' := hE rfl
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hR hns⟩
  case total k' =>
    rintro md a b c v' ok hk; simp only at hk; subst hk
    have hE' := hE rfl
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hFE
    exact ⟨_, hE' r n0 v0 hP hR hns⟩
  case pre l =>
    rintro md a b c v' ok hk; simp only at hk; subst hk
    have hE' := hE rfl
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨R, n0, v0, hP, hEV, hns, -⟩ := hFE
    exact ⟨_, hE' R n0 v0 hP hEV.1 hns⟩
  case tiles l =>
    rintro md a b c v' ok hk; simp only at hk; subst hk
    have hE' := hE rfl
    simp only [Epilogue.Fits, toE, epi] at hFE
    obtain ⟨R, n0, v0, hP, hEV, -⟩ := hFE
    exact ⟨_, hE' R n0 v0 hP hEV.1⟩
  case q0 | q1 =>
    rintro a bs hk; simp only at hk; subst hk
    exact ⟨_, hE rfl⟩
  case uk =>
    rintro a bs hk; simp only at hk; subst hk
    exact ⟨_, hE⟩
  case rscale | fsum | fmax | rld | fld => exact hD rfl
  all_goals simp only [ExpectD]

/-- **The used-K read returns the chosen request's launch word.** -/
theorem expect_uk (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : D} {ns nv : Nat} {e : Event} (he : X.get (g, k) = some e) (hs : d.site = .uk)
    (hF : CFits p L g d ns nv) (hev : EvR p L g d e) : CExpect p L g d ns e := by
  have hb := Epilogue.batch_lt hp
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  simp only [Epilogue.Fits, toE, hs, epi] at hFE
  obtain ⟨R, bal, hC, -, -⟩ := hFE
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  obtain ⟨pc, kind⟩ := e
  simp only [EvR, hs] at hev
  have hc : chosen d.v.sc = W i := by simpa only [toE] using hi
  rcases hev with ⟨bs, rfl⟩ | ⟨f, rfl⟩
  swap
  · simp [CExpect, hs, Site.sched]
  simp only [CExpect, hs]
  have haddr : (ukAddr p d).toNat = p.usedKBase + 4 * i := by
    rw [ukAddr, hc]
    exact Mma.addrK_toNat hp hroom (by omega)
  rw [haddr] at he
  have hin : ∀ j < 4, ∃ r ∈ p.inputRegions,
      r.Contains ((globalLoc (p.usedKBase + 4 * i)).at j) := by
    intro j hj
    refine ⟨⟨p.usedKBase, 4 * p.batch⟩, by simp [Params.inputRegions], ?_⟩
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    omega
  rw [inputReadValue hp hX (i := (g, k)) ⟨pc, he⟩ rfl hin (hp.usedK i (by omega)),
    show Value.bits 32 (BitVec.ofNat 64 (p.kLength i)) = b32 (p.kLength i) from rfl, rebuild_b32]
  simp only [b32, ukv, hc, r32_W (show i < 2 ^ 32 by omega),
    toNat_W (show i < 2 ^ 64 by omega)]

/-- **What a correction lane's event at a role state returns is what the references say**: the
launch words at the scheduler's reads, the source lanes' values at its collectives, the data
premise at the statistics reads and the Tensor Memory loads. -/
theorem cexpect (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat} {d : Control.D} {n : Cls → Nat}
    {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (cinj p L g d n)))
    (hJ : Correction.Ref p L g (d, rc n)) (hF : CFits p L g d (n .shfl) (n .vote))
    (hne : ∀ f, e.kind ≠ .ub f) (IH : isColl e = true → GoodUpTo p L w X (n .shfl + n .vote)) :
    CExpect p L g d (n .shfl) e ∧ Control.Expect d e := by
  obtain ⟨hev, hevR⟩ := fired_both hp hX he hσ hne
  have hCE : CExpect p L g d (n .shfl) e := by
    by_cases hu : d.site = .uk
    · exact expect_uk hp hX he hu hF hevR
    obtain ⟨rv, hle, hr, hFE, huk⟩ := hF
    obtain ⟨s, v, kk⟩ := d
    obtain ⟨pc, kind⟩ := e
    cases s
    case word k' =>
      simp only [CExpect]; intro _
      exact Epilogue.expect_word hp hReads he rfl hFE hevR
    case q0 =>
      simp only [CExpect]; intro _
      exact Epilogue.expect_q hp hReads he (.inl rfl) hFE hevR
    case q1 =>
      simp only [CExpect]; intro _
      exact Epilogue.expect_q hp hReads he (.inr rfl) hFE hevR
    case down | up | total | pre | tiles =>
      simp only [CExpect]; intro _
      have hevE := ev_toE (by rfl) hev
      have hk : ∃ md a b c r ok, kind = .shfl md a b c r ok := by
        simp only [Control.Ev, Control.D.scheduler, Ev] at hev
        revert hev; simp only [Epilogue.Ev, Site.toE]
        first
          | (rintro ⟨r, ok, h⟩; exact ⟨_, _, _, _, _, _, h⟩)
      obtain ⟨md, a, b, c, r, ok, rfl⟩ := hk
      obtain ⟨d', nv', h1, h2, h3⟩ :=
        cshfl_recv hp hX hg hw he hσ ⟨rv, hle, hr, hFE, huk⟩ (IH rfl)
      exact Epilogue.expect_shfl_of_src hp hg hw hevE ⟨toE d', nv', h1, h2, h3⟩
    case vote l =>
      simp only [CExpect]; intro _
      have hk : ∃ a b, kind = .vote (2 ^ 32 - 1) a b := by
        simp only [Control.Ev, Control.D.scheduler, Ev] at hev; obtain ⟨b, h⟩ := hev; exact ⟨_, _,
            h⟩
      obtain ⟨a, b, rfl⟩ := hk
      have hb := cvote_bits hp hX hg hw rfl he hσ ⟨rv, hle, hr, hFE, huk⟩ (IH isColl_vote)
      exact Epilogue.expect_vote_of_bits hp hg hw (l := l) rfl fun i hi => by
        obtain ⟨di, nvi, h1, h2, h3⟩ := hb i hi
        exact ⟨toE di, nvi, h1, h2, h3⟩
    case uk => exact absurd rfl hu
    case arr j =>
      simp only [CExpect]; intro _
      simp only [Control.D.scheduler, Epilogue.Expect, toE, epi]
    all_goals simp only [Control.D.scheduler, CExpect, Site.sched]; intro h; simp at h
  refine ⟨hCE, ?_⟩
  by_cases hd : d.site.data = true
  · obtain ⟨s,v,k⟩ := d
    cases s <;> first | exact True.intro | cases hd
  · have hx := expectD_of hF hCE (fun h => (hd h).elim)
    obtain ⟨s,v,k⟩ := d
    cases s <;> first | exact hx | exact True.intro

set_option maxHeartbeats 1000000 in
/-- **Every event of a lane of correction warp `w` at a state that holds `Ref` makes a good step**
once no lane of the warp is bad at an earlier collective position. -/
theorem step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (hw8 : 8 ≤ w ∧ w ≤ 11)
    (g k : Nat) (σ : (thread p L g).D) (e : Event)
    (hQ : InWarp L w g) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hR : Ref p L w g σ)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L w) X j) :
    Frame.StepGood (thread p L) (Ref p L w) g σ e := by
  obtain ⟨hg, hw⟩ := hQ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_step hp hX hg hw hw8 he hσ hR hprev
  · exact hR.elim
  · exact hR.elim
  · refine role_step hp hX he hσ hR fun hne => ?_
    obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
    obtain ⟨hcs, hcv⟩ := counts hσ
    refine cexpect hp hX hReads hg hw he hσ hJ hF hne fun hce => ?_
    have := upTo_of_prev (fun _ => ref_init) he hce hprev
    rwa [countColl ((X.tr g).take k), hcs, hcv] at this
  · exact hR.elim
  · exact hR.elim

/-- **Every lane of correction warp `w` is followed, and its states hold the reference
invariant**, given the data-plane premise. -/
theorem good (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw8 : 8 ≤ w ∧ w ≤ 11) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) (k : Nat) : Good p L w X g k :=
  Frame.followedOn (C := thread p L) (J := Ref p L w) (Q := InWarp L w)
    (Frame.inductive_lex (μ X)) (fun _ _ => ref_init)
    (step hp hX (cuQReadsFromLaunch hp hX) hw8) ⟨hg, hw⟩ k

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
