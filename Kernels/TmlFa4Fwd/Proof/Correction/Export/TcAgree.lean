-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcPlace
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Lemmas.Flow.VoteSeq
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' collective `tcgen05` events agree across a warp

Two lanes of a warp have equal rescale ballots (`rb_agree`: a ballot is the instance's predicates),
so the ordinal of an event determines its site (`corr_tc_uniform`) and no lane exits before its
warp's events (`corr_tc_unexited`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp (cinj refV rvN toE rc)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Correction (tw pend resc tcKind finc brv bnb vv)

theorem rvote_tab : ∀ st : Fin 2, vv (.rvote st) = 1 ∧ Progress.Cr.late (.rvote st) = false ∧
    (Site.rvote st).noTile = false := by decide +kernel

private theorem site_facts {s : Correction.Site} (h : s ∈ tcSites) :
    (∀ st, resc s = some st → (0 < pend s ∧ pend s ≤ 25) ∧ finc s = 0) ∧
      (resc s = none → pend s = 0 ∧ 0 ≤ finc s ∧ finc s < 64) := by
  have ht := List.all_eq_true.mp corr_tab s h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨h25, hcase⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := ht
  refine ⟨fun st q => ?_, fun q => ?_⟩
  · rw [q] at hcase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcase
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hcase
    exact ⟨⟨h1, h25⟩, h2⟩
  · rw [q] at hcase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcase
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩ := hcase
    exact ⟨h1, h2, h3⟩

/-- A lane with fewer ballots than another whose last is accepted has fewer accepted ones. -/
private theorem acc_lt {g h i j : Nat}
    (hlt : ((X.tr g).take i).countP isRb < ((X.tr h).take j).countP isRb)
    (hag : ∀ n < ((X.tr g).take i).countP isRb, ordEv X isRb isRv g n = ordEv X isRb isRv h n)
    (hl : ordEv X isRb isRv h (((X.tr h).take j).countP isRb - 1) = true) :
    ((X.tr g).take i).countP isRv + 1 ≤ ((X.tr h).take j).countP isRv := by
  rw [countP_ordinal isRb_of_isRv, countP_ordinal isRb_of_isRv h]
  generalize ((X.tr g).take i).countP isRb = a at *
  obtain ⟨b, hb⟩ : ∃ b, ((X.tr h).take j).countP isRb = b + 1 :=
    ⟨((X.tr h).take j).countP isRb - 1, by omega⟩
  rw [hb] at hl hlt ⊢
  rw [List.range_succ, List.countP_append]
  have e1 : (List.range a).countP (ordEv X isRb isRv g) =
      (List.range a).countP (ordEv X isRb isRv h) :=
    List.countP_congr fun n hn => by rw [hag n (List.mem_range.mp hn)]
  have e2 : (List.range a).countP (ordEv X isRb isRv h) ≤
      (List.range b).countP (ordEv X isRb isRv h) :=
    (List.range_sublist.mpr (by omega)).countP_le
  have e3 : ordEv X isRb isRv h b = true := hl
  simp only [List.countP_singleton, e3, ↓reduceIte]
  omega

private theorem rb_pcs : allSites.all (fun s => !(decide (s.pc = 8009) || decide (s.pc = 8228)) ||
    s.isRvote) = true := by decide +kernel

private theorem rb_site {d : Correction.Control.D} {e : Event} (hpc : e.pc = d.site.pc)
    (h : isRb e = true) : ∃ st, d.site = .rvote st := by
  simp only [isRb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  have h1 := List.all_eq_true.mp rb_pcs d.site (mem_allSites _)
  rw [← hpc] at h1
  have h2 : d.site.isRvote = true := by
    rcases h.1 with h | h <;> simpa [h] using h1
  cases hs : d.site <;> rw [hs] at h2 <;> simp [Site.isRvote] at h2
  exact ⟨_, rfl⟩

private theorem full_vote {d : Correction.Control.D} {pc : Nat} {kd : Kind}
    (hev : Correction.Control.Ev p L g d ⟨pc, kd⟩) (hfv : isFullVote ⟨pc, kd⟩ = true) :
    ∃ a b, kd = .vote (2 ^ 32 - 1) a b := by
  have hs := (CorrWarp.ev_class hev).2.1 hfv
  obtain ⟨site, v, k⟩ := d
  cases site <;> simp [Site.isVote, Site.isRvote, CorrWarp.epi, Epilogue.Site.ballot] at hs
  · obtain ⟨b, h⟩ := hev
    exact ⟨_, b, h⟩
  · obtain ⟨a, b, h⟩ := hev
    exact ⟨a, b, h⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X)
include hp hX hFw hub

/-- **Two lanes of a warp have equal rescale ballots.** -/
theorem rb_agree {h : Nat} (hs : SameWarp L g h) (hw : 8 ≤ Prologue.warpIndex L g)
    (hw1 : Prologue.warpIndex L g ≤ 11) {i j N : Nat} (hi : N < ((X.tr g).take i).countP isRb)
    (hj : N < ((X.tr h).take j).countP isRb) :
    ordEv X isRb isRv g N = ordEv X isRb isRv h N := by
  have hwi : Prologue.warpIndex L g = Prologue.warpIndex L h := hs.2
  have hh := hs.1.2.1
  have hg := hs.1.1
  have hc : g / L.block = h / L.block := hs.1.2.2
  -- a lane's rescale ballot of ordinal `N` is its vote of ordinal `N + 1`
  have get : ∀ {y z : Nat}, 8 ≤ Prologue.warpIndex L y → Prologue.warpIndex L y ≤ 11 →
      y < L.threads → N < ((X.tr y).take z).countP isRb → ∃ q pc a b, X.get (y, q) =
        some ⟨pc, .vote (2 ^ 32 - 1) a b⟩ ∧ (pc = 8009 ∨ pc = 8228) ∧
        ((X.tr y).take q).countP isFullVote = N + 1 ∧
        ordEv X isRb isRv y N = !Arith32.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0 ∧
        ∃ d n, Frame.stateAt (thread p L) X y q = some (some (cinj p L y d n)) ∧
          d.site.isRvote = true ∧ CorrWarp.CFits p L y d (n .shfl) (n .vote) := by
    intro y z hy hy1 hyt hz
    obtain ⟨q, e, -, hq, hqb, hqc⟩ := exists_nthEv (show N + 1 ≤ _ from hz)
    have hne : ∀ f, e.kind ≠ .ub f := fun f hf => by
      obtain ⟨pc, kd⟩ := e
      simp only at hf
      subst hf
      simp [isRb, isBallot] at hqb
    rcases CorrWarp.open_ev hp hX hFw hy hy1 hq hne with ⟨s, n, -, -, -, hi, hev⟩ |
      ⟨d, n, hσ, h0, hR, -, hev, -⟩
    · exfalso
      obtain ⟨pc, kd⟩ := e
      have hx : exit L y s = none := hi.2
      cases kd <;> simp [isRb, isBallot] at hqb
      obtain ⟨site, x1, x2, x3⟩ := s
      cases site
      case enter r => simp [exit] at hx
      case sh j => fin_cases j <;> simp [Startup.Ev] at hev
      all_goals simp [Startup.Ev] at hev
    have hpc : e.pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hq hσ hne
    obtain ⟨-, hF⟩ := hR h0
    have hsite : ∃ st, d.site = .rvote st := rb_site hpc hqb
    obtain ⟨st, hst⟩ := hsite
    have hT : TcC X y q d.site n := by
      rcases corr_tcC hp hX hFw hub hyt hy hy1 q
        (List.getElem?_eq_some_iff.mp hq).1.le _ hσ with ⟨s, n', h, -⟩ | ⟨d', n', h, hT⟩
      · cases h
      · cases h; exact hT
    obtain ⟨v1, v2, v3⟩ := rvote_tab st
    have hv := hT.votes (by rw [hst]; exact v2) (by rw [hst]; exact v3)
    rw [hst, v1, hqc] at hv
    have hvc := (counts hσ).2
    obtain ⟨site, v, kk⟩ := d
    change site = _ at hst
    subst hst
    obtain ⟨pred, b, hk⟩ := hev
    obtain ⟨pc, kd⟩ := e
    change kd = _ at hk
    subst hk
    have hpcv : pc = 8009 ∨ pc = 8228 := by
      change pc = (Site.rvote st).pc at hpc
      rw [hpc]
      fin_cases st
      · exact .inl rfl
      · exact .inr rfl
    refine ⟨q, pc, pred, b, hq, hpcv, by omega, ?_, _, n, hσ, rfl, hF⟩
    rw [← hqc, ordEv_eq hq hqb]
    rcases hpcv with rfl | rfl <;> simp [isRv]
  obtain ⟨q, pc, a, b, hq, -, hqv, ho, d, n, hσ, hsv, hF⟩ := get hw hw1 hg hi
  obtain ⟨q', pc', a', b', hq', -, hqv', ho', d', n', hσ', hsv', hF'⟩ :=
    get (hwi ▸ hw) (hwi ▸ hw1) hh hj
  -- each ballot's bit is its lane's predicate
  have bits : ∀ {y q pc : Nat} {a : Bool} {b : BitVec 32} {d : Control.D} {n : Cls → Nat},
      SameWarp L g y → X.get (y, q) = some ⟨pc, .vote (2 ^ 32 - 1) a b⟩ →
      ((X.tr y).take q).countP isFullVote = N + 1 →
      Frame.stateAt (thread p L) X y q = some (some (cinj p L y d n)) →
      d.site.isRvote = true → CorrWarp.CFits p L y d (n .shfl) (n .vote) →
      ∀ i < 32, ∃ j pc' b', X.get (g - laneOf L g + i, j) =
        some ⟨pc', .vote (2 ^ 32 - 1) (b.getLsbD i) b'⟩ ∧
        ((X.tr (g - laneOf L g + i)).take j).countP isFullVote = N + 1 := by
    intro y q pc a b d n hsy hq hqv hσ hsv hF
    have hyw : Prologue.warpIndex L y = Prologue.warpIndex L g := hsy.2.symm
    have hyt := hsy.1.2.1
    have hisv : d.site.isVote = true := by simp [Site.isVote, hsv]
    have hnv := (counts hσ).2
    have hbase : y - laneOf L y = g - laneOf L g := sameWarp_warpStart hsy
    rw [← hbase]
    exact vote_src (ns := n .shfl) (P := fun z a => ∃ j pc' b', X.get (z, j) =
        some ⟨pc', .vote (2 ^ 32 - 1) a b'⟩ ∧ ((X.tr z).take j).countP isFullVote = N + 1)
      hp hX hyt hyw hq hnv (fun z j hz _ => CorrWarp.good hp hX ⟨hw, hw1⟩ hz.1 hz.2 j)
      (fun z j1 e1 hz hcz he1 hs1 hG hv1 hc1 => by
        simp only [Frame.cnt] at hv1 hc1
        obtain ⟨d1, n1, -, -, hF1, hE1, hs1', hv1'⟩ :=
          CorrWarp.role_at hp hX he1 hG (.inl ⟨hs1, by
            have := CorrWarp.cfits_three hF
            omega⟩)
        have := CorrWarp.cshfl_lt_vote hp hz.1 hyt hcz hF1 ((CorrWarp.ev_class hE1).1 hs1) hF hisv
          (by omega)
        omega)
      (fun z kx pcx hz hcz hx hG hsx hvx => by
        simp only [Frame.cnt] at hsx hvx
        obtain ⟨dx, nx, -, -, hFx, hEx, -, hvx'⟩ := CorrWarp.role_at hp hX hx hG (.inr (.inr rfl))
        obtain ⟨lx, hlx⟩ := (CorrWarp.ev_class hEx).2.2 rfl
        exact CorrWarp.cvote_exit hp hyt hz.1 hcz.symm hF hisv hFx hlx (by omega))
      (fun z j ej hz hcz hej hfv hG hsj hcnt => by
        simp only [Frame.cnt] at hsj hcnt
        obtain ⟨di, ni, -, -, hFi, hEi, -, hvi⟩ := CorrWarp.role_at hp hX hej hG (.inr (.inl hfv))
        obtain ⟨pcj, kj⟩ := ej
        obtain ⟨aj, bj, rfl⟩ := full_vote hEi hfv
        have hq' : ((X.tr z).take j).countP isFullVote = N + 1 := by rw [← hqv]; omega
        exact ⟨pcj, aj, bj, rfl, j, pcj, bj, hej, hq'⟩)
  have hbb : b = b' := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨j1, p1, b1, g1, c1⟩ := bits ⟨⟨hg, hg, rfl⟩, rfl⟩ hq hqv hσ hsv hF i hi
    obtain ⟨j2, p2, b2, g2, c2⟩ := bits hs hq' hqv' hσ' hsv' hF' i hi
    have hj : j1 = j2 := nthEv_unique (p := isFullVote) g1
      (by rw [isFullVote_eq, voteWith_vote]) g2 (by rw [isFullVote_eq, voteWith_vote])
      (c1.trans c2.symm)
    subst hj
    have := g1.symm.trans g2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.vote.injEq] at this
    obtain ⟨-, -, h, -⟩ := this
    exact h
  rw [ho, ho', hbb]

/-- **The correction warps' collective `tcgen05` events agree across a warp.** -/
theorem corr_tc_uniform {e f : EvId} {k pc pc' : Nat} {ke kf : TcKind} (hw : SameWarp L e.1 f.1)
    (h8 : 8 ≤ Prologue.warpIndex L e.1) (h11 : Prologue.warpIndex L e.1 ≤ 11) (hke : X.TcK e k)
    (hkf : X.TcK f k) (he : X.get e = some ⟨pc, .tc ke⟩) (hf : X.get f = some ⟨pc', .tc kf⟩) :
    pc = pc' ∧ tcStatic ke = tcStatic kf := by
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨⟨ev, he', hme⟩, hc⟩ := hke
  obtain ⟨⟨fv, hf', hmf⟩, hc'⟩ := hkf
  obtain rfl := Option.some.inj (he.symm.trans he')
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  have hwi : Prologue.warpIndex L g = Prologue.warpIndex L h := hw.2
  have h8' : 8 ≤ Prologue.warpIndex L h := hwi ▸ h8
  have h11' : Prologue.warpIndex L h ≤ 11 := hwi ▸ h11
  have hwS : SameWarp L h g := ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
  obtain ⟨s, hs, R, hp1, hk1, hT1, hN1, hr1, hf1⟩ :=
    corr_tc_place (g := g) (k := i) hp hX hFw hub h8 h11 he hme
  obtain ⟨s', hs', R', hp2, hk2, hT2, hN2, hr2, hf2⟩ :=
    corr_tc_place (g := h) (k := j) hp hX hFw hub h8' h11' hf hmf
  rw [tileC_cta hp hw.1.1 hw.1.2.1 hw.1.2.2, hT2] at hT1
  simp only [Option.some.injEq] at hT1
  subst hT1
  have hcg : ((X.tr g).take i).countP isTcColl = k := hc
  have hch : ((X.tr h).take j).countP isTcColl = k := hc'
  rw [hcg] at hN1
  rw [hch] at hN2
  have A := fun n hn hn' =>
    rb_agree (g := g) (h := h) hp hX hFw hub hw h8 h11 (i := i) (j := j) (N := n) hn hn'
  have A' := fun n hn hn' =>
    rb_agree (g := h) (h := g) hp hX hFw hub hwS h8' h11' (i := j) (j := i) (N := n) hn hn'
  have key : s = s' := by
    obtain ⟨t1, t1'⟩ := site_facts hs
    obtain ⟨t2, t2'⟩ := site_facts hs'
    have eqv : resc s = resc s' ∧ pend s = pend s' ∧ finc s = finc s' := by
      cases q : resc s with
      | none =>
        obtain ⟨a1, a2⟩ := t1' q
        have b1 := hf1 q
        cases q' : resc s' with
        | none =>
          obtain ⟨a1', a2'⟩ := t2' q'
          have b2 := hf2 q'
          have m1 := countP_le_of_ordinal (X := X) isRb_of_isRv (by rw [b1, b2])
            (fun n hn => A n hn (by rw [b2, ← b1]; exact hn))
          have m2 := countP_le_of_ordinal (X := X) isRb_of_isRv (by rw [b1, b2])
            (fun n hn => A' n hn (by rw [b1, ← b2]; exact hn))
          refine ⟨rfl, ?_, ?_⟩ <;> omega
        | some st' =>
          exfalso
          obtain ⟨c1, c2⟩ := t2 st' q'
          obtain ⟨r, hr, hb, -⟩ := hr2 st' q'
          have hst := st'.isLt
          have m1 := countP_le_of_ordinal (X := X) isRb_of_isRv (by rw [b1, hb]; omega)
            (fun n hn => A' n hn (by rw [b1]; rw [hb] at hn; omega))
          omega
      | some st =>
        obtain ⟨a1, a2⟩ := t1 st q
        obtain ⟨r, hr, hb, ho⟩ := hr1 st q
        have hst := st.isLt
        cases q' : resc s' with
        | none =>
          exfalso
          obtain ⟨c1, c2⟩ := t2' q'
          have b2 := hf2 q'
          have m1 := countP_le_of_ordinal (X := X) isRb_of_isRv (by rw [b2, hb]; omega)
            (fun n hn => A n hn (by rw [b2]; rw [hb] at hn; omega))
          omega
        | some st' =>
          obtain ⟨c1, c2⟩ := t2 st' q'
          obtain ⟨r', hr', hb', ho'⟩ := hr2 st' q'
          have hst' := st'.isLt
          rcases Nat.lt_trichotomy (((X.tr g).take i).countP isRb)
            (((X.tr h).take j).countP isRb) with hlt | heq | hlt
          · exfalso
            have := acc_lt hlt (fun n hn => A n hn (by omega)) ho'
            omega
          · have m1 := countP_le_of_ordinal (X := X) isRb_of_isRv heq.le
              (fun n hn => A n hn (heq ▸ hn))
            have m2 := countP_le_of_ordinal (X := X) isRb_of_isRv heq.ge
              (fun n hn => A' n hn (heq.symm ▸ hn))
            have hss : st = st' := Fin.ext (by omega)
            refine ⟨congrArg some hss, ?_, ?_⟩ <;> omega
          · exfalso
            have := acc_lt hlt (fun n hn => A' n hn (by omega)) ho
            omega
    have h := List.all_eq_true.mp (List.all_eq_true.mp corr_inj s hs) s' hs'
    simpa [eqv.1, eqv.2.1, eqv.2.2] using h
  subst key
  exact ⟨by rw [hp1, hp2], by rw [hk1, hk2, tcKind_warp hp hw]⟩

/-- **A correction lane exits after its warp's collective `tcgen05` events.** -/
theorem corr_tc_unexited {e f : EvId} {k : Nat} (hw : SameWarp L e.1 f.1)
    (h8 : 8 ≤ Prologue.warpIndex L e.1) (h11 : Prologue.warpIndex L e.1 ≤ 11) (hke : X.TcK e k) :
    ¬ X.ExitedShort isTcColl f k := by
  rintro ⟨⟨pcx, hx⟩, hle⟩
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨⟨⟨pc, kd⟩, he, hme⟩, hc⟩ := hke
  obtain ⟨tk, rfl⟩ := isTcColl_kind hme
  have hwi : Prologue.warpIndex L g = Prologue.warpIndex L h := hw.2
  obtain ⟨s, hs, R, -, -, hT1, hN1, hr1, hf1⟩ :=
    corr_tc_place (g := g) (k := i) hp hX hFw hub h8 h11 he hme
  rw [tileC_cta hp hw.1.1 hw.1.2.1 hw.1.2.2] at hT1
  obtain ⟨hN2, hB2⟩ := corr_tc_exit (g := h) (k := j) hp hX hFw hub (hwi ▸ h8) (hwi ▸ h11) hx hT1
  have hsub : ((X.tr h).take j).countP isTcColl ≤ (X.tr h).countP isTcColl :=
    (List.take_sublist _ _).countP_le
  have hcg : ((X.tr g).take i).countP isTcColl = k := hc
  have hlh : (X.tr h).countP isTcColl ≤ k := hle
  obtain ⟨t1, t1'⟩ := site_facts hs
  have hb : ((X.tr g).take i).countP isRb ≤ ((X.tr h).take j).countP isRb := by
    rw [hB2]
    cases q : resc s with
    | none => exact (hf1 q).le
    | some st =>
      obtain ⟨r, hr, hb, -⟩ := hr1 st q
      have := st.isLt
      omega
  have m1 := countP_le_of_ordinal (X := X) isRb_of_isRv hb
    (fun n hn => rb_agree (g := g) (h := h) hp hX hFw hub hw h8 h11 hn (hn.trans_le hb))
  cases q : resc s with
  | none =>
    obtain ⟨a1, a2⟩ := t1' q
    omega
  | some st =>
    obtain ⟨a1, a2⟩ := t1 st q
    omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
