-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
public import Lemmas.Flow.OrdinalCount
public import Lemmas.Flow.VoteSeq
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.RefEv
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane's warp-collective `tcgen05` events and rescale ballots

A rescale stage of a round makes a ballot, and its 25 warp-collective `tcgen05` events when a row of
the warp needs rescaling, none otherwise; the final stage loads with two events a chunk. So the
warp-collective `tcgen05` events before a state are 25 for each nonzero rescale ballot, less those
the current stage has still to make, and the final stage's (`TcC.tc`); the rescale ballots are the
places' (`TcC.ballots`), and the warp's vote count at one is its ordinal after the scheduler's
(`TcC.votes`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites nexts)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- A rescale ballot. -/
def isRb (e : Event) : Bool :=
  (decide (e.pc = 8009) || decide (e.pc = 8228)) && isBallot e

/-- A nonzero rescale ballot. -/
def isRv (e : Event) : Bool :=
  (decide (e.pc = 8009) || decide (e.pc = 8228)) && match e.kind with
    | .vote _ _ b => !Arith32.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0
    | _ => false

theorem isRb_of_isRv (e : Event) (h : isRv e = true) : isRb e = true := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp_all [isRv, isRb, isBallot]

/-- The warp-collective `tcgen05` events at a site. -/
def Correction.tw : Correction.Site → Nat
  | .rld _ _ | .rldw _ _ | .rst _ _ | .rwait _ | .fld _ _ | .fwl _ _ => 1
  | _ => 0

/-- The events a rescale stage with a nonzero ballot has still to make. -/
def Correction.pend : Correction.Site → Nat
  | .rld _ c => 25 - 3 * c.val
  | .rldw _ c => 24 - 3 * c.val
  | .rst _ c => 23 - 3 * c.val
  | .rwait _ => 1
  | _ => 0

/-- The points of the final stage's events. -/
def Correction.finPts : List Nat :=
  (List.finRange 2).flatMap fun st => (List.finRange 16).flatMap fun j =>
    [(Correction.Site.fld st j).pc, (Correction.Site.fwl st j).pc]

/-- The points of the rescale ballots. -/
def Correction.rvPts : List Nat := [8009, 8228]

open Correction (tw pend finPts rvPts)

/-- A site's value of the relation. -/
def Correction.finc (s : Correction.Site) : Int := (finPts.countP (before s) : Int)
/-- A site's value of the relation. -/
def Correction.brv (s : Correction.Site) : Int := (rvPts.countP (before s) : Int)
/-- A site's value of the relation. -/
def Correction.bnb (s : Correction.Site) : Int := ((ptsOf (.nb 0)).countP (before s) : Int)

/-- The scheduler's ballot before a site of the first pass, the rounds and the final stage. -/
def Correction.vv (s : Correction.Site) : Int :=
  if s.pc < 7880 then 0 else 1

open Correction (finc brv bnb vv)

private def dnb : Correction.Site → Int
  | .nb 0 | .rbar 0 | .fbar 0 => 1
  | _ => 0
private def dB : Correction.Site → Int
  | .rvote _ => 1
  | _ => 0
private def dU : Correction.Site → Int
  | .rvote _ | .vote _ => 1
  | _ => 0
private def dV : Correction.Site → Correction.Site → Int
  | .rvote _, .rld _ _ => 1
  | _, _ => 0

private def moveOk (s s' : Correction.Site) : Bool :=
  decide ((pend s' : Int) + tw s = pend s + 25 * dV s s' + finc s' - finc s) &&
  decide (brv s' + 2 * (bnb s + dnb s - bnb s') = brv s + dB s) &&
  (s'.noTile || Progress.Cr.late s' || (!s.noTile && !Progress.Cr.late s &&
    decide (dU s = dB s + vv s' - vv s))) &&
  (decide (pend s' = 0) || (match s, s' with
    | .rvote _, .rld _ _ => true
    | _, _ => decide (0 < pend s) && decide (dB s = 0)))

private theorem moves : allSites.all (fun s => (nexts s).all (moveOk s)) = true := by
  decide +kernel

/-- What a correction state says of the trace before it. -/
structure TcC (X : Execution) (g k : Nat) (s : Correction.Site) (n : Cls → Nat) : Prop where
  tc : (((X.tr g).take k).countP isTcColl : Int) + pend s =
    25 * ((X.tr g).take k).countP isRv + finc s
  ballots : (((X.tr g).take k).countP isRb : Int) =
    brv s + 2 * ((n (.corr (.nb 0)) : Int) - bnb s)
  votes : Progress.Cr.late s = false → s.noTile = false →
    (n .vote : Int) = ((X.tr g).take k).countP isRb + vv s
  taken : 0 < pend s → 0 < ((X.tr g).take k).countP isRb ∧
    ordEv X isRb isRv g (((X.tr g).take k).countP isRb - 1) = true

private theorem rb_pc : allSites.all (fun s => !(decide (s.pc = 8009) || decide (s.pc = 8228)) ||
    decide (s = .rvote 0) || decide (s = .rvote 1)) = true := by decide +kernel

private theorem rv_pc : ∀ st, (Correction.Site.rvote st).pc = 8009 ∨
    (Correction.Site.rvote st).pc = 8228 := by decide

set_option maxHeartbeats 2000000 in
/-- The classes of an event, by its site. -/
private theorem ev_cls {d : Correction.D} (hev : Correction.Ev p L g d e)
    (hne : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = d.site.pc) :
    isTcColl e = decide (0 < tw d.site) ∧ isRb e = decide (0 < dB d.site) ∧
      isFullVote e = decide (0 < dU d.site) := by
  have hrb : isRb e = true → ∃ st, d.site = .rvote st := by
    intro h
    simp only [isRb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    have h1 := List.all_eq_true.mp rb_pc d.site (mem_allSites _)
    rw [← hpc] at h1
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq,
      decide_eq_false_iff_not] at h1
    rcases h1 with (⟨h2, h3⟩ | h1) | h1
    · rcases h.1 with h | h
      · exact absurd h h2
      · exact absurd h h3
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  have hrb' : (∀ st, d.site ≠ .rvote st) → isRb e = false := fun h => by
    rw [Bool.eq_false_iff]
    intro h'
    obtain ⟨st, hs⟩ := hrb h'
    exact h st hs
  have hd : (∀ st, d.site ≠ .rvote st) → decide (0 < dB d.site) = false := fun h => by
    cases hs : d.site <;> first | rfl | (exact absurd hs (h _))
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hne hpc
  cases s
  case rvote st =>
    simp only [Correction.Ev] at hev
    obtain ⟨b, rfl⟩ := hev
    refine ⟨rfl, ?_, ?_⟩
    · have := rv_pc st
      rw [← hpc] at this
      simp [isRb, isBallot, dB, this]
    · rw [isFullVote_eq, voteWith_vote]; rfl
  case vote l =>
    simp only [Correction.Ev] at hev
    obtain ⟨b, rfl⟩ := hev
    refine ⟨rfl, (hrb' (by simp)).trans (hd (by simp)).symm, ?_⟩
    rw [isFullVote_eq, voteWith_vote]; rfl
  all_goals
    refine ⟨?_, (hrb' (by simp)).trans (hd (by simp)).symm, ?_⟩
  all_goals clear hrb hrb' hd
  all_goals simp only [Correction.Ev, Correction.rdOrUb, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals first
    | exact absurd rfl (hne _)
    | rfl

theorem corr_take_snoc {f : Event → Bool} (he : X.get (g, k) = some e) :
    ((X.tr g).take (k + 1)).countP f = ((X.tr g).take k).countP f + if f e then 1 else 0 := by
  rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some,
    List.countP_append, List.countP_singleton]

private theorem moveOk_at {s s' : Correction.Site} (h : s' ∈ nexts s) : moveOk s s' = true :=
  List.all_eq_true.mp (List.all_eq_true.mp moves s (mem_allSites s)) s' h

/-- An event of no class keeps the relation at a state of the same site. -/
private theorem tcC_same {d d' : Correction.Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hT : TcC X g k d.site n) (hs : d'.site = d.site) (h1 : isTcColl e = false)
    (h2 : isRb e = false)
    (h3 : isFullVote e = false) (h4 : cls L g (.corr (.nb 0)) e = false) :
    TcC X g (k + 1) d'.site (Code.bump (cls L g) n e) := by
  have h5 : isRv e = false := by
    rw [Bool.eq_false_iff]; exact fun h => by rw [isRb_of_isRv e h] at h2; cases h2
  have hv : Code.bump (cls L g) n e .vote = n .vote := by
    simp [Code.bump, cls, h3]
  have hn : Code.bump (cls L g) n e (.corr (.nb 0)) = n (.corr (.nb 0)) := by
    simp [Code.bump, h4]
  obtain ⟨t1, t2, t3, t4⟩ := hT
  constructor
  · simpa [corr_take_snoc he, h1, h5, hs] using t1
  · simpa [corr_take_snoc he, h2, hn, hs] using t2
  · intro a b
    rw [hs] at a b
    simpa [corr_take_snoc he, h2, hv, hs] using t3 a b
  · intro a
    rw [hs] at a
    simpa [corr_take_snoc he, h2] using t4 a

private theorem ballot_cls {st : Fin 2} {pc : Nat} {pred : Bool} {b : BitVec 32}
    (hpc : pc = (Correction.Site.rvote st).pc) :
    isTcColl ⟨pc, .vote (2 ^ 32 - 1) pred b⟩ = false ∧
      isRb ⟨pc, .vote (2 ^ 32 - 1) pred b⟩ = true ∧
      isFullVote ⟨pc, .vote (2 ^ 32 - 1) pred b⟩ = true ∧
      isRv ⟨pc, .vote (2 ^ 32 - 1) pred b⟩ =
        !Arith32.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0 := by
  have h := rv_pc st
  rw [← hpc] at h
  refine ⟨rfl, by simp [isRb, isBallot, h], by rw [isFullVote_eq, voteWith_vote], ?_⟩
  simp only [isRv, Bool.and_eq_right_iff_imp, Bool.or_eq_true, decide_eq_true_eq]
  exact fun _ => h

/-- A payload site is no poll, and its event no wait. -/
private theorem pay_site {d : Correction.Control.D} {ev : Event}
    (hev : Correction.Ev p L g d.scheduler ev) (hp : Correction.Control.payloadSite d.site) :
    d.site.isPoll = false ∧ ∀ m par a sc, ev.kind ≠ .wait m par false a sc := by
  obtain ⟨site, v, kk⟩ := d
  rcases hp with ⟨st, h | h | h | h⟩ | ⟨st, c, h⟩ | ⟨st, j, h⟩ <;>
    (change site = _ at h
     subst h
     refine ⟨rfl, fun m par a sc hk => ?_⟩
     simp [Correction.Control.D.scheduler, Correction.Ev, Correction.rdOrUb, hk] at hev)

/-- A control step moves as the place table says, or stays with no event of a class. -/
theorem corr_ctl_step {d d' : Correction.Control.D} {n : Correction.Cnt → Nat}
    (hJ : Correction.Control.Ref p L g (d, n)) (hev : Correction.Control.Ev p L g d e)
    (hne : ∀ f, e.kind ≠ .ub f) (hs : Correction.Control.succ p L g d e = some (some d')) :
    (d'.site = d.site ∧ ((∃ m par a sc, e.kind = .wait m par false a sc) ∨
        d.site.isFst = true)) ∨
      (d'.site ∈ nexts d.site ∧ (d.site.isPoll = true →
        ∀ m par a sc, e.kind ≠ .wait m par false a sc)) := by
  obtain ⟨a, ev, hev', -, hsa, hsite, -, -, -, hor⟩ :=
    Correction.Control.represents hJ hev hne hs
  rw [← hsite]
  rcases Correction.succ_cases hsa with ⟨rfl, _, _, _, _, hk⟩ | ⟨hf, -, rfl⟩ | hM
  · refine .inl ⟨rfl, .inl ?_⟩
    rcases hor with rfl | ⟨hp, -⟩
    · exact ⟨_, _, _, _, hk⟩
    · exact absurd hk ((pay_site hev' hp).2 _ _ _ _)
  · exact .inl ⟨rfl, .inr hf⟩
  · obtain ⟨h1, -, -, h2, -⟩ := hM
    refine .inr ⟨h1, fun hpoll => ?_⟩
    rcases hor with rfl | ⟨hp, -⟩
    · exact h2 hpoll
    · rw [(pay_site hev' hp).1] at hpoll
      cases hpoll

/-- A role step keeps the relation. -/
theorem tcC_step {d d' : Correction.Control.D} {n : Cls → Nat}
    (hJ : Correction.Control.Ref p L g (d, CorrWarp.rc n))
    (he : X.get (g, k) = some e) (hev : Correction.Control.Ev p L g d e)
    (hne : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = d.site.pc)
    (hs : Correction.Control.succ p L g d e = some (some d'))
    (hT : TcC X g k d.site n) : TcC X g (k + 1) d'.site (Code.bump (cls L g) n e) := by
  have hcls : (isTcColl e = decide (0 < tw d.site) ∧ isRb e = decide (0 < dB d.site) ∧
      isFullVote e = decide (0 < dU d.site)) ∧
      ((d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc) →
        Correction.cls L g (.nb 0) e = decide (Correction.sig d.site = some (.nb 0))) := by
    by_cases hr : ∃ st, d.site = .rvote st
    · obtain ⟨st, hr⟩ := hr
      obtain ⟨site, v, kk⟩ := d
      change site = _ at hr
      subst hr
      obtain ⟨pred, b, hk⟩ := hev
      obtain ⟨pc, kd⟩ := e
      change kd = _ at hk
      subst hk
      obtain ⟨b1, b2, b3, -⟩ := ballot_cls (pred := pred) (b := b) hpc
      exact ⟨⟨b1, b2, b3⟩, fun _ => rfl⟩
    · have hd : Correction.Ev p L g d.scheduler e := by
        obtain ⟨site, v, kk⟩ := d
        cases site <;> first | exact hev | exact absurd ⟨_, rfl⟩ hr
      exact ⟨ev_cls hd hne hpc, fun hpoll => Correction.ev_cls hd hne hpoll (.nb 0)⟩
  obtain ⟨⟨c1, c2, c3⟩, hcn⟩ := hcls
  rcases corr_ctl_step hJ hev hne hs with ⟨hsame, hw | hf⟩ | ⟨hM, hpoll⟩
  · obtain ⟨_, _, _, _, hk⟩ := hw
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    exact tcC_same he hT hsame rfl (by simp [isRb, isBallot]) rfl (by simp [cls, Correction.cls])
  · have hp0 : tw d.site = 0 ∧ dB d.site = 0 ∧ dU d.site = 0 ∧
        Correction.sig d.site = some .st ∧ d.site.isPoll = false := by
      revert hf
      cases d.site <;> simp [Correction.Site.isFst, tw, dB, dU, Correction.sig,
        Correction.Site.isPoll]
    obtain ⟨p1, p2, p3, p4, p5⟩ := hp0
    refine tcC_same he hT hsame (by rw [c1, p1]; rfl) (by rw [c2, p2]; rfl)
      (by rw [c3, p3]; rfl) ?_
    have := hcn (fun h => by rw [p5] at h; cases h)
    rw [p4] at this
    exact this
  have hc := hcn hpoll
  have hnb : cls L g (.corr (.nb 0)) e = decide (0 < dnb d.site) := by
    refine hc.trans ?_
    have h0 : ∀ q : Fin 2, q = 0 ∨ q = 1 := by decide
    cases hsd : d.site with
    | nb q | rbar q | fbar q => rcases h0 q with rfl | rfl <;> rfl
    | arr q | farr q => rcases h0 q with rfl | rfl <;> rfl
    | rarr q r | fdone q r | fw q r =>
      rcases h0 q with rfl | rfl <;> rcases h0 r with rfl | rfl <;> rfl
    | _ => rfl
  have hmv := moveOk_at hM
  simp only [moveOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hmv
  obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hmv
  have hV : (if isRv e then 1 else 0 : Int) = dV d.site d'.site := by
    by_cases hr : ∃ st, d.site = .rvote st
    · obtain ⟨st, hr⟩ := hr
      obtain ⟨site, v, kk⟩ := d
      change site = _ at hr
      subst hr
      obtain ⟨pred, b, hb⟩ := hev
      obtain ⟨pc, kd⟩ := e
      change kd = _ at hb
      subst hb
      obtain ⟨-, -, -, h1⟩ := ballot_cls (pred := pred) (b := b) hpc
      simp only [Correction.Control.succ, Correction.succ, Correction.Control.D.scheduler,
        Option.map_some, Option.some.injEq, Correction.afterVote, Correction.D.ite] at hs
      rw [h1]
      subst hs
      clear m1 m2 m3 m4 hM hnb hc c1 c2 c3 h1 hcn hpoll
      generalize Arith32.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0 = z
      cases z <;> rfl
    · have h0 : dB d.site = 0 := by
        cases hsd : d.site <;> first | rfl | exact absurd ⟨_, hsd⟩ hr
      have h1 : isRb e = false := by rw [c2, h0]; rfl
      have h2 : isRv e = false := by
        rw [Bool.eq_false_iff]; exact fun h => by rw [isRb_of_isRv e h] at h1; cases h1
      rw [h2]
      cases hsd : d.site <;> first | rfl | exact absurd ⟨_, hsd⟩ hr
  have hB : (if isRb e then 1 else 0 : Int) = dB d.site := by
    rw [c2]; cases d.site <;> rfl
  have hU : (if isFullVote e then 1 else 0 : Int) = dU d.site := by
    rw [c3]; cases d.site <;> rfl
  have hW : (if isTcColl e then 1 else 0 : Int) = tw d.site := by
    rw [c1]; cases d.site <;> rfl
  have hN : (if cls L g (.corr (.nb 0)) e then 1 else 0 : Int) = dnb d.site := by
    rw [hnb]
    have h0 : ∀ q : Fin 2, q = 0 ∨ q = 1 := by decide
    cases d.site with
    | nb q | rbar q | fbar q => rcases h0 q with rfl | rfl <;> rfl
    | _ => rfl
  have hnI : ((Code.bump (cls L g) n e (.corr (.nb 0)) : Nat) : Int) =
      n (.corr (.nb 0)) + dnb d.site := by
    rw [← hN]
    show ((n (.corr (.nb 0)) + if cls L g (.corr (.nb 0)) e then 1 else 0 : Nat) : Int) = _
    push_cast; rfl
  have hvI : ((Code.bump (cls L g) n e .vote : Nat) : Int) = n .vote + dU d.site := by
    rw [← hU]
    show ((n .vote + if isFullVote e then 1 else 0 : Nat) : Int) = _
    push_cast; rfl
  obtain ⟨t1, t2, t3, t4⟩ := hT
  constructor
  · rw [corr_take_snoc he, corr_take_snoc he]
    push_cast
    rw [hW, hV]
    omega
  · rw [corr_take_snoc he, hnI]
    push_cast
    rw [hB]
    omega
  · intro a b
    rcases m3 with (m3 | m3) | ⟨⟨m3, m3'⟩, m3''⟩
    · rw [b] at m3; cases m3
    · rw [a] at m3; cases m3
    · have := t3 m3' m3
      rw [corr_take_snoc he, hvI]
      push_cast
      rw [hB]
      omega
  · intro a
    rcases m4 with m4 | m4
    · omega
    · rw [corr_take_snoc he]
      split at m4
      · rename_i st st' c hs1 hs2
        have h1 : isRb e = true := by rw [c2, hs1]; rfl
        have h2 : isRv e = true := by
          rw [hs1, hs2] at hV
          by_contra h
          simp [h, dV] at hV
        simp only [h1, ite_true, Nat.add_sub_cancel]
        refine ⟨by omega, ?_⟩
        rw [ordEv_eq he h1]
        exact h2
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at m4
        have h1 : isRb e = false := by rw [c2, m4.2]; rfl
        simp only [h1, Bool.false_eq_true, ite_false, Nat.add_zero]
        exact t4 m4.1

end
end PTX.Kernels.TmlFa4Fwd.Proof
