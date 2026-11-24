-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Tmem
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcCount
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Correction.Export.BarLag
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Place
import Kernels.TmlFa4Fwd.Proof.Correction.Export.RescaleTrace
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcEv
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcStates
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Epilogue.WorkPicked
import Lemmas.Kernel.Source.WarpColl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The rescale ballots of a correction lane that exits

A correction lane with a tile of `R` rescale rounds that exits made the ballot of each stage of each
round (`corr_ballot_at`), and after a nonzero one it stored every chunk of its accumulator
(`corr_ballot_store`). A ballot's bit of the lane is its predicate, once the warp's lanes exit
(`corr_ballot_bit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem rb_tab : allSites.all (fun s => !(decide (s.pc = 8009) || decide (s.pc = 8228)) ||
    [(0 : Fin 2), 1].any fun st => s == .rvote st) = true := by decide +kernel

private theorem vote_tab : ∀ st : Fin 2, brv (.rvote st) = st.val ∧
    bnb (.rvote st) = (ptsOf (.nb 0)).countP (before (.rvote st)) ∧
    (ptsOf (.nb 0)).countP inRound = 1 ∧
    (ptsOf (.arrive (96 + 8 * st.val))).countP (before (.rvote st)) = 1 ∧
    (ptsOf (.arrive (96 + 8 * st.val))).countP inRound = 1 := by decide +kernel

private theorem exit_tab : brv (.exit true) = 0 ∧
    bnb (.exit true) = (ptsOf (.nb 0)).countP (before (.exit true)) ∧
    (ptsOf (.nb 0)).countP inRound = 1 ∧ 8447 ≤ (Site.exit true).pc ∧
    (Site.exit true).noTile = false := by decide +kernel

private theorem pos_tab : [(0 : Fin 2), 1].all (fun st => allSites.all fun s =>
    (List.finRange 8).all fun c =>
      !decide (stPos st s = 3 * c.val + 3) || s == .rst st c) = true := by
  decide +kernel

private theorem start_kind {s : Startup.D} {e : Event} (hx : exit L g s = none)
    (hev : Startup.Ev L g s e) : e.kind ≠ .exit ∧ isBallot e = false ∧ isFullVote e = false := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kd⟩ := e
  cases site
  case enter r => simp [exit] at hx
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;>
      subst hk <;> exact ⟨nofun, rfl, rfl⟩
  all_goals simp only [Startup.Ev] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals exact ⟨nofun, rfl, rfl⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hub hw hw1

omit hp hX hFw hw hw1 in
private theorem noUb {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ∀ f, e.kind ≠ .ub f := fun f hf =>
  hub ⟨(g, k), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩

/-- **The rescale ballots of a correction lane with a tile that exits** are two per round. -/
theorem corr_exit_ballots {b k pc : Nat} (hb : b < p.batch)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ R, CorrRounds p L g R ∧ ((X.tr g).take k).countP isRb = 2 * R := by
  have hg := Frame.lt_of_get hX he
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (noUb hub he) with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · exact absurd rfl (start_kind hi.2 hev).1
  obtain ⟨l, hs⟩ := corr_exit_at (corr_ctl_ev hev (by simp))
  have hs : d.site = .exit l := hs
  cases l with
  | false =>
    exfalso
    obtain ⟨rv, -, -, hFE, -⟩ : CorrWarp.CFits p L g d (n .shfl) (n .vote) := (hR h0).2
    exact Epilogue.no_exit_of_work hp hg hb hhi hFE
      (by simp only [show d.scheduler.site = d.site from rfl, hs, CorrWarp.epi])
  | true =>
    obtain ⟨t1, t2, t3, t4, t5⟩ := exit_tab
    rcases corr_place hp hX hFw hub hg hw hw1 hσ with ⟨-, s, n', h⟩ |
      ⟨d', n', r, h, -, hc, -, hreg, hno⟩
    · cases h
    cases h
    have hs' : d.scheduler.site = .exit true := hs
    have hP : ∃ R bal, Epilogue.Picked p L g R bal := by
      by_contra hn
      rcases hno hn with h | h <;> rw [hs'] at h
      · omega
      · rw [t5] at h; cases h
    obtain ⟨R0, bal, hP⟩ := hP
    have hR : CorrRounds p L g _ := ⟨R0, bal, hP, rfl⟩
    refine ⟨_, hR, ?_⟩
    obtain ⟨hr, -⟩ := hreg _ hR
    generalize (Bs p L g (corrRef p L g R0 bal)).toNat - 1 = R at hr
    rw [hs'] at hr
    unfold Reg at hr
    have hT : TcC X g k (.exit true) n := by
      rcases corr_tcC hp hX hFw hub hg hw hw1 k
        (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1.le _ hσ with
        ⟨s, n', h, -⟩ | ⟨d', n', h, hT⟩
      · cases h
      · cases h; rw [hs] at hT; exact hT
    have h1 := hT.ballots
    have h2 := hc (.nb 0) (by simp)
    rw [hs'] at h2
    rw [t1, t2] at h1
    simp only [passed, t3] at h2
    omega

/-- **The rescale ballot of a stage of a round.** -/
theorem corr_ballot_at {k R r : Nat} (st : Fin 2)
    (hk : ((X.tr g).take k).countP isRb = 2 * R) (hr : r < R) :
    ∃ q pc a b d n, q < k ∧ X.get (g, q) = some ⟨pc, .vote (2 ^ 32 - 1) a b⟩ ∧
      Frame.stateAt (thread p L) X g q = some (some (CorrWarp.cinj p L g d n)) ∧
      d.site = .rvote st ∧ Tm.pArr L X g st q = r + 1 := by
  have hst := st.isLt
  obtain ⟨q, e, hqk, he, hb, hc⟩ := exists_nthEv (X := X) (p := isRb) (g := g) (k := k)
    (n := 2 * r + st.val) (by omega)
  have hg := Frame.lt_of_get hX he
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (noUb hub he) with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · have h := (start_kind hi.2 hev).2.1
    simp [isRb, h] at hb
  have hpc : e.pc = d.site.pc :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ (noUb hub he)
  obtain ⟨st', hs⟩ : ∃ st', d.site = .rvote st' := by
    have h1 := List.all_eq_true.mp rb_tab d.site (mem_allSites _)
    simp only [isRb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
    rw [← hpc] at h1
    rcases hb.1 with h | h <;> rw [h] at h1 <;> simp at h1 <;>
      rcases h1 with h1 | h1 <;> exact ⟨_, h1⟩
  have hT : TcC X g q (.rvote st') n := by
    rcases corr_tcC hp hX hFw hub hg hw hw1 q
      (List.getElem?_eq_some_iff.mp (show (X.tr g)[q]? = _ from he)).1.le _ hσ with
      ⟨s, n', h, -⟩ | ⟨d', n', h, hT⟩
    · cases h
    · cases h; rw [hs] at hT; exact hT
  obtain ⟨r', ℓ, hQ⟩ := (hR h0).1.counts
  have hs' : d.scheduler.site = .rvote st' := hs
  have h2 := hQ.cnt (.nb 0) (by simp)
  have h3 := hQ.cnt (.arrive (96 + 8 * st'.val)) (by simp)
  obtain ⟨t1, t2, t3, t4, t5⟩ := vote_tab st'
  rw [hs'] at h2 h3
  simp only [passed, t3, t4, t5] at h2 h3
  have h1 := hT.ballots
  rw [t1, t2, hc] at h1
  have h2 : n (.corr (.nb 0)) = _ := h2
  have h3 : n (.corr (.arrive (96 + 8 * st'.val))) = _ := h3
  have hst' := st'.isLt
  obtain rfl : st' = st := Fin.ext (by omega)
  obtain ⟨site, v, kk⟩ := d
  change site = _ at hs
  subst hs
  obtain ⟨a, b, hkd⟩ := hev
  obtain ⟨pc, kd⟩ := e
  change kd = _ at hkd
  subst hkd
  exact ⟨q, pc, a, b, _, n, hqk, he, hσ, rfl, by rw [pArr_at hσ]; omega⟩

/-- **The stores after a nonzero ballot** of a lane that exits: one of each chunk. -/
theorem corr_ballot_store {q k pc pcx : Nat} {a : Bool} {b : BitVec 32} {st : Fin 2}
    {d : Control.D} {n : Cls → Nat} (he : X.get (g, q) = some ⟨pc, .vote (2 ^ 32 - 1) a b⟩)
    (hσ : Frame.stateAt (thread p L) X g q = some (some (CorrWarp.cinj p L g d n)))
    (hs : d.site = .rvote st) (hqk : q < k) (hx : X.get (g, k) = some ⟨pcx, .exit⟩)
    (hb : Arith32.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0 = false) (c : Fin 8) :
    ∃ k' ad vals, X.TSt (g, k') ad vals .s32x32b ∧
      ad % 65536 = 256 + 128 * st.val + 16 * c.val ∧ vals.length = 16 ∧
      Tm.pArr L X g st k' = Tm.pArr L X g st q := by
  have hlen := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from hx)).1
  have ev : ∀ j ≤ k, ∃ e', X.get (g, j) = some e' := fun j hj =>
    ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
  have walk : ∀ t ≤ 24, ∃ d' n', q + 1 + t ≤ k ∧
      Frame.stateAt (thread p L) X g (q + 1 + t) = some (some (CorrWarp.cinj p L g d' n')) ∧
      stPos st d'.site = 1 + t ∧ Tm.pArr L X g st (q + 1 + t) = Tm.pArr L X g st q := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨e1, h1⟩ := ev (q + 1) (by omega)
      obtain ⟨d', hσ', hsu, -, -⟩ :=
        corr_step hp hX hFw hw hw1 he h1 (noUb hub he) (noUb hub h1) hσ
      refine ⟨d', _, hqk, hσ', ?_, ?_⟩
      · obtain ⟨site, v, kk⟩ := d
        change site = _ at hs
        subst hs
        simp only [Control.succ, succ, Control.D.scheduler, afterVote, hb, D.ite,
          Bool.false_eq_true, ite_false, Option.map_some, Option.some.injEq] at hsu
        subst hsu
        simp [stPos, Control.erase]
      · exact pArr_next he rfl
    | succ t ih =>
      intro ht
      obtain ⟨d', n', hle, hσ', hpos, harr⟩ := ih (by omega)
      obtain ⟨e1, h1⟩ := ev (q + 1 + t) hle
      rcases CorrWarp.open_ev hp hX hFw hw hw1 h1 (noUb hub h1) with ⟨s, n0, h, -⟩ |
        ⟨d0, n0, h, -, -, -, hev, -⟩
      · rw [hσ'] at h; cases h
      rw [hσ'] at h
      cases h
      obtain ⟨tk, hk⟩ := (stPos_ev (d := d'.scheduler) (by show 1 ≤ stPos st d'.site; omega)
        (stPos_shape (st := st) (by omega) hev) (noUb hub h1)).1 (by
          show stPos st d'.site ≤ 25; omega)
      have hlt : q + 1 + t < k := by
        rcases Nat.eq_or_lt_of_le hle with h | h
        · rw [h, hx] at h1
          cases h1
          cases hk
        · exact h
      obtain ⟨e2, h2⟩ := ev (q + 1 + t + 1) hlt
      obtain ⟨d2, hσ2, hsu, -, -⟩ :=
        corr_step hp hX hFw hw hw1 h1 h2 (noUb hub h1) (noUb hub h2) hσ'
      refine ⟨d2, _, hlt, hσ2, ?_, ?_⟩
      · rw [stPos_next_control (by omega) (by omega) hsu, hpos]
        omega
      · refine (pArr_next h1 ?_).trans harr
        obtain ⟨pc1, kd1⟩ := e1
        simp only at hk
        subst hk
        rfl
  have hc := c.isLt
  obtain ⟨d', n', hle, hσ', hpos, harr⟩ := walk (3 * c.val + 2) (by omega)
  have hsite : d'.site = .rst st c := by
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp pos_tab st
      (by fin_cases st <;> simp)) d'.site (mem_allSites _)) c (List.mem_finRange c)
    rw [hpos] at h1
    simpa [show 1 + (3 * c.val + 2) = 3 * c.val + 3 by omega] using h1
  obtain ⟨e1, h1⟩ := ev _ hle
  rcases CorrWarp.open_ev hp hX hFw hw hw1 h1 (noUb hub h1) with ⟨s, n0, h, -⟩ |
    ⟨d0, n0, h, -, -, -, hev, -⟩
  · rw [hσ'] at h; cases h
  rw [hσ'] at h
  cases h
  have hev := stPos_shape (st := st) (by omega) hev
  have hne := noUb hub h1
  obtain ⟨pc1, kd1⟩ := e1
  simp only [Ev, show d'.scheduler.site = .rst st c from hsite] at hev
  obtain ⟨ad, vals, sh, hk⟩ := hev.resolve_right fun ⟨f, h⟩ => hne f h
  subst hk
  have ht : X.TSt (g, q + 1 + (3 * c.val + 2)) ad vals sh := ⟨pc1, h1⟩
  obtain ⟨d1, n1, -, -, hσ1, -, rfl, st', c', hs1, h3, h4⟩ :=
    corr_st_state hp hX hFw hw hw1 ht
  rw [hσ'] at hσ1
  cases hσ1
  rw [hsite] at hs1
  cases hs1
  exact ⟨_, ad, vals, ht, h3, h4, harr⟩

omit hub in
/-- An event of a correction lane is no mode vote. -/
private theorem no_mode {k pc mask : Nat} {md : VoteMode} {a r : Bool}
    (he : X.get (g, k) = some ⟨pc, .voteMode md mask a r⟩) : False := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (by intro f h; cases h) with
    ⟨⟨site, x1, x2, x3⟩, n, -, -, -, hi, hev⟩ | ⟨⟨s, v, kk⟩, n, -, -, -, -, hev, -⟩
  · cases site
    case enter r => have hx : exit L g _ = none := hi.2; simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · cases s
    all_goals simp only [Control.Ev, Control.D.scheduler, Ev, rdOrUb, Epilogue.Ev,
      Site.toE] at hev
    all_goals shape_destruct hev
    all_goals cases ‹Kind.voteMode _ _ _ _ = _›

omit hub in
/-- **A ballot's bit of its lane is its predicate**, once the warp's lanes exit. -/
theorem corr_ballot_bit {q pc M : Nat} {a : Bool} {b : BitVec 32}
    (hall : ∀ y, SameWarp L g y → ∃ kx pcx, X.get (y, kx) = some ⟨pcx, .exit⟩)
    (hM : ∀ i < 32, M.testBit i = true)
    (he : X.get (g, q) = some ⟨pc, .vote M a b⟩) : b.getLsbD (laneOf L g) = a := by
  classical
  have hg := Frame.lt_of_get hX he
  have hb32 : L.block % 32 = 0 := by rw [hp.block]
  set N := ((X.tr g).take q).countP (fun ev => (voteClass ev.kind).any (·.mask == M))
    with hN
  have hK : X.MaskK voteClass (g, q) M N :=
    ⟨⟨_, ⟨M, .ballot, a⟩, he, rfl, rfl⟩, rfl⟩
  let Q : Nat → Bool → Prop := fun i v => ∃ j pc' b', X.get (g - laneOf L g + i, j) =
    some ⟨pc', .vote M v b'⟩ ∧ X.MaskK voteClass (g - laneOf L g + i, j) M N
  let part : Nat → Option Bool := fun i =>
    if h : i < 32 ∧ ∃ v, Q i v then some h.2.choose else none
  have hMI : MaskInstance L voteClass X g M N .ballot part := by
    intro i hi
    refine ⟨fun _ => ?_, fun hb => ?_⟩
    · obtain ⟨hiT, hiW, hiC, hiL, hiS⟩ := Frame.lane_facts hb32 hg rfl hi
      by_cases h : i < 32 ∧ ∃ v, Q i v
      · obtain ⟨j, pc', b', hj, hjk⟩ := h.2.choose_spec
        exact .inl ⟨j, pc', _, _, hj, rfl, hjk, dite_eq_left h⟩
      · refine .inr ⟨?_, dite_eq_right h⟩
        obtain ⟨kx, pcx, hx⟩ := hall _ hiS
        refine ⟨kx, pcx, hx, ?_⟩
        by_contra hgt
        obtain ⟨j, e, -, hj, hv, hcj⟩ := exists_nthEv (X := X)
          (p := fun ev => (voteClass ev.kind).any (·.mask == M))
          (g := g - laneOf L g + i) (k := kx) (n := N) (by omega)
        obtain ⟨pcj, kj⟩ := e
        have hwy : Prologue.warpIndex L (g - laneOf L g + i) = Prologue.warpIndex L g :=
          hiS.2.symm
        cases kj <;> simp only [voteClass, Option.any_none, Bool.false_eq_true,
          Option.any_some, beq_iff_eq] at hv
        · subst hv
          exact h ⟨hi, _, j, pcj, _, hj, ⟨⟨_, _, hj, rfl, rfl⟩, hcj⟩⟩
        · exact no_mode hp hX hFw (by omega) (by omega) hj
    · rw [hM i hi] at hb
      cases hb
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hself : g - laneOf L g + laneOf L g = g := Nat.sub_add_cancel (Nat.mod_le _ _ |>.trans
    (Nat.mod_le _ _))
  have hQ : ∃ v, Q (laneOf L g) v := ⟨a, q, pc, b, by rw [hself]; exact he, by rw [hself]; exact hK⟩
  refine (hX.vote g q N pc _ _ b he hK part hMI _ hl).1 a ?_
  have h : laneOf L g < 32 ∧ ∃ v, Q (laneOf L g) v := ⟨hl, hQ⟩
  refine (dite_eq_left h).trans (congrArg some ?_)
  obtain ⟨j, pc', b', hj, hjk⟩ := h.2.choose_spec
  rw [hself] at hj hjk
  have hjq : j = q := by
    refine nthEv_unique (X := X) (g := g)
      (p := fun ev => (voteClass ev.kind).any (·.mask == M)) hj (by simp [voteClass]) he
      (by simp [voteClass]) (hjk.2.trans hK.2.symm)
  subst hjq
  have := hj.symm.trans he
  simp only [Option.some.injEq, Event.mk.injEq, Kind.vote.injEq] at this
  exact this.2.2.1

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
