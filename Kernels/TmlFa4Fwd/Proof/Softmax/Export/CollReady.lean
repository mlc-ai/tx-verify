-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollState
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollTc
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcCount
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollOfCls
import Kernels.TmlFa4Fwd.Proof.Lib.NoTc
import Kernels.TmlFa4Fwd.Proof.Protocol.Soft.Blk
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
import Lemmas.Kernel.Progress.WarpReady
import Lemmas.Step.CtaBarNamed
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The blocking events before a softmax lane's collectives

The barrier after the register request, the last arrival on the correction warps' barrier and the
wait before a round's warp barrier are the events that block a lane right before a collective. When
a lane of the warp is at the same collective, past its own and released, the event is ready. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain preR finR)
open SoftColl

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {x y k : Nat}

/-- The barrier-2 events and the named-barrier arrivals before the sites read here. -/
private theorem rdy_tab (b : Bool) :
    (ptsOf b .bar2).countP (before .bar1) = 0 ∧
    (ptsOf b .bar2).countP (before (.down .first)) = 1 ∧
    (ptsOf b .bar2).countP inBias = 0 ∧ (ptsOf b .bar2).countP inPlain = 0 ∧
    (ptsOf b .nb).countP (before .finarr) = 1 ∧
    (ptsOf b (.arrive 96)).countP (before .finarr) = 1 ∧
    (ptsOf b .nb).countP (before (.down .second)) = 2 ∧
    (ptsOf b (.arrive 96)).countP (before (.down .second)) = 1 ∧
    (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 ∧
    (ptsOf b (.acquire 80)).countP (before .finarr) = 1 := by
  cases b <;> decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) {w : Nat} (hw8 : w < 8) (hsw : SameWarp L y x)
  (hwy : Prologue.warpIndex L y = w) (hrel : Step.Released L X y)
  (hnx : ∀ i pc, X.get (x, i) ≠ some ⟨pc, .exit⟩)
  {d dy : Softmax.Control.D} {n ny : Cls → Nat} {e : Event}
  (he : X.get (x, k) = some e)
  (hσ : Frame.stateAt (thread p L) X x k = some (some (SmWarp.sinj p L x d n)))
  (hy : Frame.stateAt (thread p L) X y (X.tr y).length = some (some (SmWarp.sinj p L y dy ny)))
include hp hX hFw hub hw8 hsw hwy hrel hnx he hσ hy

/-- **The barrier before the first pass.** -/
theorem soft_ready_bar1 (hs : d.site = .bar1) (hsy : dy.site = .down .first)
    (hk : e.kind = .bar 2 (some 416) .sync) : Ready L X (x, k) := by
  have hgx := hsw.1.2.1
  have hgy := hsw.1.1
  have hwx : Prologue.warpIndex L x = w := hsw.2.symm.trans hwy
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  obtain ⟨c, rb, rp, hQ, hLk, -, -⟩ := soft_open hp hX hub hgx hw8 hwx hσ
  obtain ⟨cy, rb', rp', hQy, hLky, -, -⟩ := soft_open hp hX hub hgy hw8 hwy hy
  have hs' : d.scheduler.site = .bar1 := hs
  have hsy' : dy.scheduler.site = .down .first := hsy
  obtain ⟨t1, -, t3, t4, -⟩ := rdy_tab (Softmax.lz L x)
  obtain ⟨-, s2, s3, s4, -⟩ := rdy_tab (Softmax.lz L y)
  have h1 := hQ.cnt .bar2 rfl
  have h2 := hQy.cnt .bar2 rfl
  simp only [passed, hs', t1, t3, t4, Nat.mul_zero, Nat.add_zero] at h1
  simp only [passed, hsy', s2, s3, s4, Nat.mul_zero, Nat.add_zero] at h2
  have hwx8 : Prologue.warpIndex L x < 8 := by rw [hwx]; exact hw8
  have hwy8 : Prologue.warpIndex L y < 8 := by rw [hwy]; exact hw8
  have hcx : ((X.tr x).take k).countP (Execution.isBarId 2) = 0 := by
    rw [soft_isBar2 hwx8, count hσ, ← hLk _ rfl, h1]
  have hcy : ((X.tr y).take (X.tr y).length).countP (Execution.isBarId 2) = 1 := by
    rw [soft_isBar2 hwy8, count hy, ← hLky _ rfl, h2]
  rw [List.take_length] at hcy
  obtain ⟨j, e', hj, hq, hcj⟩ := NamedBar.exists_ordinal (Execution.isBarId 2) (X.tr y) (r := 0)
    (by omega)
  obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hq
  have hget : X.get (y, j) = some ⟨pcj, .bar 2 cntj mj⟩ := hj
  have hmj : mj = .sync := by
    rcases soft_bar hp hX hFw hwy8 hget with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · rcases h with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · rw [hcj] at h; cases h
    · omega
    · omega
  subst hmj
  exact Sched.bar_ready_lane hX hgy hsw hget (Top.ready_of_rel hX hget rfl hrel) he
    (hcx.trans hcj.symm) hnx

/-- **The last arrival on the correction warps' barrier.** -/
theorem soft_ready_fin (hs : d.site = .finarr) (hsy : dy.site = .down .second)
    (hk : ∃ id cnt, e.kind = .bar id cnt .arrive) : Ready L X (x, k) := by
  have hgx := hsw.1.2.1
  have hgy := hsw.1.1
  have hwx : Prologue.warpIndex L x = w := hsw.2.symm.trans hwy
  obtain ⟨pc, kd⟩ := e
  obtain ⟨id, cnt, hk⟩ := hk
  simp only at hk
  subst hk
  have hwx8 : Prologue.warpIndex L x < 8 := by rw [hwx]; exact hw8
  have hwy8 : Prologue.warpIndex L y < 8 := by rw [hwy]; exact hw8
  obtain ⟨c, rb, rp, hQ, hLk, -, -⟩ := soft_open hp hX hub hgx hw8 hwx hσ
  obtain ⟨cy, rb', rp', hQy, hLky, -, -⟩ := soft_open hp hX hub hgy hw8 hwy hy
  have hs' : d.scheduler.site = .finarr := hs
  have hsy' : dy.scheduler.site = .down .second := hsy
  obtain ⟨-, -, -, -, t5, -, -, -, t9, t10, t11⟩ := rdy_tab (Softmax.lz L x)
  obtain ⟨-, -, -, -, -, -, s7, s8, s9, s10, -⟩ := rdy_tab (Softmax.lz L y)
  obtain ⟨-, -, r3, r4⟩ := rnd2 (Softmax.lz L y)
  have h1 := hQ.cnt .nb rfl
  have h2 := hQy.cnt .nb rfl
  have h3 := hQy.cnt (.arrive 96) rfl
  simp only [passed, hs', t5, t9, t10, Nat.mul_one] at h1
  simp only [passed, hsy', s7, s9, s10, Nat.mul_one] at h2
  simp only [passed, hsy', s8, r3, r4, Nat.mul_one] at h3
  have hid : id = w + 3 ∧ SoftRounds p L x (((X.tr x).take k).countP (Execution.isBarId id)) := by
    have hne : ∀ f, (⟨pc, .bar id cnt .arrive⟩ : Event).kind ≠ .ub f := fun f h => by cases h
    have hev := (SmWarp.fired_soft hp hX he hσ hne).1.1
    simp only [Softmax.Ev, hs', Kind.bar.injEq] at hev
    have hid : id = w + 3 := by rw [hev.1, soft_nbW hwx8, hwx]
    obtain ⟨a1, a2, -⟩ := rnd2 (Softmax.lz L x)
    have h4 := hQ.cnt (.acquire 80) rfl
    simp only [passed, hs', t11, a1, a2, Nat.mul_one] at h4
    refine ⟨hid, ?_⟩
    rcases soft_bar hp hX hFw hwx8 he with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, h | ⟨-, h⟩⟩
    · omega
    · omega
    · omega
    · exfalso
      rw [hid, ← hwx, soft_isBarId hwx8, sobj, soft_okPolls hwx8, count hσ, count hσ,
        ← hLk _ rfl, ← hLk _ rfl, h1, h4] at h
      omega
    · exact h
  obtain ⟨rfl, hTx⟩ := hid
  have hTy := soft_late_T hp hX hFw hw8 hwy hy rfl hQy hLky (by rw [hsy']; rfl)
  have hcx : ((X.tr x).take k).countP (Execution.isBarId (w + 3)) = cy (.arrive 96) := by
    obtain ⟨R, hR, h5⟩ := soft_mma hTx (y := x) rfl
    have h6 := hTy.mma hsw.1.2.2 hR
    omega
  have hcy : ((X.tr y).take (X.tr y).length).countP (Execution.isBarId (w + 3)) =
      cy (.arrive 96) + 1 := by
    rw [← hwy, soft_isBarId hwy8, count hy, ← hLky _ rfl, h2, h3]
    omega
  rw [List.take_length] at hcy
  obtain ⟨j, e', hj, hq, hcj⟩ := NamedBar.exists_ordinal (Execution.isBarId (w + 3)) (X.tr y)
    (r := cy (.arrive 96)) (by omega)
  obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hq
  have hget : X.get (y, j) = some ⟨pcj, .bar (w + 3) cntj mj⟩ := hj
  have hmj : mj = .arrive := by
    rcases soft_bar hp hX hFw hwy8 hget with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h, -⟩
    · omega
    · omega
    · omega
    · exact h
  subst hmj
  exact Sched.bar_ready_lane hX hgy hsw hget (Top.ready_of_rel hX hget rfl hrel) he
    (hcx.trans hcj.symm) hnx

end

private theorem pws_tab (b : Bool) :
    ([Softmax.Rd.first, .bias, .plain].map fun r =>
      ((ptsOf b (.arrive 96)).countP (before (.pws r)),
        (ptsOf b .tcld).countP (before (.pws r)), (ptsOf b .tcst).countP (before (.pws r)),
        (ptsOf b .nb).countP (before (.pws r)), (ptsOf b .sb).countP (before (.pws r)))) =
      [(1, 4, 4, 1, 1), (2, 8, 8, 2, 2), (2, 8, 8, 2, 1)] ∧
    [(ptsOf b .tcld).countP inBias, (ptsOf b .tcst).countP inBias, (ptsOf b .nb).countP inBias,
      (ptsOf b .sb).countP inBias, (ptsOf b .tcld).countP inPlain, (ptsOf b .tcst).countP inPlain,
      (ptsOf b .nb).countP inPlain, (ptsOf b .sb).countP inPlain] = [4, 4, 1, 1, 4, 4, 1, 0] ∧
    preR (.pws .first) = true ∧ inBias (Softmax.Site.pws .bias).pos = true ∧
    inPlain (Softmax.Site.pws .plain).pos = true := by
  cases b <;> decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) {w : Nat} (hw8 : w < 8)
include hp hX hFw hub hw8

/-- **A lane at a round's warp barrier**: its collectives and its `tcgen05` events. -/
theorem soft_pws_counts {g k : Nat} (hg : g < L.threads) (hw : Prologue.warpIndex L g = w)
    {d : Softmax.Control.D} {n : Cls → Nat} {r : Softmax.Rd}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)))
    (hs : d.site = .pws r) : ∃ (a : SoftRun) (u : Nat), IsSoftTile p L w (g / L.block) g a ∧
      ((X.tr g).take k).countP Sched.isWarpColl = startEl w + a.ch + 2 * u ∧
      ((X.tr g).take k).countP isTcColl + 3 * min (u + 1) (1 + a.nb) = 14 * (u + 1) := by
  obtain ⟨c, rb, rp, hQ, hLk, ⟨hFE, hu⟩, hI⟩ := soft_open hp hX hub hg hw8 hw hσ
  have hN := soft_cnt_eq hp hX hub hg hw8 hw hσ
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  have hTc := soft_tc hp hX hFw hg k _ (by rintro j _ ⟨pc, _⟩ he f rfl; exact hub ⟨_, pc, f, he⟩)
    hσ hub0
  have hs' : d.scheduler.site = .pws r := hs
  have hTc' : (((X.tr g).take k).countP isTcColl : Int) = c .tcld + c .tcst + 6 * c .nb -
      3 * c .sb := by
    have h0 : Softmax.tcCorr d.site (d.k == 0) = 0 := by rw [hs]; rfl
    rw [h0, Int.add_zero] at hTc
    rw [hLk _ rfl, hLk _ rfl, hLk _ rfl, hLk _ rfl]
    exact hTc
  simp only [Epilogue.Fits, SmWarp.toE, hs', SmWarp.epi] at hFE
  obtain ⟨R, bal, hC, h5, h6⟩ := hFE
  obtain ⟨eB, eP⟩ := nBP hC h5 h6 (hu (by rw [hs']; rfl))
  obtain ⟨hP, -, -, -, -, -, -, hns, hnv⟩ := hC
  obtain ⟨a, hT, a1, a2, a3⟩ := soft_tile hp hg hw hP
  rw [← eB] at a2
  obtain ⟨r1, r2, r3, -⟩ := region hQ
  rw [← a2] at r1 r2 r3
  have h96 := hQ.cnt (.arrive 96) rfl
  have e1 := hQ.cnt .tcld rfl
  have e2 := hQ.cnt .tcst rfl
  have e3 := hQ.cnt .nb rfl
  have e4 := hQ.cnt .sb rfl
  obtain ⟨t1, t2, t3, t4⟩ := rnd2 (Softmax.lz L g)
  obtain ⟨tab, reg, p1, p2, p3⟩ := pws_tab (Softmax.lz L g)
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at tab reg
  obtain ⟨⟨f1, f2, f3, f4, f5⟩, ⟨b1, b2, b3, b4, b5⟩, ⟨q1, q2, q3, q4, q5⟩⟩ := tab
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := reg
  simp only [passed, t3, t4, g1, g2, g3, g4, g5, g6, g7, g8, hs', Nat.mul_one,
    Nat.mul_zero] at h96 e1 e2 e3 e4
  have hrem : d.scheduler.site.rem = 2 := by rw [hs']; rfl
  have hN' : ((X.tr g).take k).countP Sched.isWarpColl =
      n .shfl + n .vote + ((X.tr g).take k).countP roundColl := hN
  generalize ((X.tr g).take k).countP roundColl = E at hI hN'
  generalize ((X.tr g).take k).countP Sched.isWarpColl = N at hN'
  generalize ((X.tr g).take k).countP isTcColl = C at hTc'
  clear hN hTc
  rw [hs'] at r1 r2 r3
  refine ⟨a, c (.arrive 96) - 1, hT, ?_, ?_⟩
  all_goals
    cases r with
    | first =>
      obtain ⟨h0, -⟩ := r1 p1
      rw [f1] at h96; rw [f2] at e1; rw [f3] at e2; rw [f4] at e3; rw [f5] at e4
      clear * - hN' hI hrem hns hnv a1 h0 h96 e1 e2 e3 e4 hTc'
      omega
    | bias =>
      obtain ⟨h0, h1, -⟩ := r2 p2
      rw [b1] at h96; rw [b2] at e1; rw [b3] at e2; rw [b4] at e3; rw [b5] at e4
      clear * - hN' hI hrem hns hnv a1 h0 h1 h96 e1 e2 e3 e4 hTc'
      omega
    | plain =>
      obtain ⟨h0, -⟩ := r3 p3
      rw [q1] at h96; rw [q2] at e1; rw [q3] at e2; rw [q4] at e3; rw [q5] at e4
      clear * - hN' hI hrem hns hnv a1 h0 h96 e1 e2 e3 e4 hTc'
      omega

omit hFw in
/-- A softmax lane's `tcgen05` event is no paired Tensor Memory operation. -/
theorem soft_tc_kind {g j : Nat} (hg : g < L.threads) (hw : Prologue.warpIndex L g = w)
    {e : Event} (he : X.get (g, j) = some e) (hc : isTcColl e = true) :
    ∃ pc t, e = ⟨pc, .tc t⟩ ∧ ∀ grp dst act, t ≠ .resource grp dst act := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, j), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨σ, hσ, hR⟩ := good_state hp hX he (fun pc f h => hne f (by rw [h]))
    (SmWarp.good hp hX hw8 hg hw j)
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | tc t =>
    refine ⟨pc, t, rfl, ?_⟩
    rintro grp dst act rfl
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · have hst := start_fired hp hX he hσ
      have := start_tcFree hst.1 hst.2.1
      rw [hc] at this
      cases this
    · exact soft_no_res (SmWarp.fired_soft hp hX he hσ hne).1 grp dst act rfl
  | _ => simp [isTcColl] at hc

/-- **The wait before a round's warp barrier.** -/
theorem soft_ready_wait {x y k : Nat} (hsw : SameWarp L y x) (hwy : Prologue.warpIndex L y = w)
    (hrel : Step.Released L X y) {d dy : Softmax.Control.D} {n ny : Cls → Nat} {e : Event}
    {r : Softmax.Rd} (he : X.get (x, k) = some e) (hc : isTcColl e = true)
    (hlen : k + 1 = (X.tr x).length)
    (hσ : Frame.stateAt (thread p L) X x (X.tr x).length = some (some (SmWarp.sinj p L x d n)))
    (hy : Frame.stateAt (thread p L) X y (X.tr y).length = some (some (SmWarp.sinj p L y dy ny)))
    (hs : d.site = .pws r) (hsy : dy.site = .pws r)
    (hn : (X.tr x).countP Sched.isWarpColl = (X.tr y).countP Sched.isWarpColl) :
    Ready L X (x, k) := by
  have hwx : Prologue.warpIndex L x = w := hsw.2.symm.trans hwy
  obtain ⟨a, u, hT, hN, hC⟩ := soft_pws_counts hp hX hFw hub hw8 hsw.1.2.1 hwx hσ hs
  obtain ⟨b, v, hT', hN', hC'⟩ := soft_pws_counts hp hX hFw hub hw8 hsw.1.1 hwy hy hsy
  rw [List.take_length] at hN hC hN' hC'
  obtain rfl : b = a := by
    rw [hsw.1.2.2] at hT'
    exact IsSoftTile.same hsw.1.2.2 hT hT'
  obtain rfl : u = v := by omega
  have hcx : ((X.tr x).take k).countP isTcColl + 1 = (X.tr x).countP isTcColl := by
    conv_rhs => rw [← List.take_length (l := X.tr x), ← hlen, List.take_add_one,
      show (X.tr x)[k]? = some e from he]
    simp [hc]
  obtain ⟨j, e', hj, hq, hcj⟩ := NamedBar.exists_ordinal isTcColl (X.tr y)
    (r := ((X.tr x).take k).countP isTcColl) (by omega)
  have hget : X.get (y, j) = some e' := hj
  obtain ⟨pc, t, rfl, ht⟩ := soft_tc_kind hp hX hub hw8 hsw.1.2.1 hwx he hc
  obtain ⟨pc', t', rfl, ht'⟩ := soft_tc_kind hp hX hub hw8 hsw.1.1 hwy hget hq
  have hres : (Event.mk pc' (.tc t')).kind.resume = .blocking false := by
    cases t' <;> first | rfl | (simp [isTcColl] at hq)
  exact Sched.tc_ready_lane hsw hget ht' ⟨⟨_, hget, hq⟩, hcj⟩
    (Top.ready_of_rel hX hget hres hrel) he ht ⟨⟨_, he, hc⟩, rfl⟩ le_rfl

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
