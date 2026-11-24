-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Result.RdSLoad
public import Kernels.InklingRelDecode.Proof.Interface.RdPvBack

@[expose] public section

/-!
# The rescale load reads the last PV MMA of the previous block (`Rs.OLoadSrc`)

The `O` analogue of `Rd.sLoadSrc_of`. For the softmax thread's rescale load `tcgen05.ld` of
iteration `i ≥ 1` (the state at `ldO`):

* the poll of `o_done` before it, `Interface.preLdO_back` (the window of sites between the poll
  and the load), is the thread's `(i - 1)`-th successful poll of the barrier (`Rd.sm_cnt`), so it
  observes the lane's commit with `i - 1` earlier commits to it (`SO.o_observes`), the second PV
  commit of block `i - 1` (`Rd.o_commit_block`);
* the lane's state two events before that commit is step 7 of the PV half of iteration `i`
  (`Interface.exists_pv7_commit2`), which is `DoneBefore` the load (`SO.o_doneBefore`) and writes
  its 64 cells (`Mma.pv_writeCell`); it is the only lane state at that site and iteration
  (`Rd.pv7_unique`);
* every other writer of a cell is before it or after the load: the PV MMAs before it in the lane
  by program order (`Sr.pv_before`), the rescale stores of earlier iterations by `Sr.pv_ost_B`
  (a store before the load in the thread's program order is before the poll of the iteration, so
  its coordinate is below `i`), the later PV MMAs through thread 0's arrival on `p_ready` and the
  lane's poll of it (the premise `ORdv`), the thread's own later stores by program order after
  its `tcgen05.wait::ld`.

The cell of another thread's rescale store is never the load's (`Sr.split_thread`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rd
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.Sv (ValidRow)

noncomputable section

variable {Q : Params} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **A commit to `o_done` is at the site `pvCommit2`.** -/
theorem site_of_ocommit {g : Nat} {d : Mma.D} {pc : Nat} {sp : TcCommit.Spec}
    (hsh : EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = oDone L (g / L.block)) : d.site = .pvCommit2 := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [EvW.MmShape] at hsh
  case pvCommit2 => rfl
  case finCommit =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm SO.oFinal_ne_oDone
  case pvCommit1 =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm (SO.kvEmpty_ne_oDone (by omega))
  case qkCommit =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm.symm (SO.oDone_ne_sReady (by omega))
  all_goals first
    | (simp only [Event.mk.injEq] at hsh; simp at hsh; done)
    | (obtain ⟨_, _, hh, -⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | (obtain ⟨_, hh⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | (obtain ⟨_, _, _, _, _, _, hh⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | skip

/-- **The premise on the rescale load's rendezvous.** The softmax thread's `tcgen05.wait::ld`
after the rescale load of iteration `i` (the event after the load) is base-causally before an
event of thread 0 of the default partition that has at most `i / 2` arrivals on `p_ready (i % 2)`
before it (`StGate.rendezvous` for the load: the wait is before the thread's `bar.sync 0, 128`
at `bar24`, thread 0's matching one is before its arrival of block `i`). -/
def ORdv (Q : Params) (L : Launch) (X : Execution) {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (G : SrPkg L K A mem0 X) : Prop :=
  ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape} {pcw : Nat}, g < L.threads →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .ldO →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    X.get (g, k + 1) = some ⟨pcw, .tc .waitLd⟩ →
    ∃ e0, baseCausality L X (g, k + 1) (G.p0 (g / L.block), e0) ∧
      arrivals (pReady L (g / L.block) (d.i % 2)) ((X.tr (G.p0 (g / L.block))).take e0) ≤
        d.i / 2

theorem okPolls_mono (m : Loc) (l : List Event) {i j : Nat} (h : i ≤ j) :
    okPolls m (l.take i) ≤ okPolls m (l.take j) :=
  (List.take_sublist_take_left h).countP_le

/-- **`Rs.OLoadSrc`**: the softmax thread's rescale load of iteration `i` reads the PV MMA at
step 7 of iteration `i`, which is the only lane state at that site and iteration. -/
theorem oLoadSrc_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hcomp : Complete L X)
    (hR : Interface.RoleReads L X)
    (hb : Interface.BaseWordRead L X) (hn : Interface.NumWordRead Q L X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (G : SrPkg L kernel Assumptions.all mem0 X) (st : Pr.MmaStates Q L G)
    (ht : Tmem1.Tmem1Facts L X 0) (hl : SO.TmemLife L X) (hz : Rs.SmBaseZero Q L X)
    (hSoft : SoftAll L G) (hrdv : ORdv Q L X G) : Rs.OLoadSrc Q L X := by
  refine ⟨fun {g k pc a d vals sh} hg hvr hσ hs he => ?_⟩
  have hS := ProA.sharedOk_of_pre hpre
  have hW := waitOShape_of hS
  have hk : k < (X.tr g).length := len_of_get he
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  have hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = g / L.block → x.1 = G.cm (g / L.block) :=
    fun hx hc => l.mma_thread hx hc
  have hdef : g % L.block < 128 := (hf.reach hg hσ).1
  have hsoft : G.Soft (g / L.block) g := hSoft _ hcl g hg rfl hdef
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  -- the shape of the load
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he hσ (by simp [Interface.ExitState])
  obtain ⟨vals', hlen, hev⟩ := Sm.shape_ldO (Interface.fired_sm hF) hs
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev
  obtain ⟨hpc, ha, hvv, hsh⟩ := hev
  subst ha hvv hsh
  -- the poll before the load
  obtain ⟨kp, dp, ep, hkp, hep, hσp, hwp, hip, hpl, hwin⟩ :=
    Interface.preLdO_back k hk.le hσ (by simp [Interface.PreLdO, hs])
  have hgep : X.get (g, kp) = some ep := hep
  obtain ⟨up, hFp⟩ := Interface.fired_cont hX hf hg hgep hσp (by simp [Interface.ExitState])
  obtain ⟨okp, hevp⟩ := hW g dp ep up (Interface.fired_sm hFp) hwp
  obtain ⟨lp, pp, ap, scp, hkpe⟩ := hpl
  have hokp : okp = true := by
    rw [hevp] at hkpe
    simp only [Kind.wait.injEq] at hkpe
    exact hkpe.2.2.1
  subst hokp
  have hpoll : X.get (g, kp) = some ⟨Sm.evPc dp.site,
      .wait (oDone L (g / L.block)) (SO.oDoneParity dp.i) true true .cta⟩ := by
    rw [hgep, hevp]
  have hcnt := (sm_cnt hpre hX hf hg kp (by omega) _ hσp).2 dp rfl
  have hi1 : 1 ≤ d.i := by
    have := hcnt.ok hwp
    omega
  have hq : okPolls (oDone L (g / L.block)) ((X.tr g).take kp) = d.i - 1 := by
    rw [hcnt.o]
    have : SO.smOPolled dp = dp.i - 1 := by simp [SO.smOPolled, hwp]
    rw [this, hip]
  -- the commit the poll observes
  have hReach := Mbar.oReach H hsoft
  obtain ⟨ic, pcc, spc, rank, hgetc, hmbar, htgt, hcntc, hrank, hobs⟩ :=
    SO.o_observes H.cons H.facts H.opar hReach hpoll hq
  have hcm := l.cm_ok.1
  have hcmc := l.cm_ok.2
  have hickl : ic < (X.tr (G.cm (g / L.block))).length := len_of_get hgetc
  obtain ⟨dc, Pc, hσc, hshc⟩ := Interface.mma_event_state hpre hX hf.sound hf.tracked hcm hgetc
    (Or.inr ⟨spc, rfl⟩)
  have hsite : dc.site = .pvCommit2 :=
    site_of_ocommit hshc (by rw [hcmc]; exact hmbar)
  obtain ⟨hlead, k', dm, d1, hadj, hσm, hs7, hi7, htmc, hnm, hσ1, hs1, pcm, dst, spm, acc, mask,
    hevm⟩ := Interface.exists_pv7_commit2 hpre hX hf hickl hσc hsite
  have hcg : (G.cm (g / L.block)) / L.block = g / L.block := hcmc
  obtain ⟨dc', Pc', hσc', hsc', hdi⟩ := o_commit_block hpre hX hf hR hlead hB hcm hgetc
    (by rw [hcg]; exact hmbar)
  have hdd : dc' = dc := by
    have := Option.some.inj (Option.some.inj (hσc'.symm.trans hσc))
    simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
    exact this.1
  subst hdd
  rw [hcg, hcntc] at hdi
  have hI := Interface.mma_inv_at hX hf hickl hσc
  have hpv1 := (hI.pv (by rw [hsite]; trivial)).1
  have hdci : dc'.i = d.i := by omega
  have hmi : dm.i = d.i := hi7.trans hdci
  -- the last PV MMA
  have hmEvt : IsMma X (G.cm (g / L.block), k') := ⟨dst, spm, acc, mask, pcm, hevm⟩
  have hdm0 : dm.tm = 0 :=
    Interface.mma_tm hpre hX hf hb hn (m := (G.cm (g / L.block), k')) ⟨_, hσm⟩
  have hd0 : d.e.tm = 0 := hz hg hσ
  have hlenm : k' < (X.tr (G.cm (g / L.block))).length := len_of_get hevm
  have hpvA := st.pv hcm hlenm hσm hs7
  rw [hcmc] at hpvA
  obtain ⟨hdm1, hQm⟩ := hpvA
  obtain ⟨hqo, hdst, -, hmask, -⟩ := pv_event hpre hX hf hcm hevm hσm hs7
  have hT : g % L.block < 128 := hdef
  have hoa : Sm.oAddr L g d = d.e.tm + 256 + g % L.block / 32 * 2 ^ 21 :=
    Sm.oAddr_eq hT (by omega) (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
  have hlcell : ∀ j, tcDataCell L g (.s16x32bx2 64) (Sm.oAddr L g d) j =
      oCell (g / L.block) dm.tm (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) := by
    intro j
    have : d.e.tm = dm.tm := hd0.trans hdm0.symm
    rw [hoa, this]
    exact Rs.stO_cell L g (by omega) j
  refine ⟨(G.cm (g / L.block), k'), pcm, dst, spm, acc, mask, dm, Pc, hcm, hcmc, hevm, hσm,
    hs7, hmi, ?_, ?_⟩
  · intro j hj
    rw [hlcell j]
    set cell : Cell := oCell (g / L.block) dm.tm (Sm.row (g % L.block))
      (64 * Sm.half (g % L.block) + j) with hcelldef
    have hrow : Sm.row (g % L.block) < 64 := by unfold Sm.row; omega
    have hcol : 64 * Sm.half (g % L.block) + j < 128 := by unfold Sm.half; omega
    have hwc : writeCell spm dst mask (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) =
        some cell := by
      rw [hdst, hmask]
      have := pv_writeCell (sp := spm) hqo.desc (cta := g / L.block) (tm := dm.tm)
        (hqo.low.trans hcmc) (by omega) hrow hcol
      simpa using this
    have hmc : X.MmaCell (G.cm (g / L.block), k') cell :=
      ⟨_, _, _, _, _, _, ⟨pcm, hevm⟩, hwc⟩
    obtain ⟨jy, pcy, ey, hjy, hgy, hqy⟩ := hQm.issue
    obtain ⟨hIO, hcta⟩ := SO.pv_cells l.tmOk hqy hgy hmc
    have ix : WInfo L X (g / L.block) (G.cm (g / L.block)) (G.p0 (g / L.block))
        (G.tm (g / L.block)) (G.Soft (g / L.block)) (G.cm (g / L.block), k') cell :=
      .pv hQm hIO hcta
    -- the base column of the lane's accumulator is 0
    have hGtm : G.tm (g / L.block) = 0 := by
      obtain ⟨db, dsc, hd, -, hey⟩ := hqy
      rw [hey] at hgy
      have h1 := Option.some.inj (hevm.symm.trans hgy)
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h1
      have h2 := h1.2.1
      omega
    -- the source is done before the load
    have hbcl : baseCausality L X (g, kp) (g, k) :=
      SO.baseCausality_src hpoll rfl rfl hkp hk
    have hdone : DoneBefore L X (G.cm (g / L.block), k') (g, k) :=
      SO.o_doneBefore H.cons H.facts H.opar hone ⟨hcm, hg, by rw [hcmc]⟩ hReach hpoll hq hmEvt
        hcmc (le_trans (countP_take_mono _ _ (show k' ≤ ic by omega)) (le_of_eq hcntc)) hkp hk
    -- the wait after the load
    obtain ⟨pcw, hwait⟩ := Interface.ldO_wait hpre hX hf hcomp hg he hσ hs
    refine ⟨?_, .inl hmc, .inl (.inl hdone), ?_, ?_⟩
    · -- the source is not the load
      intro hh
      have hh1 : G.cm (g / L.block) = g := congrArg Prod.fst hh
      have hh2 : k' = k := congrArg Prod.snd hh
      subst hh2
      rw [hh1] at hσm
      rw [hσ] at hσm
      cases Option.some.inj (Option.some.inj hσm)
    · -- every other writer of the cell is before the PV MMA or after the load
      intro other hw'
      have hol := cta_lt hX (write_event hnc hns hw')
      have iy := winfo hnc hns (G.lane _ hol) hw' rfl
      have hxy : other.1 / L.block = g / L.block := iy.cta.symm.trans ix.cta
      rw [hxy] at iy
      cases iy with
      | @qk _ _ i' hq' h1' _ =>
        exact absurd hIO (SO.inS_inO_disjoint (Nat.mod_lt _ (by omega)) h1')
      | @pv _ _ m' hv' h1' _ =>
        rcases Nat.lt_trichotomy other.2 k' with hlt | heq | hgt
        · exact .inr (.inl (.inl (pv_before l.cm_ok.1 hv' hQm hlt)))
        · exact .inl (Prod.ext hv'.thread heq)
        · -- a later PV MMA: it follows the load through thread 0's arrival
          right; right; left
          obtain ⟨pcq, dq, sq, aq, mq, hgq⟩ := hv'.isMma.get
          have hic : other.2 ≠ ic := by
            intro hh
            have hother : other = (G.cm (g / L.block), ic) := Prod.ext hv'.thread hh
            rw [hother] at hgq
            have h := Option.some.inj (hgetc.symm.trans hgq)
            simp only [Event.mk.injEq, Kind.tc.injEq] at h
            cases h.2
          have hic1 : other.2 ≠ k' + 1 := by
            intro hh
            have hother : other = (G.cm (g / L.block), k' + 1) := Prod.ext hv'.thread hh
            rw [hother] at hgq
            rcases Result.Mma.mma_event_cases hpre hX hf hcm hgq with
              ⟨d'', P'', j'', hσ'', hI'', hs'', -⟩ | ⟨d'', P'', j'', hσ'', hI'', hs'', -⟩
            all_goals
              have hdd : d'' = d1 := by
                have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ1))
                simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
                exact this.1
              subst hdd
              rw [hs1] at hs''
              cases hs''
          have hgt2 : ic + 1 ≤ other.2 := by omega
          have hc1 := countP_take_succ (p := commitsTo (oDone L (g / L.block))) hgetc
            (by simp [commitsTo, hmbar])
          have hc2 := countP_take_mono (commitsTo (oDone L (g / L.block)))
            (X.tr (G.cm (g / L.block))) hgt2
          have hoc := hv'.oCommits
          have hpp := hv'.pPolls (d.i % 2) hb2
          unfold SO.below2 at hpp
          have hlen2 : other.2 < (X.tr (G.cm (g / L.block))).length := lane_len hv'.thread hgq
          obtain ⟨e0, hbc0, harr⟩ := hrdv hg hσ hs he hwait
          have hp0 := p0_before_lane H l hb2 harr (f := other.2) (by omega) hlen2
          have hx : other = (G.cm (g / L.block), other.2) := Prod.ext hv'.thread rfl
          rw [hx]
          exact ⟨(g, k + 1), ⟨pcw, hwait⟩, rfl, Nat.lt_succ_self k, .inl (hbc0.trans hp0)⟩
      | @pst t sk i' w j' a' vals'' sh'' cell' hst hp hjs ha hc' hin _ =>
        exact absurd hIO (SO.inP_inO_disjoint (Nat.mod_lt _ (by omega)) hin)
      | @ost t sk i' w j' a' vals'' sh'' cell' hst ho hjs ha hc' hin hctaO =>
        obtain ⟨ht', htc, ht128⟩ := soft_info H ho.gate.soft
        obtain ⟨hsh'', hl'', -⟩ := ho.shape
        subst hsh''
        -- the thread of the store is the load's
        have htg : g = t := by
          have heq : tcDataCell L g (.s16x32bx2 64) (256 + g % L.block / 32 * 2 ^ 21) j =
              tcDataCell L t (.s16x32bx2 64) (256 + w * 2 ^ 21) j' := by
            have e1 := hlcell j
            rw [hoa, hd0, Nat.zero_add] at e1
            have e2 : tcDataCell L g (.s16x32bx2 64) (256 + g % L.block / 32 * 2 ^ 21) j =
                cell := by
              rw [e1]
            rw [e2, hc', ha, hGtm, Nat.zero_add]
          exact (split_thread (L := L) (g := g) (h := t) (ba := 256) (off := 64) (by omega)
            hj (by omega) hdef ht128 (by rw [htc]) heq)
        subst htg
        obtain ⟨pcs, hgets⟩ := hst
        have hlens : sk < (X.tr g).length := len_of_get hgets
        have hne_k : sk ≠ k := by
          intro hh
          subst hh
          rw [he] at hgets
          simp at hgets
        have hne_w : sk ≠ k + 1 := by
          intro hh
          subst hh
          rw [hwait] at hgets
          simp at hgets
        by_cases hafter : k + 1 < sk
        · -- the store follows the load in the thread's program order
          right; right; left
          exact ⟨(g, k + 1), ⟨pcw, hwait⟩, rfl, Nat.lt_succ_self k,
            .inl (baseCausality_of_tc_po hwait rfl hafter hlens)⟩
        · -- the store is before the load: before the poll of the iteration
          right; left
          have hskk : sk < k := by omega
          have hskp : sk < kp := by
            by_contra hnot
            rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hnot) with hh | hh
            · -- sk = kp
              subst hh
              obtain ⟨ds, hσs, hds⟩ := Rs.stO_state hX hf hgets
              have := Option.some.inj (Option.some.inj (hσp.symm.trans hσs))
              simp only [Interface.TSt.d.injEq, DComp.St.sm.injEq] at this
              rw [this] at hwp
              rw [hwp] at hds
              cases hds
            · obtain ⟨dj, hσj, hsj⟩ := hwin sk hh hskk.le
              obtain ⟨ds, hσs, hds⟩ := Rs.stO_state hX hf hgets
              have := Option.some.inj (Option.some.inj (hσj.symm.trans hσs))
              simp only [Interface.TSt.d.injEq, DComp.St.sm.injEq] at this
              rw [this] at hsj
              rw [hds] at hsj
              simp [Interface.PreLdO] at hsj
          -- the coordinate of the store is below the iteration
          obtain ⟨ds, hσs, hds⟩ := Rs.stO_state hX hf hgets
          have hcs := (sm_cnt hpre hX hf ht' sk hlens.le _ hσs).2 ds rfl
          obtain ⟨jg, pcg, pg, scg, hjg, hgetg, hqg⟩ := ho.gate.poll
          have hlj : (X.tr g)[jg]? = some ⟨pcg, .wait (oDone L (g / L.block)) pg true true scg⟩ :=
            hgetg
          have hc3 : okPolls (oDone L (g / L.block)) ((X.tr g).take (jg + 1)) = i' - 1 + 1 := by
            rw [okPolls_take_succ _ hlj, hqg]
            simp [okPoll_wait (rfl : (⟨pcg, .wait (oDone L (g / L.block)) pg true true scg⟩ :
              Event) = _)]
          have hc4 := okPolls_mono (oDone L (g / L.block)) (X.tr g) (show jg + 1 ≤ sk by omega)
          rw [hcs.o] at hc4
          have hsmo : SO.smOPolled ds = ds.i := by simp [SO.smOPolled, hds]
          have hc5 := okPolls_mono (oDone L (g / L.block)) (X.tr g) (show sk ≤ kp by omega)
          rw [hcs.o, hq] at hc5
          have hi1' := ho.one_le
          have hnot : ¬ dm.i - 1 ≤ i' - 1 := by omega
          exact .inr (.inl (pv_ost_B H l hQm ho ⟨pcs, hgets⟩ hnot))
    · -- the source is live
      intro cta r hr hcov dd hrel
      obtain ⟨⟨pc1, grp, a1, n1, hd⟩, hdc⟩ := Tmem1.release_info hX ht.toTmem1Ops hr hrel
      have hown := Tmem1.covers_owner hcov
      obtain ⟨hlc, -⟩ := Tmem1.record_info hX ht.toTmem1Ops hr
      have hcc : dd.1 / L.block = (g, k).1 / L.block := by
        rw [hdc, ← hlc, ← hown]
        exact hcta
      refine .inl ⟨fun ⟨a', vals', sh', h'⟩ => (hl.ldst_before_dealloc hd hcc).1 h',
        fun ⟨a', vals', sh', h'⟩ => ?_, fun hta => ?_⟩
      · exfalso
        obtain ⟨pc2, h2⟩ := h'
        rw [he] at h2
        simp at h2
      · exfalso
        rcases hta with ⟨dd', s', ac', mk', pc2, h2⟩ | ⟨cp, hcp⟩ | ⟨s', hs'⟩
        · rw [he] at h2
          simp at h2
        · exact hnc _ _ hcp
        · exact hns _ _ hs'
  · -- uniqueness of the lane's state at PV step 7 of the iteration
    intro k'' d'' P'' hσ'' hs'' hi''
    have hk'' := Interface.lt_length_of_complete hX hf hcomp hcm hσ''
    exact (pv7_unique hpre hX hf hR hlenm hk'' hσm hs7 hσ'' hs'' (by rw [hi'']) ).symm

end
end PTX.Kernels.InklingRelDecode.Proof.Rd
