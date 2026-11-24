-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Result.SvScoreLoad
public import Kernels.InklingRelDecode.Proof.Result.SwStore
public import Kernels.InklingRelDecode.Proof.Result.RsOSource
public import Kernels.InklingRelDecode.Proof.Interface.RdSmBack
public import Kernels.InklingRelDecode.Proof.Interface.RdElect
public import Kernels.InklingRelDecode.Proof.Interface.RdLayer

@[expose] public section

/-!
# The S tile's load reads the last QK MMA (`Sv.SLoadSrc`)

The S-tile analogue of `Rs.oSource_of`. For the softmax thread's `tcgen05.ld` of iteration `i`
(the state at `ldS`):

* the poll of `s_ready (i % 2)` two events before it is the thread's `(i / 2)`-th successful poll
  of that barrier (`Rd.sm_cnt`, `Interface.ldS_back`), so it observes the lane's commit with
  `i / 2` earlier commits to the barrier (`SO.s_observes`), which is the QK commit of block `i`
  (`Rd.qk_commit_block`: the anchored run of the lane from the thread's states);
* the lane's state one event before that commit is step 7 of the QK half of iteration `i`
  (`Interface.exists_qk7`), an MMA that is `DoneBefore` the load (`Sr.s_doneBefore_to`), writes
  the load's 64 cells (`Mma.qk_writeCell`);
* every other writer of a cell is before it or after the load: the QK MMAs of the lane before it
  by program order (`Sr.qk_before`) and the `P` stores of earlier blocks (`Sr.qk_pst_B`); a later
  QK MMA follows the load through thread 0's arrival on `p_ready` and the lane's poll of it
  (`SRdv`, `SO.p_before_pv`); a `P` store of a block from `i` on is the premise `SPstAfter`.

Premises: `SRdv` (the load's `tcgen05.wait::ld` is base-causally before an event of thread 0 with
at most `i / 2` arrivals on `p_ready (i % 2)`), `SPstAfter` (the `P` stores of blocks `i, i + 1, …`
come after the load: the S load before the `P` store of the other half, `Sr.PAliasSyncS`), the
softmax threads of a CTA are its default-partition threads (`hSoft`), the handshake's
(`SrPkg`, `Pr.MmaStates`, `Tmem1.Tmem1Facts`, `SO.TmemLife`), the role byte protocol `RoleReads`,
`SmBaseZero` and the words the MMA warp reads (`BaseWordRead`, `NumWordRead`).
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
/-- **A commit to `s_ready b` is at the site `qkCommit`.** -/
theorem site_of_scommit {g : Nat} {d : Mma.D} {pc b : Nat} {sp : TcCommit.Spec} (hb : b < 2)
    (hsh : EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = sReady L (g / L.block) b) : d.site = .qkCommit := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [EvW.MmShape] at hsh
  case qkCommit => rfl
  case finCommit =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm (SO.oFinal_ne_sReady hb)
  case pvCommit1 =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm (SO.kvEmpty_ne_sReady (by omega) hb)
  case pvCommit2 =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm (SO.oDone_ne_sReady hb)
  all_goals first
    | (simp only [Event.mk.injEq] at hsh; simp at hsh; done)
    | (obtain ⟨_, _, hh, -⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | (obtain ⟨_, hh⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | (obtain ⟨_, _, _, _, _, _, hh⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | skip

/-- **The premise on the S load's rendezvous.** The softmax thread's `tcgen05.wait::ld` after the
load of iteration `i` is base-causally before an event of thread 0 of the default partition that
has at most `i / 2` arrivals on `p_ready (i % 2)` before it (the analogue of `StGate.rendezvous`
for the load: the wait is before the thread's `bar.sync 0, 128`, thread 0's matching
`bar.sync 0, 128` is before its arrival of block `i`; `Sr.BarChain`, `Sr.Bar128Causal`, and the
barrier-0 ordinal of the site `bar20`). -/
def SRdv (Q : Params) (L : Launch) (X : Execution) {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (G : SrPkg L K A mem0 X) : Prop :=
  ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}, g < L.threads →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .ldS →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    ∃ wl pcw e0, k < wl ∧ X.get (g, wl) = some ⟨pcw, .tc .waitLd⟩ ∧
      baseCausality L X (g, wl) (G.p0 (g / L.block), e0) ∧
      arrivals (pReady L (g / L.block) (d.i % 2)) ((X.tr (G.p0 (g / L.block))).take e0) ≤
        d.i / 2

/-- **The premise on the `P` stores after the S load.** A `P` store of a block `i' ≥ i` that
writes a cell the load of iteration `i` reads comes after the load (`ReadBefore .ld`): the S load
before the `P` store of the other half of the warp (the `bar.sync 0, 128` of the site `bar20`
between the load's `tcgen05.wait::ld` and the store; `Sr.PAliasSyncS`), and the later blocks'
stores of the thread and its partner follow by program order and the same rendezvous. -/
def SPstAfter (Q : Params) (L : Launch) (X : Execution) {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (G : SrPkg L K A mem0 X) : Prop :=
  ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape} {t sk i' a' : Nat}
    {vals' : List Value} {sh' : TcShape}, g < L.threads →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .ldS →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    PSt L X (g / L.block) (G.p0 (g / L.block)) (G.Soft (g / L.block)) (G.tm (g / L.block)) t sk
      i' a' vals' sh' → X.TSt (t, sk) a' vals' sh' → d.i ≤ i' →
    (∃ j j', j < 64 ∧ j' < vals'.length ∧
      tcDataCell L g (.s16x32bx2 64) a j = tcDataCell L t sh' a' j') →
    ReadBefore L X .ld (g, k) (t, sk)

/-- The softmax threads of a CTA are its default-partition threads. -/
def SoftAll (L : Launch) {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (G : SrPkg L K A mem0 X) : Prop :=
  ∀ c, c < L.grid → ∀ g, g < L.threads → g / L.block = c → g % L.block < 128 → G.Soft c g

/-- **Thread 0's events up to an arrival with at most `q` earlier arrivals are before the lane's
events after its `q + 1`-th poll of `p_ready`** (`SO.p_before_pv`). -/
theorem p0_before_lane {c cm p0 tm : Nat} {Soft Mma : Nat → Prop}
    (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma) (l : Lane L X c cm p0 tm Soft) {b : Nat}
    (hb : b < 2) {e f q : Nat} (he : arrivals (pReady L c b) ((X.tr p0).take e) ≤ q)
    (hf : q + 1 ≤ okPolls (pReady L c b) ((X.tr cm).take f)) (hfl : f < (X.tr cm).length) :
    baseCausality L X (p0, e) (cm, f) := by
  have hp0 := soft_info H H.route.p0_soft
  have hU := SO.p_handoff H.cons H.facts hb (cons := fun h => h = cm)
    (fun h hh => by subst hh; exact Mbar.pReach H hb H.route.cm_mma)
    (fun hh hw' => by subst hh; exact l.pAcq hb hw')
    (fun h hh => by subst hh; exact ⟨hp0.1, l.cm_ok.1, by rw [hp0.2.1, l.cm_ok.2]⟩)
  exact SO.p_before_pv hU rfl he hf hfl

/-- **`Sv.SLoadSrc`**: the softmax thread's S load of iteration `i` reads the QK MMA at step 7 of
iteration `i`. -/
theorem sLoadSrc_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hR : Interface.RoleReads L X)
    (hb : Interface.BaseWordRead L X) (hn : Interface.NumWordRead Q L X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (G : SrPkg L kernel Assumptions.all mem0 X) (st : Pr.MmaStates Q L G)
    (ht : Tmem1.Tmem1Facts L X 0) (hl : SO.TmemLife L X) (hz : Rs.SmBaseZero Q L X)
    (hSoft : SoftAll L G) (hrdv : SRdv Q L X G) (hpst : SPstAfter Q L X G) :
    Sv.SLoadSrc Q L X := by
  refine ⟨fun {g k pc a d vals sh} hg hvr hσ hs he => ?_⟩
  have hS := ProA.sharedOk_of_pre hpre
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
  obtain ⟨vals', hlen, hev⟩ := Sm.shape_ldS (Interface.fired_sm hF) hs
  have hev' := hev
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev
  obtain ⟨hpc, ha, hvv, hsh⟩ := hev
  subst ha hvv hsh
  -- the poll two events before
  obtain ⟨k2, d2, d1, e2, e1, hk2, he2, he1, hσ2, hs2, hi2, hw, hσ1, hs1, -⟩ :=
    Interface.ldS_back hX hf hg (by omega) hσ hs
  have hge2 : X.get (g, k2) = some e2 := he2
  obtain ⟨u2, hF2⟩ := Interface.fired_cont hX hf hg hge2 hσ2 (by simp [Interface.ExitState])
  obtain ⟨ok2, hev2⟩ := Sm.shape_waitS_loc hS (Interface.fired_sm hF2) hs2
  obtain ⟨l2, p2, a2, sc2, hk2e⟩ := hw
  have hok2 : ok2 = true := by
    rw [hev2] at hk2e
    simp only [Kind.wait.injEq] at hk2e
    exact hk2e.2.2.1
  subst hok2
  have hpoll : X.get (g, k2) = some ⟨Sm.evPc d2.site, .wait (sReady L (g / L.block) (d.i % 2))
      (d2.i / 2 % 2) true true .cta⟩ := by
    rw [hge2, hev2, SO.loc_sReadyOf, hi2]
  have hcnt := (sm_cnt hpre hX hf hg k2 (by omega) _ hσ2).2 d2 rfl
  have hq : okPolls (sReady L (g / L.block) (d.i % 2)) ((X.tr g).take k2) = d.i / 2 := by
    rw [hcnt.s _ hb2]
    have : SO.smPolled d2 = d2.i := by simp [SO.smPolled, hs2]
    rw [this, hi2]
    unfold SO.below2
    omega
  -- the commit the poll observes
  have hReach := Mbar.sReach H hb2 hsoft
  obtain ⟨ic, pcc, spc, rank, hgetc, hmbar, htgt, hcntc, hrank, hobs⟩ :=
    SO.s_observes H.cons H.facts hb2 hReach hpoll hq
  have hcm := l.cm_ok.1
  have hcmc := l.cm_ok.2
  have hickl : ic < (X.tr (G.cm (g / L.block))).length := len_of_get hgetc
  obtain ⟨dc, Pc, hσc, hshc⟩ := Interface.mma_event_state hpre hX hf.sound hf.tracked hcm hgetc
    (Or.inr ⟨spc, rfl⟩)
  have hsite : dc.site = .qkCommit :=
    site_of_scommit hb2 hshc (by rw [hcmc]; exact hmbar)
  have hlead : ElectLead L (G.cm (g / L.block)) (X.tr (G.cm (g / L.block))) :=
    Interface.lead_of_qkCommit hpre hX hf hickl hσc hsite
  have hcg : (G.cm (g / L.block)) / L.block = g / L.block := hcmc
  obtain ⟨dc', Pc', hσc', hsc', hi2', hdi⟩ := qk_commit_block hpre hX hf hR hlead hB hcm hb2 hgetc
    (by rw [hcg]; exact hmbar)
  have hdd : dc' = dc := by
    have := Option.some.inj (Option.some.inj (hσc'.symm.trans hσc))
    simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
    exact this.1
  subst hdd
  rw [hcg, hcntc] at hdi
  have hdci : dc'.i = d.i := by
    unfold SO.blockB at hdi
    omega
  -- the last QK MMA
  obtain ⟨k', dm, hadj, hσm, hs7, hi7, htmc, hnm, pcm, dst, spm, acc, mask, hevm⟩ :=
    Interface.exists_qk7 hpre hX hf hickl hσc hsite
  have hmEvt : IsMma X (G.cm (g / L.block), k') := ⟨dst, spm, acc, mask, pcm, hevm⟩
  have hdm0 : dm.tm = 0 :=
    Interface.mma_tm hpre hX hf hb hn (m := (G.cm (g / L.block), k')) ⟨_, hσm⟩
  have hd0 : d.e.tm = 0 := hz hg hσ
  have hlenm : k' < (X.tr (G.cm (g / L.block))).length := len_of_get hevm
  have hQm := st.qk hcm hlenm hσm hs7
  rw [hcmc] at hQm
  -- the cells
  obtain ⟨hqo, hdst, -, hmask, -⟩ := qk_event hpre hX hf hcm hevm hσm hs7
  have hT : g % L.block < 128 := hdef
  have hte : Sm.tileAddr L g d = d.e.tm + 128 * (d.i % 2) + g % L.block / 32 * 2 ^ 21 :=
    Sm.tileAddr_eq hT (by omega) (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
  have hlcell : ∀ j, tcDataCell L g (.s16x32bx2 64) (Sm.tileAddr L g d) j =
      sCell (g / L.block) dm.tm dm.i (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) := by
    intro j
    rw [hte, hd0, hdm0, hi7, hdci]
    exact Sv.ldS_cell L g (by omega) j
  refine ⟨(G.cm (g / L.block), k'), pcm, dst, spm, acc, mask, dm, Pc, hcm, hcmc, hevm, hσm,
    hs7, by rw [hi7, hdci], by rw [hd0, hdm0], ?_⟩
  intro j hj
  rw [hlcell j]
  set cell : Cell := sCell (g / L.block) dm.tm dm.i (Sm.row (g % L.block))
    (64 * Sm.half (g % L.block) + j) with hcelldef
  have hrow : Sm.row (g % L.block) < 64 := by unfold Sm.row; omega
  have hcol : 64 * Sm.half (g % L.block) + j < 128 := by unfold Sm.half; omega
  have hwc : writeCell spm dst mask (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) =
      some cell := by
    rw [hdst, hmask]
    have := qk_writeCell (sp := spm) hqo.desc (cta := g / L.block) (tm := dm.tm)
      (i := dm.i) (hqo.low.trans hcmc) (by omega) hrow hcol
    simpa using this
  have hmc : X.MmaCell (G.cm (g / L.block), k') cell :=
    ⟨_, _, _, _, _, _, ⟨pcm, hevm⟩, hwc⟩
  obtain ⟨jy, pcy, ey, hgy, hqy⟩ := hQm.issue
  obtain ⟨hIS, hcta⟩ := SO.qk_cells l.tmOk hqy hgy hmc
  have ix : WInfo L X (g / L.block) (G.cm (g / L.block)) (G.p0 (g / L.block))
      (G.tm (g / L.block)) (G.Soft (g / L.block)) (G.cm (g / L.block), k') cell :=
    .qk hQm hIS hcta
  -- the source is done before the load
  have hmi : dm.i = d.i := hi7.trans hdci
  have hIS' : InS (G.tm (g / L.block)) (d.i % 2) cell.column := by rw [← hmi]; exact hIS
  have hbcl : baseCausality L X (g, k2) (g, k) :=
    SO.baseCausality_src hpoll rfl rfl (by omega) hk
  have hdone : DoneBefore L X (G.cm (g / L.block), k') (g, k) :=
    s_doneBefore_to H hb2 ⟨hcm, hg, by rw [hcmc]⟩ hone hReach hpoll hq hmEvt hcmc
      (le_trans (countP_take_mono _ _ (show k' ≤ ic by omega)) (le_of_eq hcntc)) hbcl
  refine ⟨?_, .inl hmc, .inl (.inl hdone), ?_, ?_⟩
  · -- the source is not the load
    intro hh
    have hh1 : G.cm (g / L.block) = g := congrArg Prod.fst hh
    have hh2 : k' = k := congrArg Prod.snd hh
    subst hh2
    rw [hh1] at hσm
    rw [hσ] at hσm
    cases Option.some.inj (Option.some.inj hσm)
  · -- every other writer of the cell is before the QK MMA or after the load
    intro other hw'
    have hol := cta_lt hX (write_event hnc hns hw')
    have iy := winfo hnc hns (G.lane _ hol) hw' rfl
    have hxy : other.1 / L.block = g / L.block := iy.cta.symm.trans ix.cta
    rw [hxy] at iy
    cases iy with
    | @qk _ _ i' hq' h1' _ =>
      have hpar : d.i % 2 = i' % 2 := inS_parity hIS' h1'
      have hpar' : dm.i % 2 = i' % 2 := by rw [hmi]; exact hpar
      rcases Nat.lt_trichotomy other.2 k' with hlt | heq | hgt
      · exact .inr (.inl (.inl (qk_before l.cm_ok.1 hq' hQm hpar'.symm hlt)))
      · exact .inl (Prod.ext hq'.thread heq)
      · -- a later QK MMA: it follows the load through thread 0's arrival
        right; right; left
        obtain ⟨pcq, dq, sq, aq, mq, hgq⟩ := hq'.isMma.get
        have hic : other.2 ≠ ic := by
          intro hh
          have hother : other = (G.cm (g / L.block), ic) := Prod.ext hq'.thread hh
          rw [hother] at hgq
          have h := Option.some.inj (hgetc.symm.trans hgq)
          simp only [Event.mk.injEq, Kind.tc.injEq] at h
          cases h.2
        have hgt2 : ic + 1 ≤ other.2 := by omega
        have hc1 := countP_take_succ (p := commitsTo (sReady L (g / L.block) (d.i % 2)))
          hgetc (by simp [commitsTo, hmbar])
        have hc2 := countP_take_mono (commitsTo (sReady L (g / L.block) (d.i % 2)))
          (X.tr (G.cm (g / L.block))) hgt2
        have hsc := hq'.sCommits
        rw [← hpar] at hsc
        have hpp := hq'.pPolls
        rw [← hpar] at hpp
        have hlen2 : other.2 < (X.tr (G.cm (g / L.block))).length := lane_len hq'.thread hgq
        obtain ⟨wl, pcw, e0, hlw, hwl, hbc0, harr⟩ := hrdv hg hσ hs he
        have hp0 := p0_before_lane H l hb2 harr (f := other.2) (by omega) hlen2
        have hx : other = (G.cm (g / L.block), other.2) := Prod.ext hq'.thread rfl
        rw [hx]
        exact ⟨(g, wl), ⟨pcw, hwl⟩, rfl, hlw, .inl (hbc0.trans hp0)⟩
    | @pv _ _ m' hv' h1' _ =>
      exact absurd h1' (SO.inS_inO_disjoint hb2 hIS')
    | @pst t sk i' w j' a' vals'' sh'' cell' hst hp hjs ha hc' hin _ =>
      have hpar : d.i % 2 = i' % 2 := inS_parity hIS' (SO.inP_inS hin)
      by_cases hle : d.i ≤ i'
      · right; right
        obtain ⟨hsh'', hl'', -⟩ := hp.shape
        subst hsh''
        exact hpst hg hσ hs he hp hst hle ⟨j, j', hj, by omega, (hlcell j).trans hc'⟩
      · right; left
        have hpar' : dm.i % 2 = i' % 2 := by rw [hmi]; exact hpar
        have hnot : ¬ dm.i / 2 ≤ i' / 2 := by rw [hmi]; omega
        exact .inr (.inl (qk_pst_B H l hQm hp hst hpar' hnot))
    | @ost t sk i' w j' a' vals'' sh'' cell' hst ho hj ha hc' hin _ =>
      exact absurd hin (SO.inS_inO_disjoint hb2 hIS')
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

end
end PTX.Kernels.InklingRelDecode.Proof.Rd
