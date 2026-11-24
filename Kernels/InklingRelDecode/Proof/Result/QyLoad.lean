-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Result.KkAll
public import Kernels.InklingRelDecode.Proof.Result.QxAll
public import Kernels.InklingRelDecode.Proof.Interface.QyLayer
public import Kernels.InklingRelDecode.Proof.Result.QyElems

@[expose] public section

/-!
# The read sources of the softmax region's loads on every consistent execution (`ldSm`)

`Rd.sLoadSrc_of` and `Rd.oLoadSrc_of` name the read sources of the S load and the rescale load
for valid rows, from premises (`Rd.SRdv`, `Rd.SPstAfter`, `Rd.ORdv`) that `Rr.sRdv_of`,
`Kk.sPstAfter_of`, `Kk.oRdv_of` prove from `Complete L X`; `oLoadSrc_of` also uses `Complete` for
the wait after the load (`Interface.ldO_wait`) and for the uniqueness of the source. Neither proof
uses the row's validity. Here, on every consistent execution and for every row:

* `sPstAfterF`: `Rd.SPstAfter` itself. The later `P` store's thread has passed its `bar20` of the
  load's iteration (the store's state is at or after `tmemSt` of that iteration); the load's
  thread has the barrier-0 event of the same count (`Lk.member_of`, `Qy.exit_bound20`,
  `Qy.b128_of20`), which comes after the load and its wait by the counts; `Bar.bar128Causal`.
* the rendezvous is needed only for a later MMA that writes a cell the load reads: that MMA's
  polls of `p_ready` bound thread 0's arrivals from below (`Qy.arrivals_of_polls`), so the
  guarded rendezvous `Px.ldRdv_of` applies;
* the wait after the rescale load is needed only for a later rescale store of the thread, whose
  event comes after it (`Vx.ld_wait_after`).

The value of each source is its MMA's `f32` result (`Qx.ldSource_result`), so `ldSm_of` proves
`Qy.LdSmRest` from `Qx.ResultF32`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N (cnt0 C0 Dc nIt)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Rd.SPstAfter` on every consistent execution**: a `P` store of a block `i' ≥ i` of the CTA
comes after the S load of iteration `i`. -/
theorem sPstAfterF (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hD : ∀ c j, DecAgree Q L X c j) {K : Kernel}
    {A : List Assumption} (G : SrPkg L K A mem0 X) : Rd.SPstAfter Q L X G := by
  intro g k pc a d vals sh t sk i' a' vals' sh' hg hσ hs he hP hT hii _
  have hI := Sv.sm_inv_at hX hf he hσ
  have hdef : g % L.block < 128 := hI.tid
  have hlt : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    rw [← Rr.r26_eq hpre hX hf hg he hσ]
    exact (hI.late (by rw [hs]; trivial)).2.2
  have hk : k ≤ (X.tr g).length := (len_of_get he).le
  -- the storing thread and the state of its store
  obtain ⟨ht, htc, htd⟩ := hP.gate.soft
  obtain ⟨pcs, hget⟩ := hT
  obtain ⟨hsh, -, -⟩ := hP.shape
  subst hsh
  have hne : ∀ pc' f, (⟨pcs, .tc (.st a' vals' (.s16x32bx2 32))⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
    intro pc' f h
    simp only [Event.mk.injEq] at h
    cases h.2
  obtain ⟨s, hσs⟩ := Frame.event_state hf.sound hX hf.tracked hget hne
  obtain ⟨dt, rfl, hst⟩ := Interface.tcst_event_state hf.sound hX hget hσs
  have hsT : dt.site = .tmemSt := by
    rcases hst with h | h
    · exact h
    · exfalso
      obtain ⟨u', hF'⟩ := Interface.fired_cont hX hf ht hget hσs (by simp [Interface.ExitState])
      obtain ⟨vals2, -, -, -, hev2⟩ := Sm.shape_stO (Interface.fired_sm hF') h
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev2
      obtain ⟨-, -, -, hsh2⟩ := hev2
      simp at hsh2
  have hsk : sk ≤ (X.tr t).length := (len_of_get hget).le
  -- the store's iteration is at least `i'`
  have hjt : i' ≤ dt.i := by
    obtain ⟨jp, pcp, p, sc, hjp, hwp, hqp⟩ := hP.gate.poll
    have hb2 : i' % 2 < 2 := Nat.mod_lt _ (by omega)
    have hcnt := ((Rd.sm_cnt hpre hX hf ht sk hsk _ hσs).2 dt rfl).s (i' % 2) hb2
    have hwp' : (X.tr t)[jp]? =
        some ⟨pcp, .wait (sReady L (g / L.block) (i' % 2)) p true true sc⟩ := hwp
    have hp1 := Rd.okPolls_take_succ (sReady L (g / L.block) (i' % 2)) hwp'
    have hok : okPoll (sReady L (g / L.block) (i' % 2))
        ⟨pcp, .wait (sReady L (g / L.block) (i' % 2)) p true true sc⟩ = true := by
      simp [okPoll, sourceWaitSuccess]
    simp only [hok, ↓reduceIte] at hp1
    have hm := Rd.okPolls_mono (sReady L (g / L.block) (i' % 2)) (X.tr t)
      (show jp + 1 ≤ sk by omega)
    rw [htc] at hcnt
    simp only [SO.smPolled, hsT, SO.below2] at hcnt
    omega
  have hct : t / L.block = g / L.block := htc
  have hltt : d.i < Q.numIters (ProA.cta L t .z) (ProA.cta L t .x) := by
    rw [ProA.cta_eq_of_block hct .z, ProA.cta_eq_of_block hct .x]
    exact hlt
  -- the storing thread's `bar20` of iteration `i`, before the store
  obtain ⟨yb, db, pcb, hyl, hσb, hsb, hib, heb⟩ : ∃ (yb : Nat) (db : Sm.D) (pcb : Nat), yb < sk ∧
      St Q L X t yb = some (some (.d (.sm db))) ∧ db.site = .bar20 ∧ db.i = d.i ∧
      X.get (t, yb) = some ⟨pcb, .bar 0 (some 128) .sync⟩ := by
    rcases Nat.lt_or_eq_of_le (show d.i ≤ dt.i by omega) with hlt' | heq
    · obtain ⟨k', d', hk', hσ', hs', hi'⟩ :=
        Interface.bar21_back (g := t) d.i sk hsk hσs (Or.inl hlt')
      rcases Sv.pred_sm (by omega) hσ' with ⟨dz, rfl⟩ | ⟨k1, d1, e1, rfl, -, hσ1, hn1⟩
      · simp [SmEntry.d0] at hs'
      obtain ⟨hs1, hi1⟩ := Interface.next_bar21 hn1 hs'
      rcases Sv.pred_sm (by omega) hσ1 with ⟨dz, rfl⟩ | ⟨k2, d2, e2, rfl, -, hσ2, hn2⟩
      · simp [SmEntry.d0] at hs1
      obtain ⟨hs2, hi2⟩ := Interface.next_tmemWait hn2 hs1
      obtain ⟨kB, dB, pc, hkB, hσB, hsB, hiB, heB⟩ :=
        Interface.Kk.bar20_before hpre hX hf ht (by omega) hσ2 hs2
      exact ⟨kB, dB, pc, by omega, hσB, hsB, by omega, heB⟩
    · obtain ⟨kB, dB, pc, hkB, hσB, hsB, hiB, heB⟩ :=
        Interface.Kk.bar20_before hpre hX hf ht hsk hσs hsT
      exact ⟨kB, dB, pc, by omega, hσB, hsB, by omega, heB⟩
  have hyb : yb ≤ (X.tr t).length := by omega
  have hinb : db.i < nIt Q L t := by
    show db.i < Q.numIters (ProA.cta L t .z) (ProA.cta L t .x)
    omega
  -- the load's thread has the barrier-0 event of the same count
  have hIsB : X.IsBarrier (t, yb) 0 (some 128) pcb := heb
  obtain ⟨a0, pca, cna, hba, hcnta⟩ := Interface.Lk.member_of hpre hX hf hIsB
    (show yb + 1 < (X.tr t).length by have : sk < (X.tr t).length := len_of_get hget; omega)
    (by simpa using htd)
    (show g / L.block = (t, yb).1 / L.block from hct.symm) hdef
    (fun hj => exit_bound20 hpre hX hf hD ht hyb hσb hsb hinb hct.symm hdef hj)
  have hcn := b128_of20 hpre hX hf hD ht hyb hσb hsb hinb hct.symm hdef hba hcnta
  subst hcn
  have hba' : X.get (g, a0) = some ⟨pca, .bar 0 (some 128) .sync⟩ := hba
  have hal : a0 < (X.tr g).length := len_of_get hba'
  -- the counts put the load before that event
  have hv := Hs.cnt_at hpre hX hf hD hg hk hσ
  have hvb := Hs.cnt_at hpre hX hf hD ht hyb hσb
  have hC : C0 Q L t = C0 Q L g := by simp only [C0, Interface.B0N.nbQ_cta (Q := Q) hct]
  have hDc : Dc Q L X (t / L.block) = Dc Q L X (g / L.block) := by rw [hct]
  rw [hC, hDc] at hvb
  have hRD := Hs.rd_ge (Dc Q L X (g / L.block)) db
  have hRDd : RD (Dc Q L X (g / L.block)) d = nResc (Dc Q L X (g / L.block)) d.i := by
    simp [RD, postR, hs]
  have hRD' : ((nResc (Dc Q L X (g / L.block)) d.i : Nat) : Int) ≤
      ((RD (Dc Q L X (g / L.block)) db : Nat) : Int) := by rw [← hib]; exact_mod_cast hRD
  have hle : (cnt0 X g k : Int) ≤ cnt0 X g a0 := by
    have hcnta' : (cnt0 X g a0 : Int) = cnt0 X t yb := by exact_mod_cast hcnta
    rw [hcnta', hvb, hv, hRDd, hsb, hs]
    simp only [phi]
    split_ifs <;> omega
  have hka : k < a0 := by
    by_contra hge
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt2 | heq2
    · have h1 := Hs.cnt0_le (X := X) g (show a0 + 1 ≤ k by omega)
      rw [Hs.cnt0_succ hba'] at h1
      simp [Execution.isBarId] at h1
      omega
    · subst heq2
      rw [he] at hba'
      cases hba'
  -- the wait after the load
  obtain ⟨d', hσ', hs', -⟩ := Interface.ldS_succ hX hf hg he hσ hs
    ⟨a0, pca, _, hka, hba', fun f h => by cases h⟩
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k + 1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem (show k + 1 < (X.tr g).length by omega)⟩
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he1 hσ' (by simp [Interface.ExitState])
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  have hev := Sm.shape_waitLd hblk (Interface.fired_sm hF) hs'
  rw [hev] at he1
  have hwB : k + 1 < a0 := by
    rcases Nat.lt_or_eq_of_le (show k + 1 ≤ a0 by omega) with h | h
    · exact h
    · subst h
      rw [he1] at hba'
      cases hba'
  have hB := Bar.bar128Causal hpre hX hf.sound hf.tracked (g := g) (p := t) (a := a0) (y := yb)
    (before := k + 1) (f := sk) hg ht hct.symm hdef htd hba' heb hcnta hwB hyl (len_of_get hget)
  exact .inl ⟨(g, k + 1), ⟨_, he1⟩, rfl, by simp, .inl hB⟩

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : Interface.RoleReads L X)
  (hb : Interface.BaseWordRead L X) (hn : Interface.NumWordRead Q L X)
  (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
  (G : SrPkg L kernel Assumptions.all mem0 X) (hG : ∀ c, G.p0 c = Hs.p0Of L c)
  (st : Pr.MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hl : SO.TmemLife L X)
  (hz : Rs.SmBaseZero Q L X) (hD : ∀ c j, DecAgree Q L X c j) (hMB : Mma.MmaBcast L X)
include hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB

/-- **The S load of iteration `i` reads the QK MMA at step 7 of iteration `i`**, every row, every
consistent execution (`Rd.sLoadSrc_of` without the row's validity and without `Complete`). -/
theorem sLoadSrcF {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}
    (hg : g < L.threads) (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldS)
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .qk 7 ∧ dm.i = d.i ∧
      d.e.tm = dm.tm ∧
      ∀ j < 64, ReadSource L X .ld m (g, k) (tcDataCell L g (.s16x32bx2 64) a j) := by
  have hS := ProA.sharedOk_of_pre hpre
  have hk : k < (X.tr g).length := len_of_get he
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  have hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = g / L.block → x.1 = G.cm (g / L.block) :=
    fun hx hc => l.mma_thread hx hc
  have hdef : g % L.block < 128 := (hf.reach hg hσ).1
  have hsoft : G.Soft (g / L.block) g := ⟨hg, rfl, hdef⟩
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
  have hcnt := (Rd.sm_cnt hpre hX hf hg k2 (by omega) _ hσ2).2 d2 rfl
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
    Rd.site_of_scommit hb2 hshc (by rw [hcmc]; exact hmbar)
  have hlead : ElectLead L (G.cm (g / L.block)) (X.tr (G.cm (g / L.block))) :=
    Interface.lead_of_qkCommit hpre hX hf hickl hσc hsite
  have hcg : (G.cm (g / L.block)) / L.block = g / L.block := hcmc
  obtain ⟨dc', Pc', hσc', hsc', hi2', hdi⟩ := Rd.qk_commit_block hpre hX hf hR hlead hMB hcm hb2
    hgetc (by rw [hcg]; exact hmbar)
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
        have hq1 : d.i / 2 + 1 ≤ okPolls (pReady L (g / L.block) (d.i % 2))
            ((X.tr (G.cm (g / L.block))).take other.2) := by omega
        have hgd := arrivals_of_polls H l hb2 hq1
        rw [hG] at hgd
        obtain ⟨pcw, e0, hwl, hbc0, harr⟩ :=
          Px.ldRdv_of hpre hX hf hD (g / L.block) hg rfl hσ (Or.inl hs) he hgd
        rw [← hG] at hbc0 harr
        have hp0 := Rd.p0_before_lane H l hb2 harr (f := other.2) hq1 hlen2
        have hx : other = (G.cm (g / L.block), other.2) := Prod.ext hq'.thread rfl
        rw [hx]
        exact ⟨(g, k + 1), ⟨pcw, hwl⟩, rfl, Nat.lt_succ_self k, .inl (hbc0.trans hp0)⟩
    | @pv _ _ m' hv' h1' _ =>
      exact absurd h1' (SO.inS_inO_disjoint hb2 hIS')
    | @pst t sk i' w j' a' vals'' sh'' cell' hst hp hjs ha hc' hin _ =>
      have hpar : d.i % 2 = i' % 2 := inS_parity hIS' (SO.inP_inS hin)
      by_cases hle : d.i ≤ i'
      · right; right
        obtain ⟨hsh'', hl'', -⟩ := hp.shape
        subst hsh''
        exact sPstAfterF hpre hX hf hD G hg hσ hs he hp hst hle
          ⟨j, j', hj, by omega, (hlcell j).trans hc'⟩
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

/-- **The rescale load of iteration `i` reads the PV MMA at step 7 of iteration `i`**, every row,
every consistent execution (`Rd.oLoadSrc_of` without the row's validity, without `Complete` and
without the uniqueness of the source). -/
theorem oLoadSrcF {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}
    (hg : g < L.threads) (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldO)
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .pv 7 ∧ dm.i = d.i ∧
      ∀ j < 64, ReadSource L X .ld m (g, k) (tcDataCell L g (.s16x32bx2 64) a j) := by
  have hS := ProA.sharedOk_of_pre hpre
  have hW := Rd.waitOShape_of hS
  have hk : k < (X.tr g).length := len_of_get he
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  have hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = g / L.block → x.1 = G.cm (g / L.block) :=
    fun hx hc => l.mma_thread hx hc
  have hdef : g % L.block < 128 := (hf.reach hg hσ).1
  have hsoft : G.Soft (g / L.block) g := ⟨hg, rfl, hdef⟩
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
  have hcnt := (Rd.sm_cnt hpre hX hf hg kp (by omega) _ hσp).2 dp rfl
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
    Rd.site_of_ocommit hshc (by rw [hcmc]; exact hmbar)
  obtain ⟨hlead, k', dm, d1, hadj, hσm, hs7, hi7, htmc, hnm, hσ1, hs1, pcm, dst, spm, acc, mask,
    hevm⟩ := Interface.exists_pv7_commit2 hpre hX hf hickl hσc hsite
  have hcg : (G.cm (g / L.block)) / L.block = g / L.block := hcmc
  obtain ⟨dc', Pc', hσc', hsc', hdi⟩ := Rd.o_commit_block hpre hX hf hR hlead hMB hcm hgetc
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
    hs7, hmi, ?_⟩
  intro j hj
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
  have hdone : DoneBefore L X (G.cm (g / L.block), k') (g, k) :=
    SO.o_doneBefore H.cons H.facts H.opar hone ⟨hcm, hg, by rw [hcmc]⟩ hReach hpoll hq hmEvt
      hcmc (le_trans (countP_take_mono _ _ (show k' ≤ ic by omega)) (le_of_eq hcntc)) hkp hk
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
        have hq1 : d.i / 2 + 1 ≤ okPolls (pReady L (g / L.block) (d.i % 2))
            ((X.tr (G.cm (g / L.block))).take other.2) := by omega
        have hgd := arrivals_of_polls H l hb2 hq1
        rw [hG] at hgd
        obtain ⟨pcw, e0, hwl, hbc0, harr⟩ :=
          Px.ldRdv_of hpre hX hf hD (g / L.block) hg rfl hσ (Or.inr hs) he hgd
        rw [← hG] at hbc0 harr
        have hp0 := Rd.p0_before_lane H l hb2 harr (f := other.2) hq1 hlen2
        have hx : other = (G.cm (g / L.block), other.2) := Prod.ext hv'.thread rfl
        rw [hx]
        exact ⟨(g, k + 1), ⟨pcw, hwl⟩, rfl, Nat.lt_succ_self k, .inl (hbc0.trans hp0)⟩
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
      by_cases hafter : k < sk
      · -- the store follows the load and its wait in the thread's program order
        obtain ⟨pcw, hwait⟩ := Vx.ld_wait_after hpre hX hf hg
          ⟨sk, pcs, _, hafter, hgets, fun f h => by cases h⟩ he
        have hne_w : sk ≠ k + 1 := by
          intro hh
          subst hh
          rw [hwait] at hgets
          simp at hgets
        right; right; left
        exact ⟨(g, k + 1), ⟨pcw, hwait⟩, rfl, Nat.lt_succ_self k,
          .inl (baseCausality_of_tc_po hwait rfl (by omega) hlens)⟩
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
        have hcs := (Rd.sm_cnt hpre hX hf ht' sk hlens.le _ hσs).2 ds rfl
        obtain ⟨jg, pcg, pg, scg, hjg, hgetg, hqg⟩ := ho.gate.poll
        have hlj : (X.tr g)[jg]? = some ⟨pcg, .wait (oDone L (g / L.block)) pg true true scg⟩ :=
          hgetg
        have hc3 : okPolls (oDone L (g / L.block)) ((X.tr g).take (jg + 1)) = i' - 1 + 1 := by
          rw [Rd.okPolls_take_succ _ hlj, hqg]
          simp [okPoll_wait (rfl : (⟨pcg, .wait (oDone L (g / L.block)) pg true true scg⟩ :
            Event) = _)]
        have hc4 := Rd.okPolls_mono (oDone L (g / L.block)) (X.tr g) (show jg + 1 ≤ sk by omega)
        rw [hcs.o] at hc4
        have hsmo : SO.smOPolled ds = ds.i := by simp [SO.smOPolled, hds]
        have hc5 := Rd.okPolls_mono (oDone L (g / L.block)) (X.tr g) (show sk ≤ kp by omega)
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

/-- **`Qy.LdSmRest`** (`Qx.SourceRest.ldSm`): every register of a load of the softmax region has
a read source with a value: the QK or PV MMA at step 7 of the load's iteration
(`sLoadSrcF`, `oLoadSrcF`), whose result at the cell is an `f32` number (`Qx.ldSource_result`). -/
theorem ldSm_of (hres : Qx.ResultF32 L X) : LdSmRest Q L X := by
  intro g k pc a j vals sh d cell hg he hσ hlc
  obtain ⟨a', vals', sh', ⟨pc', he'⟩, hj, hcell⟩ := hlc
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at he'
  obtain ⟨-, rfl, rfl, rfl⟩ := he'
  obtain ⟨hsh, hlen, hcase⟩ := Interface.Lk.tcld_event hpre hX hf hg he
  subst hsh
  rw [hlen] at hj
  have hsite : d.site = .ldS ∨ d.site = .ldO := by
    rcases hcase with ⟨d', hσ', hs'⟩ | ⟨d', hσ', -⟩
    · rw [hσ] at hσ'
      simp only [Option.some.injEq, Interface.TSt.d.injEq, DComp.St.sm.injEq] at hσ'
      subst hσ'
      rcases hs' with ⟨h, -⟩ | ⟨h, -⟩
      · exact .inl h
      · exact .inr h
    · rw [hσ] at hσ'
      simp at hσ'
  have hsrc : ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool)
      (mask : List Nat), m.1 < L.threads ∧ X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      ReadSource L X .ld m (g, k) (tcDataCell L g (.s16x32bx2 64) a j) := by
    rcases hsite with hs | hs
    · obtain ⟨m, pcm, dst, sp, acc, mask, -, -, hml, -, hem, -, -, -, -, hrs⟩ :=
        sLoadSrcF hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hg hσ hs he
      exact ⟨m, pcm, dst, sp, acc, mask, hml, hem, hrs j hj⟩
    · obtain ⟨m, pcm, dst, sp, acc, mask, -, -, hml, -, hem, -, -, -, hrs⟩ :=
        oLoadSrcF hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hg hσ hs he
      exact ⟨m, pcm, dst, sp, acc, mask, hml, hem, hrs j hj⟩
  obtain ⟨⟨mg, mk⟩, pcm, dst, sp, acc, mask, hml, hem, hrs⟩ := hsrc
  obtain ⟨x, hx⟩ := Qx.ldSource_result hX hres hml hem he hrs
  exact ⟨_, _, by rw [hcell]; exact hrs, by rw [hcell]; exact .inl hx⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
