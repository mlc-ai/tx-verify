-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.SwPTile
public import Kernels.InklingRelDecode.Proof.Result.PrChain
public import Kernels.InklingRelDecode.Proof.Interface.KkTmemSt
public import Kernels.InklingRelDecode.Proof.Result.RdSLoad

@[expose] public section

/-!
# The read source of the `P` tile's cells (`Rs.PReadSrc`)

The A operand of PV MMA `j` of iteration `i ≥ 1` reads the cell `(r, w)` of `P ((i - 1) % 2)`.
Its source is the `P` store of iteration `i - 1` of one softmax thread:

* `cover`: the thread `32 (r / 16) + 16 (w / 32) + r % 16` of the CTA writes the cell with its
  register `w % 32` (`Sr.cell_split`);
* the thread reaches `tmemSt` of iteration `i - 1` (`Interface.sm_reaches_tmemSt`); the package's
  coordinate of that store is its loop counter (`pst_iter`, from the poll counts that `Sr.PSt`
  carries), so its gate is the iteration's and `Sr.store_before_mma` orders it before the MMA;
* every other writer of the cell (`Sr.winfo`): a QK MMA of a block up to `i - 1` is done before
  the store (`Sr.qk_pst_A`), a later one is after the A read (the pipelined pair
  `SO.aRead_before_later_mma`); a `P` store is the same thread's (`Sr.split_thread`), the source
  itself in iteration `i - 1` (`Interface.Kk.tmemSt_unique`), pipelined before it in an earlier
  iteration (`StoreDoneBefore.of_po`), after the MMA in a later one (`Sr.mma_before_s_store`);
  PV MMAs and rescale stores write other columns;
* `SourceLive` from `Tmem1.MmaDoneDealloc` (`Pr.sourceLive_mma`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Kk
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The thread that writes cell `(r, w)` of a `P` buffer**, with its register `w % 32`. -/
theorem cover (hblk : L.block = 256) {tm b r w : Nat} (hT : TmOk tm) (hb : b < 2) (hr : r < 64)
    (hw : w < 64) (c : Nat) :
    ∃ t, t / L.block = c ∧ t % L.block < 128 ∧ ∀ w0 : Nat,
      tcDataCell L t (.s16x32bx2 32) (tm + 128 * b + w0 * 2 ^ 21) (w % 32) =
        ⟨c, r % 16 + 32 * (r / 16), tm + 128 * b + w⟩ := by
  refine ⟨c * L.block + (32 * (r / 16) + 16 * (w / 32) + r % 16), ?_, ?_, fun w0 => ?_⟩
  · rw [hblk]; omega
  · rw [hblk]; omega
  · have hba : tm + 128 * b + 32 < 2 ^ 16 := by unfold TmOk at hT; omega
    rw [cell_split L _ _ 32 w0 (w % 32) hba]
    simp only [TcMma.Cell.mk.injEq]
    unfold laneOf
    rw [hblk]
    refine ⟨by omega, by omega, ?_⟩
    split_ifs <;> omega

/-- **The coordinate of a `P` store is the softmax state's loop counter**: the state at the store
is at `tmemSt`, and its successful polls of `s_ready b` (`Rd.sm_cnt`) are the store's. -/
theorem pst_iter (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c p0 tm t sk i a : Nat} {Soft : Nat → Prop}
    {vals : List Value} {sh : TcShape} (hP : PSt L X c p0 Soft tm t sk i a vals sh)
    (ht : t < L.threads) (htc : t / L.block = c) :
    ∃ d : Sm.D, St Q L X t sk = some (some (.d (.sm d))) ∧ d.site = .tmemSt ∧ d.i = i := by
  obtain ⟨hsh, -, -⟩ := hP.shape
  subst hsh
  obtain ⟨pcs, hget⟩ := hP.event
  have hne : ∀ pc' f, (⟨pcs, .tc (.st a vals (.s16x32bx2 32))⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
    intro pc' f h
    simp only [Event.mk.injEq] at h
    cases h.2
  obtain ⟨s, hσs⟩ := Frame.event_state hf.sound hX hf.tracked hget hne
  obtain ⟨d, rfl, hst⟩ := Interface.tcst_event_state hf.sound hX hget hσs
  have hsT : d.site = .tmemSt := by
    rcases hst with h | h
    · exact h
    · exfalso
      obtain ⟨u', hF'⟩ := Interface.fired_cont hX hf ht hget hσs (by simp [Interface.ExitState])
      obtain ⟨vals2, -, -, -, hev2⟩ := Sm.shape_stO (Interface.fired_sm hF') h
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev2
      obtain ⟨-, -, -, hsh2⟩ := hev2
      simp at hsh2
  have hk : sk ≤ (X.tr t).length := (len_of_get hget).le
  have hS := ((Rd.sm_cnt hpre hX hf ht sk hk _ hσs).2 d rfl).s
  have h0 := hS 0 (by omega)
  have h1 := hS 1 (by omega)
  have p0 := hP.polls 0 (by omega)
  have p1 := hP.polls 1 (by omega)
  rw [htc] at h0 h1
  rw [h0] at p0
  rw [h1] at p1
  refine ⟨d, hσs, hsT, ?_⟩
  simp only [SO.smPolled, hsT, SO.below2] at p0 p1
  omega

/-- **`Rs.PReadSrc`**: the A read of a PV MMA takes each cell of `P` from the `P` store of the
previous iteration of the softmax thread that covers it. -/
theorem pReadSrc_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hcomp : Complete L X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (G : SrPkg L kernel Assumptions.all mem0 X) (st : Pr.MmaStates Q L G)
    (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X) : Rs.PReadSrc Q L X := by
  refine ⟨?_⟩
  intro g k d P j r w hσ hs hi1 hr hw1 hw2
  obtain ⟨hg, hk⟩ := Interface.mma_state_lt hX hf hcomp hσ
  obtain ⟨e, he0⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he0⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  obtain ⟨pc, dst, sp, acc, mask, hev⟩ :=
    Interface.mma_issue_event hpre hX hf hg he0 hσ (.inr ⟨j, hs⟩)
  rw [hev] at he0
  have hmE : IsMma X (g, k) := ⟨dst, sp, acc, mask, pc, he0⟩
  have hgcm : g = G.cm (g / L.block) := l.mma_thread hmE rfl
  have hpv := (st.pv hg hk hσ hs).2
  obtain ⟨-, hdst, -, -, hinv⟩ := pv_event hpre hX hf hg he0 hσ hs
  have htmG : G.tm (g / L.block) = d.tm := by
    have := Rs.pvAt_dst hpv he0
    omega
  have hiter : d.i - 1 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    have h1 := hinv.pv (by rw [hs]; trivial)
    have h2 := Interface.mma_iters_loop hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩
      (.inr (by rw [hs]; trivial))
    simp only [reqOf, splitOf] at h2
    omega
  have hrow : r < 64 := by have := hr.1; omega
  have hw64 : w < 64 := by have := j.isLt; omega
  have hb2 : (d.i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  -- the covering thread and its store of iteration `i - 1`
  obtain ⟨t, htc, htd, hcov⟩ := cover hpre.block l.tmOk hb2 hrow hw64 (g / L.block)
  have hpos : 0 < L.block := by have := hpre.block; omega
  have htl : t < L.threads := by
    have h1 := (Nat.div_lt_iff_lt_mul hpos).mp (htc ▸ hcl : t / L.block < L.grid)
    unfold Launch.threads
    exact h1
  have hct : t / L.block = g / L.block := htc
  have hitt : d.i - 1 < Q.numIters (ProA.cta L t .z) (ProA.cta L t .x) := by
    rw [ProA.cta_eq_of_block hct .z, ProA.cta_eq_of_block hct .x]
    exact hiter
  obtain ⟨ks, ds, pcs, a, vals, hσs, hss, his, hget, -⟩ :=
    Interface.sm_reaches_tmemSt hpre hX hf hcomp htl htd hitt
  have hT : X.TSt (t, ks) a vals (.s16x32bx2 32) := ⟨pcs, hget⟩
  have hks : ks ≤ (X.tr t).length := (len_of_get hget).le
  -- the package's `P` store, with the iteration's coordinate
  have hp : PSt L X (g / L.block) (G.p0 (g / L.block)) (G.Soft (g / L.block))
      (G.tm (g / L.block)) t ks (d.i - 1) a vals (.s16x32bx2 32) := by
    rcases l.st hT hct with ⟨i5, hp⟩ | ⟨i5, ho⟩
    · obtain ⟨d5, hσ5, -, hi5⟩ := pst_iter hpre hX hf hp htl hct
      rw [hσs] at hσ5
      simp only [Option.some.injEq, Interface.TSt.d.injEq, DComp.St.sm.injEq] at hσ5
      subst hσ5
      rw [his] at hi5
      subst hi5
      exact hp
    · exfalso
      have := ho.shape.1
      simp at this
  obtain ⟨-, hl32, w0, ha⟩ := hp.shape
  have hcell : tcDataCell L t (.s16x32bx2 32) a (w % 32) =
      sCell (g / L.block) d.tm (d.i - 1) r w := by
    rw [ha, hcov w0, sCell, htmG]
  have hin : InP (G.tm (g / L.block)) ((d.i - 1) % 2)
      (sCell (g / L.block) d.tm (d.i - 1) r w).column := by
    unfold InP sCell
    simp only
    omega
  have hxc : (g, k).1 / L.block = g / L.block := rfl
  refine ⟨t, ks, pcs, a, ds, vals, .s16x32bx2 32, htl, hct, hσs, hss, his, hget, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- the source is not the MMA
    intro h
    have h1 : t = g := congrArg Prod.fst h
    have h2 : ks = k := congrArg Prod.snd h
    subst h1 h2
    rw [hσs] at hσ
    cases Option.some.inj (Option.some.inj hσ)
  · exact .inr (.inl ⟨a, vals, _, w % 32, hT, by omega, hcell.symm⟩)
  · -- the store is done before the MMA
    have hf' : (d.i - 1) / 2 + 1 ≤
        okPolls (pReady L (g / L.block) ((d.i - 1) % 2))
          ((X.tr (G.cm (g / L.block))).take k) := by
      have := hpv.pPolls ((d.i - 1) % 2) hb2
      unfold SO.below2 at this
      simp only at this
      omega
    have h := store_before_mma H hb2 l.cm_ok.1 l.cm_ok.2 (fun hw => l.pAcq hb2 hw) hp.gate hT hf'
      (by rw [← hgcm]; exact hk)
    rw [← hgcm] at h
    exact .inr (.inl h)
  · -- every other writer of the cell
    intro other hw'
    have hol := cta_lt hX (write_event hnc hns hw')
    have iy := winfo hnc hns (G.lane _ hol) hw' rfl
    have hxy : other.1 / L.block = g / L.block := iy.cta.symm.trans (by simp [sCell])
    rw [hxy] at iy
    cases iy with
    | @qk _ cell' i' hq h1 _ =>
      have hpar : i' % 2 = (d.i - 1) % 2 := inS_parity h1 (SO.inP_inS hin)
      by_cases hle : i' ≤ d.i - 1
      · exact .inr (.inl (WriteBefore.of_done (qk_pst_A H l hq hp hT hpar (by omega))))
      · right
        right
        obtain ⟨j0, pc0, e0, hj0, hget0, db, dsc, hd, -, rfl⟩ := hpv.issue
        obtain ⟨j', pc', e', hget', da', db', dsc', hd', -, -, rfl⟩ := hq.issue
        refine SO.aRead_before_later_mma ⟨pc0, hget0⟩ rfl ⟨pc', hget'⟩
          (hpv.thread ▸ l.cm_ok.1) (hpv.thread.trans hq.thread.symm) ?_
        by_contra hnot
        have hmono := countP_take_mono (commitsTo (EvW.oDone L (g / L.block)))
          (X.tr (G.cm (g / L.block))) (show other.2 ≤ k by simp at hnot ⊢; omega)
        have h1 := hq.oCommits
        have h2 := hpv.oCommits
        simp only at h2
        omega
    | @pv _ cell' m' hv' h1 _ =>
      exact absurd h1 (SO.inP_inO_disjoint hb2 hin)
    | @pst t' sk' i' w' j' a' vals' sh' cell' hst' hp' hj' ha' hc' hin' _ =>
      have hpar : (d.i - 1) % 2 = i' % 2 := inP_parity hin hin'
      obtain ⟨ht', htc', htd'⟩ := hp'.gate.soft
      have hba : G.tm (g / L.block) + 128 * ((d.i - 1) % 2) + 32 < 2 ^ 16 := by
        have := l.tmOk
        unfold TmOk at this
        omega
      have htt : t = t' := by
        refine split_thread (ba := G.tm (g / L.block) + 128 * ((d.i - 1) % 2)) (off := 32)
          (w := w0) (w' := w') (j := w % 32) (j' := j') hba (by omega) hj' htd htd'
          (hct.trans htc'.symm) ?_
        rw [← ha, hcell, hc', ha', ← hpar]
      subst htt
      obtain ⟨d', hσ', hs', hi'⟩ := pst_iter hpre hX hf hp' htl hct
      have hsk' : sk' ≤ (X.tr t).length := by
        obtain ⟨pc'', h''⟩ := hst'
        exact (len_of_get h'').le
      rcases Nat.lt_trichotomy i' (d.i - 1) with hlt | heq | hgt
      · -- an earlier `P` store of the thread
        have hlt' : sk' < ks := by
          rcases Nat.lt_trichotomy sk' ks with h | h | h
          · exact h
          · subst h
            rw [hσs] at hσ'
            simp only [Option.some.injEq, Interface.TSt.d.injEq, DComp.St.sm.injEq] at hσ'
            subst hσ'
            omega
          · have := Interface.Kk.tmemSt_order hsk' hσs hss hσ' hs' h
            omega
        exact .inr (.inl (.inr (.inl (StoreDoneBefore.of_po hst' hT htl rfl hlt'))))
      · -- the source itself
        left
        have := Interface.Kk.tmemSt_unique hsk' hks hσ' hs' hσs hss (by omega)
        rw [this]
      · -- a later `P` store: after the MMA
        have hb' : i' % 2 < 2 := Nat.mod_lt _ (by omega)
        have hu : ((X.tr (G.cm (g / L.block))).take (g, k).2).countP
            (commitsTo (sReady L (g / L.block) (i' % 2))) ≤ i' / 2 := by
          have := hpv.sCommits
          rw [hpar] at this
          omega
        exact .inr (.inr (.inr (.inl (mma_before_s_store H hb' l.cm_ok.1 l.cm_ok.2
          (fun hx hc => l.mma_thread hx hc) hp'.gate hst' hpv.isMma hxc hu))))
    | @ost t' sk' i' w' j' a' vals' sh' cell' hst' ho hj' ha' hc' hin' _ =>
      exact absurd hin' (SO.inP_inO_disjoint hb2 hin)
  · exact Pr.sourceLive_mma hX ht hmd hmE (by simp [sCell])

end
end PTX.Kernels.InklingRelDecode.Proof.Kk
