-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.KkAll
public import Kernels.InklingRelDecode.Proof.Result.QxAll
public import Kernels.InklingRelDecode.Proof.Interface.QyLayer

@[expose] public section

/-!
# The A operand of a PV MMA on every consistent execution (`Qx.ElemRest.pvA`, `SourceRest.a`)

`Kk.pReadSrc_of` names the read source of each A cell of a PV MMA (the `P` store of the previous
iteration of the softmax thread that covers the cell), from `Complete L X`: it takes the store's
existence from `Interface.sm_reaches_tmemSt`. `pReadSrcF` is the same statement for an issued PV
MMA on every consistent execution and for every row `r < 64`. The store's existence comes from
the MMA's own poll of `p_ready`: the lane's `(i - 1) / 2 + 1` successful polls of
`p_ready ((i - 1) % 2)` before the MMA (`Pr.MmaStates`) are bounded by thread 0's arrivals
(`Qy.arrivals_of_polls`), and those give every softmax thread's `P` store of iteration `i - 1`
(`Qy.tmemSt_of_arrivals`). The rest of the proof is `Kk.pReadSrc_of`'s.

The stored words are `bf16` pairs of reals at every state (`Sm.D.pw`, `Sm.shape_tmemSt`), so
every A element is a number (`pvA_of`), and every A cell has a source with a value (`aSource_of`;
a QK MMA reads no A cell from Tensor Memory).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hb : Interface.BaseWordRead L X)
  (hn : Interface.NumWordRead Q L X)
  (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
  (G : SrPkg L kernel Assumptions.all mem0 X) (hG : ∀ c, G.p0 c = Hs.p0Of L c)
  (st : Pr.MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X)
  (hD : ∀ c j, DecAgree Q L X c j)
include hpre hX hf hb hn hnc hns G hG st ht hmd hD

omit hb hn in

/-- **The read source of an A cell of an issued PV MMA**, every row `r < 64`, every consistent
execution: the `P` store of iteration `i - 1` of the softmax thread that covers the cell. -/
theorem pReadSrcF {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (he0 : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {d : Mma.D} {P : Loader.Pro}
    {j : Fin 8} {r w : Nat} (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site = .pv j) (hrow : r < 64) (hw1 : 8 * j.val ≤ w) (hw2 : w < 8 * j.val + 8) :
    ∃ (t ks pcs a : Nat) (ds : Sm.D) (vals : List Value) (sh : TcShape),
      t < L.threads ∧ t / L.block = g / L.block ∧
      St Q L X t ks = some (some (.d (.sm ds))) ∧ ds.site = .tmemSt ∧ ds.i = d.i - 1 ∧
      X.get (t, ks) = some ⟨pcs, .tc (.st a vals sh)⟩ ∧
      ReadSource L X .a (t, ks) (g, k) (sCell (g / L.block) d.tm (d.i - 1) r w) := by
  have hg : g < L.threads := event_thread_lt hX he0
  have hk : k < (X.tr g).length := len_of_get he0
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he0⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  have hmE : IsMma X (g, k) := ⟨dst, sp, acc, mask, pc, he0⟩
  have hgcm : g = G.cm (g / L.block) := l.mma_thread hmE rfl
  have hpv := (st.pv hg hk hσ hs).2
  obtain ⟨-, hdst, -, -, hinv⟩ := pv_event hpre hX hf hg he0 hσ hs
  have htmG : G.tm (g / L.block) = d.tm := by
    have := Rs.pvAt_dst hpv he0
    omega
  have hw64 : w < 64 := by have := j.isLt; omega
  have hb2 : (d.i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  -- the covering thread
  obtain ⟨t, htc, htd, hcov⟩ := Kk.cover hpre.block l.tmOk hb2 hrow hw64 (g / L.block)
  have hpos : 0 < L.block := by have := hpre.block; omega
  have htl : t < L.threads := by
    have h1 := (Nat.div_lt_iff_lt_mul hpos).mp (htc ▸ hcl : t / L.block < L.grid)
    unfold Launch.threads
    exact h1
  have hct : t / L.block = g / L.block := htc
  -- the lane's polls of `p_ready` give the thread's store of iteration `i - 1`
  have hf' : (d.i - 1) / 2 + 1 ≤
      okPolls (pReady L (g / L.block) ((d.i - 1) % 2))
        ((X.tr (G.cm (g / L.block))).take k) := by
    have := hpv.pPolls ((d.i - 1) % 2) hb2
    unfold SO.below2 at this
    simp only at this
    omega
  have hgd := arrivals_of_polls H l hb2 hf'
  rw [hG] at hgd
  obtain ⟨ks, ds, pcs, vals, hσs, hss, his, hget⟩ :=
    tmemSt_of_arrivals hpre hX hf hD htl hct htd hgd
  set a := Sm.tileAddr L t ds with ha_def
  have hT : X.TSt (t, ks) a vals (.s16x32bx2 32) := ⟨pcs, hget⟩
  have hks : ks ≤ (X.tr t).length := (len_of_get hget).le
  -- the package's `P` store, with the iteration's coordinate
  have hp : PSt L X (g / L.block) (G.p0 (g / L.block)) (G.Soft (g / L.block))
      (G.tm (g / L.block)) t ks (d.i - 1) a vals (.s16x32bx2 32) := by
    rcases l.st hT hct with ⟨i5, hp⟩ | ⟨i5, ho⟩
    · obtain ⟨d5, hσ5, -, hi5⟩ := Kk.pst_iter hpre hX hf hp htl hct
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
      obtain ⟨d', hσ', hs', hi'⟩ := Kk.pst_iter hpre hX hf hp' htl hct
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

/-- **`Qx.ElemRest.pvA`**: every A element of a PV MMA with recorded operands is a number, every
row. The read source of the element's cell is a `P` store (`pReadSrcF`), whose word at the cell
is a pair of `bf16` numbers (`Sm.shape_tmemSt`: word `w` is `Sm.D.pw w`), and `AReadOk` gives the
operand bytes as that word's bytes. -/
theorem pvA_of (hre : Interface.Lk.SmReal Q L X) :
    ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    {d : Mma.D} {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {r kk : Nat},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → r < 64 → kk < 16 →
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk = .ok x := by
  intro g k pc dst sp acc mask d P j ops r kk hg he0 hσ hs _ hops hr64 hk
  have hd0 : d.tm = 0 := Interface.mma_tm hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩
  obtain ⟨hqo, -, -, -, hIn⟩ := pv_event hpre hX hf hg he0 hσ hs
  have hat := Rs.pv_aTmem hpre hX hf hg he0 hσ hs
  rw [hd0] at hat
  obtain ⟨t, ks, pcs, a, ds, vals, sh, ht', htc, hσs, hsite, hdi, hget, hrs⟩ :=
    pReadSrcF hpre hX hf hnc hns G hG st ht hmd hD he0 hσ hs hr64
      (w := 8 * j.val + kk / 2) (by omega) (by omega)
  rw [hd0] at hrs
  have hlen : ks < (X.tr t).length := len_of_get hget
  obtain ⟨hae, hsh⟩ := Rs.pstore_shape hX hf ht' hσs hsite hget
  subst hsh
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf ht' hget hσs (by simp [Interface.ExitState])
  obtain ⟨vals', hl, hwv, -, hev⟩ := Sm.shape_tmemSt (Interface.fired_sm hF) hsite
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
  obtain ⟨-, -, hvv, -⟩ := hev
  subst hvv
  have hwr := hrs.2.1
  rcases tmemWrite_of_no_copy hnc hns hwr with ⟨d1, s1, acc1, mask1, row1, col1, ⟨pc1, h1⟩, -⟩ |
    ⟨a1, vals1, sh1, w1, hts1, hw1, hcell1⟩
  · exfalso
    rw [hget] at h1
    simp at h1
  obtain ⟨pcs1, hget1⟩ := hts1
  rw [hget] at hget1
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hget1
  obtain ⟨-, rfl, rfl, rfl⟩ := hget1
  have hw1' : w1 < 32 := by rw [← hl]; exact hw1
  have hvw := hwv w1 hw1'
  have hRs : Sm.RealSt ds.stg ds.m ds.pf := by
    obtain ⟨t0, ins0, o0, -, hinv0, -, -⟩ := Frame.fired_site hf.sound hX hget hσs
    exact hinv0.2.re (hre hσs)
  rw [Sm.pwV_real hRs.pv] at hvw
  have hwrote : Wrote L Assumptions.all X (t, ks)
      (sCell (g / L.block) 0 (d.i - 1) r (8 * j.val + kk / 2)) _ :=
    .inr (.inl ⟨_, _, .s16x32bx2 32, w1, ⟨pcs, hget⟩, hvw, hcell1⟩)
  have hbyte : ∀ z, z < 2 → ops.a[2 * (r * 16 + kk) + z]? = some (some
      ((Value.float .bf16 (ds.pf (2 * w1 + kk % 2))).byteAt z)) := by
    intro z hz
    rw [← idx_eq]
    have hcellA := Rs.pv_a_cell hqo.desc (cta := g / L.block) (tm := 0) (b := d.i - 1)
      (j := j.val) hqo.low hat j.isLt (by omega) hr64 hk hz
    have hpos : 2 * (kk % 2) + z < (ds.pw w1).bytes := by
      simp [Sm.D.pw, Value.bytes, FloatFmt.bytes]
      omega
    have hread := hX.tcRead.2 (g, k) (32 * r + 2 * kk + z)
      (sCell (g / L.block) 0 (d.i - 1) r (8 * j.val + kk / 2)) (2 * (kk % 2) + z) (t, ks) _ ops
      ⟨dst, sp, acc, mask, ⟨pc, he0⟩, hcellA⟩ hrs hwrote hops hpos
    rw [hread]
    congr 2
    unfold Sm.D.pw
    rcases Nat.mod_two_eq_zero_or_one kk with h0 | h1
    · rw [h0, mul_zero, zero_add, (Rs.pair_byteAt _ _ z hz).1, Nat.add_zero]
    · have e : 2 * (kk % 2) + z = 2 + z := by omega
      rw [e, (Rs.pair_byteAt _ _ z hz).2, h1]
  exact ⟨_, element_bf16 (hbyte 0 (by omega)) (hbyte 1 (by omega))⟩

/-- **`Qx.SourceRest.a`**: every A cell of an MMA has a read source with a value. A QK MMA reads
its A operand from shared memory (no A cell); a PV MMA's A cell is the `P` store's cell
(`pReadSrcF`), whose stored word is its value. -/
theorem aSource_of : ∀ i cell, X.async.mmaDone i = true → X.MmaACell i cell →
    ∃ source value, ReadSource L X .a source i cell ∧
      Wrote L Assumptions.all X source cell value := by
  rintro ⟨g, k⟩ cell - ⟨d0, sp, acc, mask, index, bb, ⟨pc, he0⟩, hac⟩
  have hg : g < L.threads := event_thread_lt hX he0
  rcases mma_event_cases hpre hX hf hg he0 with
    ⟨d, P, j, hσ, -, hs, hq, -, -, -⟩ | ⟨d, P, j, hσ, -, hs, hq, -, -, -⟩
  · exfalso
    unfold aCell at hac
    rw [hq.aTmem] at hac
    cases hac
  · have hd0 : d.tm = 0 := Interface.mma_tm hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩
    have hat := Rs.pv_aTmem hpre hX hf hg he0 hσ hs
    rw [hd0] at hat
    have hrows : Operand.rows .a Ring.Foot.pvDesc = 64 := by decide
    have hbytes : Ring.Foot.pvDesc.kind.k * Ring.Foot.pvDesc.kind.width = 32 := by decide
    have hr64 : index / 32 < 64 := by
      have hac' := hac
      unfold aCell at hac'
      rw [hat, hq.desc] at hac'
      simp only [Option.bind_some, hrows, hbytes] at hac'
      by_contra hi
      split_ifs at hac' with hc <;> exact hi hc.2.1
    have hkk : index % 32 / 2 < 16 := by omega
    have hz : index % 2 < 2 := Nat.mod_lt _ (by omega)
    have hcellA := Rs.pv_a_cell hq.desc (cta := g / L.block) (tm := 0) (b := d.i - 1)
      (j := j.val) hq.low hat j.isLt (by omega) hr64 hkk hz
    have he : 32 * (index / 32) + 2 * (index % 32 / 2) + index % 2 = index := by omega
    rw [he, hac] at hcellA
    have hcell : cell = sCell (g / L.block) 0 (d.i - 1) (index / 32)
        (8 * j.val + index % 32 / 2 / 2) := (Prod.mk.inj (Option.some.inj hcellA)).1
    subst hcell
    obtain ⟨t, ks, pcs, a, ds, vals, sh, -, -, -, -, -, hget, hrs⟩ :=
      pReadSrcF hpre hX hf hnc hns G hG st ht hmd hD he0 hσ hs hr64
        (w := 8 * j.val + index % 32 / 2 / 2) (by omega) (by omega)
    rw [hd0] at hrs
    rcases tmemWrite_of_no_copy hnc hns hrs.2.1 with ⟨d1, s1, acc1, mask1, row1, col1, ⟨pc1, h1⟩,
      -⟩ | ⟨a1, vals1, sh1, w1, ⟨pcs1, hts1⟩, hw1, hcell1⟩
    · exfalso
      rw [hget] at h1
      simp at h1
    · exact ⟨(t, ks), vals1[w1], hrs,
        .inr (.inl ⟨a1, vals1, sh1, w1, ⟨pcs1, hts1⟩, List.getElem?_eq_getElem hw1, hcell1⟩)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
