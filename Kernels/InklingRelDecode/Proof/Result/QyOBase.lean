-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxAll
public import Kernels.InklingRelDecode.Proof.Result.RrAll
public import Kernels.InklingRelDecode.Proof.Interface.SwStO

@[expose] public section

/-!
# The accumulator source of PV step 0 of an iteration, every row (`Qx.ElemRest.oBase`)

`Rs.oAccBase_of` is the read-source half of `OAcc.base` for valid rows on complete executions:
it uses `Complete` only for the index of the MMA's state (`Interface.mma_state_lt`), the row's
validity only for `r < 64`, and the rescale factors only in `OAccPrem.skip` and `store`. `oBaseF`
is its read-source half for an issued PV MMA, every row `r < 64`, on every consistent execution,
with the order of the rescale stores of a thread from `Rr.oaccOstIter_of`.

The value half: when the read source is a rescale store, its word at the cell is the product
`prodO al (ow w)` of the softmax state at the store (`Sm.shape_stO`). The word `ow w` is the one
the rescale load three events before returned (`Sv.stO_pred`); its read source is the PV MMA at
step 7 of the store's iteration (`OLoadSrcF`, the statement of `Qy.oLoadSrcF`), which is the MMA
of the thread before the accumulating one (`Rd.pv7_unique`), so under `Qx.ResultBelow` the word is
an `f32` number `y` and the product is the `f32` number `alr · y` (`oBase_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The statement of `Qy.oLoadSrcF` (`QyLoad.lean`, which imports this file): the rescale load
of iteration `i` reads the PV MMA at step 7 of iteration `i`. -/
def OLoadSrcF (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape},
    g < L.threads → St Q L X g k = some (some (.d (.sm d))) → d.site = .ldO →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .pv 7 ∧ dm.i = d.i ∧
      ∀ j < 64, ReadSource L X .ld m (g, k) (tcDataCell L g (.s16x32bx2 64) a j)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hb : Interface.BaseWordRead L X)
  (hn : Interface.NumWordRead Q L X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
  (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L kernel Assumptions.all mem0 X)
  (st : Pr.MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X)
include hpre hX hf hb hn hnc hns G st ht hmd

/-- **The accumulator source of PV step 0 of iteration `i ≥ 2`**, every row `r < 64`, every
consistent execution: the PV MMA at step 7 of iteration `i - 1` (when no rescale store of
iteration `i - 1` covers the cell), or a rescale store of iteration `i - 1`. -/
theorem oBaseF (hMB : Mma.MmaBcast L X) {g k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv 0) (hi : 2 ≤ d.i)
    {r n : Nat} (hrow : r < 64) (hn' : n < 128) :
    ∃ (k' : Nat) (d' : Mma.D), k' < k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
      d'.site = .pv 7 ∧ d'.i + 1 = d.i ∧ d'.tm = d.tm ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      (TcMma.ReadSource L X .acc (g, k') (g, k) (oCell (g / L.block) d.tm r n) ∨
        ∃ (t sk a : Nat) (vals : List Value) (sh : TcShape) (j : Nat),
          TcMma.ReadSource L X .acc (t, sk) (g, k) (oCell (g / L.block) d.tm r n) ∧
          X.TSt (t, sk) a vals sh ∧
          OSt L X (g / L.block) (G.p0 (g / L.block)) (G.Soft (g / L.block))
            (G.tm (g / L.block)) t sk (d.i - 1) a vals sh ∧ j < 64 ∧ sh = .s16x32bx2 64 ∧
          oCell (g / L.block) d.tm r n = tcDataCell L t (.s16x32bx2 64) a j) := by
  obtain ⟨e, he0⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have hg : g < L.threads := event_thread_lt hX he0
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he0⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  obtain ⟨pc, dst, sp, acc, mask, hev⟩ :=
    Interface.mma_issue_event hpre hX hf hg he0 hσ (.inr ⟨0, hs⟩)
  rw [hev] at he0
  have hmE : IsMma X (g, k) := ⟨dst, sp, acc, mask, pc, he0⟩
  have hgcm : g = G.cm (g / L.block) := l.mma_thread hmE rfl
  have hlead : ElectLead L g (X.tr g) := Interface.lead_of_pv0 hX hk hσ hs
  obtain ⟨k', d', hlt, hσ', hs', hi', htm, -, hev', hch⟩ :=
    Interface.exists_pv7 hpre hX hf hlead (Interface.bcast_of_mma hf.roleWarp hMB hg hk.le hσ)
      (i0 := d.i - 1) (by omega) k hk hσ (Or.inl (by omega))
  obtain ⟨pc', dst', sp', acc', mask', he'⟩ := hev'
  have hk' : k' < (X.tr g).length := len_of_get he'
  have hbet := Interface.between_bef hX hf (b := d.i - 1) (by omega) hk hσ hs (by omega)
    (fun j h1 h2 => by
      obtain ⟨dj, a1, a2, -⟩ := hch j h1 h2
      exact ⟨dj, a1, a2⟩)
  -- the lane's data
  have hpvE := (st.pv hg hk hσ hs).2
  have hpvS := (st.pv hg hk' hσ' hs').2
  have hdm0 : d.tm = 0 := Interface.mma_tm hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩
  obtain ⟨hqo, hdst, -, hmask, -⟩ := pv_event hpre hX hf hg he0 hσ hs
  obtain ⟨hqo', hdst', -, hmask', -⟩ := pv_event hpre hX hf hg he' hσ' hs'
  have htmG : G.tm (g / L.block) = d.tm := by
    have := Rs.pvAt_dst hpvE he0
    omega
  have hwcE : writeCell sp dst mask r n = some (oCell (g / L.block) d.tm r n) := by
    rw [hdst, hmask, hdm0]
    have := pv_writeCell (sp := sp) hqo.desc (cta := g / L.block) (tm := 0) hqo.low (by omega)
      hrow hn'
    simpa using this
  have hwcS : writeCell sp' dst' mask' r n = some (oCell (g / L.block) d.tm r n) := by
    rw [hdst', hmask', htm, hdm0]
    have := pv_writeCell (sp := sp') hqo'.desc (cta := g / L.block) (tm := 0) hqo'.low (by omega)
      hrow hn'
    simpa using this
  have hmcE : X.MmaCell (g, k) (oCell (g / L.block) d.tm r n) :=
    ⟨_, _, _, _, r, n, ⟨pc, he0⟩, hwcE⟩
  have hmcS : X.MmaCell (g, k') (oCell (g / L.block) d.tm r n) :=
    ⟨_, _, _, _, r, n, ⟨pc', he'⟩, hwcS⟩
  have hmS : IsMma X (g, k') := ⟨dst', sp', acc', mask', pc', he'⟩
  obtain ⟨jy, pcy, ey, hjy, hgy, hqy⟩ := hpvS.issue
  obtain ⟨hIO, hcta⟩ := SO.pv_cells l.tmOk hqy hgy hmcS
  have ixS : WInfo L X (g / L.block) (G.cm (g / L.block)) (G.p0 (g / L.block))
      (G.tm (g / L.block)) (G.Soft (g / L.block)) (g, k') (oCell (g / L.block) d.tm r n) :=
    .pv hpvS hIO hcta
  -- no PV MMA of the lane lies between the two steps
  have hnobetween : ∀ (o2 : Nat) {m'' : Nat},
      PvAt L X (g / L.block) (G.cm (g / L.block)) (G.tm (g / L.block)) (g, o2) m'' →
      ¬ (k' < o2 ∧ o2 < k) := by
    intro o2 m'' hv ⟨h1, h2⟩
    obtain ⟨dj, hσj, hbef⟩ := hbet (k - o2 - 1) o2 (by omega) h1
    obtain ⟨dq, hσq, hpq, -⟩ := hch o2 h1 (by omega)
    have hdd : dq = dj := by
      have := Option.some.inj (Option.some.inj (hσq.symm.trans hσj))
      simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    obtain ⟨pco, dso, sso, aco, mko, hgo⟩ := hv.isMma.get
    rcases mma_event_cases hpre hX hf hg hgo with
      ⟨d'', P'', j'', hσ'', hI'', hs'', hq'', hdst'', -, -⟩ | ⟨d'', P'', j'', hσ'', hI'', hs'', -⟩
    · exfalso
      have hdd2 : d'' = dq := by
        have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσq))
        simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
        exact this.1
      subst hdd2
      have h0 := Interface.mma_tm hpre hX hf hb hn (m := (g, o2)) ⟨P'', hσ''⟩
      have h1d := Rs.pvAt_dst hv hgo
      omega
    · exfalso
      have hdd2 : d'' = dq := by
        have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσq))
        simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
        exact this.1
      subst hdd2
      unfold Interface.Past at hpq
      unfold Interface.Bef at hbef
      rcases hpq with hp | ⟨-, hp⟩
      · rcases hbef with hb2 | ⟨-, -, -, hb2, -⟩
        · omega
        · exact hb2 j'' hs''
      · rcases hp with hp | hp <;> rw [hs''] at hp <;> cases hp
  -- a writer of the cell is a PV MMA of the lane or a rescale store
  have hclass : ∀ other : EvId, TmemWrite L X other (oCell (g / L.block) d.tm r n) →
      (∃ m'', PvAt L X (g / L.block) (G.cm (g / L.block)) (G.tm (g / L.block)) other m'' ∧
        other.1 = g) ∨
      ∃ (t sk i' a' : Nat) (vals : List Value) (sh : TcShape) (j' : Nat),
        OSt L X (g / L.block) (G.p0 (g / L.block)) (G.Soft (g / L.block))
          (G.tm (g / L.block)) t sk i' a' vals sh ∧ X.TSt (t, sk) a' vals sh ∧ j' < 64 ∧
          oCell (g / L.block) d.tm r n = tcDataCell L t (.s16x32bx2 64) a' j' ∧
          other = (t, sk) := by
    intro other hw'
    have hol := cta_lt hX (write_event hnc hns hw')
    have iy := winfo hnc hns (G.lane _ hol) hw' rfl
    have hxy : other.1 / L.block = g / L.block := iy.cta.symm.trans ixS.cta
    rw [hxy] at iy
    cases iy with
    | @qk _ _ i' hq' h1' _ =>
      exact absurd hIO (SO.inS_inO_disjoint (Nat.mod_lt _ (by omega)) h1')
    | @pv _ _ m' hv' h1' _ => exact .inl ⟨m', hv', hv'.thread.trans hgcm.symm⟩
    | @pst t sk i' w j' a' vals sh cell' hst hp hj ha hc' hin _ =>
      exact absurd hIO (SO.inP_inO_disjoint (Nat.mod_lt _ (by omega)) hin)
    | @ost t sk i' w j' a' vals sh cell' hst ho hj ha hc' hin _ =>
      exact .inr ⟨t, sk, i', a', vals, sh, j', ho, hst, hj, hc', rfl⟩
  have hcG : oCell (g / L.block) (G.tm (g / L.block)) r n = oCell (g / L.block) d.tm r n := by
    rw [htmG]
  have hOI := Rr.oaccOstIter_of hpre hX hf G
  refine ⟨k', d', hlt, hσ', hs', by omega, htm, ⟨pc', dst', sp', acc', mask', he'⟩, ?_⟩
  by_cases hex : ∃ (t sk a : Nat) (vals : List Value) (sh : TcShape) (j : Nat),
      X.TSt (t, sk) a vals sh ∧
        OSt L X (g / L.block) (G.p0 (g / L.block)) (G.Soft (g / L.block))
          (G.tm (g / L.block)) t sk (d.i - 1) a vals sh ∧ j < 64 ∧
        oCell (g / L.block) d.tm r n = tcDataCell L t (.s16x32bx2 64) a j
  · -- a rescale store of the iteration covers the cell: it is the read source
    obtain ⟨t, sk, a, vals, sh, j, hst, ho, hj, hcj⟩ := hex
    obtain ⟨hsh1, hsh2, w, ha⟩ := ho.shape
    obtain ⟨htt, -, -⟩ := soft_info H ho.gate.soft
    refine .inr ⟨t, sk, a, vals, sh, j, ?_, hst, ho, hj, hsh1, hcj⟩
    rw [readSource_acc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hh
      obtain ⟨pcs, hs0⟩ := hst
      rw [hh, he0] at hs0
      simp at hs0
    · exact .inr (.inl ⟨a, vals, sh, j, hst, by rw [hsh2]; exact hj,
        by rw [hsh1]; exact hcj⟩)
    · exact .inr (.inl (pv_ost_B H l hpvE ho hst (by omega)))
    · intro other hw'
      rcases hclass other hw' with ⟨m'', hv', hth⟩ | ⟨t', sk', i'', a', vals', sh', j', ho',
        hst', hj', hcj', rfl⟩
      · obtain ⟨o1, o2⟩ := other
        simp only at hth
        subst hth
        rcases Nat.lt_trichotomy o2 k with h2 | h2 | h2
        · rcases Nat.lt_or_ge k' o2 with h3 | h3
          · exact absurd ⟨h3, h2⟩ (hnobetween o2 hv')
          · exact .inr (.inr (.inl (.inl (.inl (Rs.pv_ost_A' H l hv'.isMma rfl hpvS h3 ho hst
              (by omega))))))
        · exact .inr (.inl (by rw [h2]))
        · exact .inr (.inr (.inr (pv_before l.cm_ok.1 hpvE hv' h2)))
      · obtain ⟨hsh1', hsh2', w', ha'⟩ := ho'.shape
        have htt' : t = t' := Rs.ost_same_thread H l ho hj ha hcj ho' hj' ha' hcj'
        subst htt'
        have hit := hOI (g / L.block) hcl ho ho'
        have hit' := hOI (g / L.block) hcl ho' ho
        rcases Nat.lt_trichotomy i'' (d.i - 1) with h2 | h2 | h2
        · rcases Nat.lt_trichotomy sk' sk with h3 | h3 | h3
          · exact .inr (.inr (.inl (.inr (.inl (StoreDoneBefore.of_po hst' hst htt rfl h3)))))
          · have := hit.2 h3.symm
            omega
          · have := hit.1 h3
            omega
        · rcases Nat.lt_trichotomy sk' sk with h3 | h3 | h3
          · have := hit'.1 h3
            omega
          · subst h3
            exact .inl rfl
          · have := hit.1 h3
            omega
        · exact .inr (.inr (.inr (.inl (pv_ost_A H l hpvE ho' hst' (by omega)))))
    · exact Pr.sourceLive_mma hX ht hmd hmE rfl
  · -- no rescale store of the iteration covers the cell: the earlier PV MMA is the source
    refine .inl ?_
    rw [readSource_acc]
    have hbefSE : Before L X (g, k') (g, k) := by
      obtain ⟨jy, pcy, ey, hjy, hgy, dby, dscy, hdy, -, rfl⟩ := hpvS.issue
      obtain ⟨jx, pcx, ex, hjx, hgx, dbx, dscx, hdx, -, rfl⟩ := hpvE.issue
      have hdsc : dscx = dscy := Option.some.inj (hdx.symm.trans hdy)
      subst hdsc
      exact Before.of_mma_po ⟨pcy, hgy⟩ ⟨pcx, hgx⟩ hg rfl hlt sameAcc_pv
    refine ⟨?_, .inl hmcS, .inl hbefSE, ?_, Pr.sourceLive_mma hX ht hmd hmE rfl⟩
    · intro hh
      have := congrArg Prod.snd hh
      simp only at this
      omega
    · intro other hw'
      rcases hclass other hw' with ⟨m'', hv', hth⟩ | ⟨t', sk', i'', a', vals', sh', j', ho',
        hst', hj', hcj', rfl⟩
      · obtain ⟨o1, o2⟩ := other
        simp only at hth
        subst hth
        rcases Nat.lt_trichotomy o2 k' with h1 | h1 | h1
        · exact .inr (.inr (.inl (.inl (pv_before l.cm_ok.1 hv' hpvS h1))))
        · exact .inl (by rw [h1])
        · rcases Nat.lt_trichotomy o2 k with h2 | h2 | h2
          · exact absurd ⟨h1, h2⟩ (hnobetween o2 hv')
          · exact .inr (.inl (by rw [h2]))
          · exact .inr (.inr (.inr (pv_before l.cm_ok.1 hpvE hv' h2)))
      · have h1le := ho'.one_le
        rcases Nat.lt_trichotomy i'' (d.i - 1) with h2 | h2 | h2
        · exact .inr (.inr (.inl (.inr (.inl (pv_ost_B H l hpvS ho' hst' (by omega))))))
        · exact absurd ⟨t', sk', a', vals', sh', j', hst', by rw [← h2]; exact ho', hj', hcj'⟩ hex
        · exact .inr (.inr (.inr (.inl (pv_ost_A H l hpvE ho' hst' (by omega)))))

/-- **`Qx.ElemRest.oBase`** (with the event of the MMA, `ElemRest.oBase` restated): the
accumulator of PV step 0 of an iteration `i ≥ 2` reads the last PV MMA of iteration `i - 1` or a
rescale store whose word at the cell is an `f32` number. -/
theorem oBase_of (hR : Interface.RoleReads L X) (hO : OLoadSrcF Q L X) (hMB : Mma.MmaBcast L X) :
    ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro}, g < L.threads →
    (∃ e, X.get (g, k) = some e) →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv 0 → 2 ≤ d.i →
    X.async.mmaDone (g, k) = true → Qx.ResultBelow L X g k → ∀ {r n : Nat}, r < 64 → n < 128 →
    ∃ src, ReadSource L X .acc src (g, k) (oCell (g / L.block) d.tm r n) ∧
      ((∃ (k' : Nat) (d' : Mma.D) (P' : Loader.Pro), k' < k ∧ src = (g, k') ∧
          St Q L X g k' = some (some (.w (.mma d' P'))) ∧
          (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
          d'.site = .pv 7 ∧ d'.i + 1 = d.i ∧ d'.tm = d.tm) ∨
        ∃ old x, StoreValue L X src (oCell (g / L.block) d.tm r n) old ∧
          valFloat .f32 old = .ok x) := by
  intro g k d P hg ⟨e, he⟩ hσ hs hi _ hbelow r n hr hn'
  obtain ⟨k', d', hlt, hσ', hs', hi', htm, hev', hsrc⟩ :=
    oBaseF hpre hX hf hb hn hnc hns G st ht hmd hMB (len_of_get he) hσ hs hi hr hn'
  rcases hsrc with hrs | ⟨t, sk, a, vals, sh, j, hrs, ⟨pcs, hget⟩, ho, hj, hsh, hcj⟩
  · exact ⟨_, hrs, .inl ⟨k', d', P, hlt, rfl, hσ', hev', hs', hi', htm⟩⟩
  · subst hsh
    obtain ⟨ds, hσs, hds⟩ := Rs.stO_state hX hf hget
    have htl : t < L.threads := event_thread_lt hX hget
    obtain ⟨u, hF⟩ := Interface.fired_cont hX hf htl hget hσs (by simp [Interface.ExitState])
    obtain ⟨vals', hl, hw, -, hev⟩ := Sm.shape_stO (Interface.fired_sm hF) hds
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
    obtain ⟨-, -, hvv, -⟩ := hev
    subst hvv
    have hIv : Sm.Inv L t ds := by
      obtain ⟨t', ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hget hσs
      exact hinv.2
    -- the iteration of the store and its thread
    have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
    have H := G.ctx (g / L.block) hcl
    have l := G.lane (g / L.block) hcl
    obtain ⟨-, htc, -⟩ := soft_info H ho.gate.soft
    have hdsi : ds.i = d.i - 1 := Rr.ostIter_of hpre hX hf G (g / L.block) hcl ho hσs
    -- the rescale load three events before, and its source
    obtain ⟨k0, d0, a0, vals0, sh0, rfl, hσ0, hs0, ⟨pc0, hget0⟩, hd⟩ :=
      Sv.stO_pred (len_of_get hget).le hσs hds
    obtain ⟨hsh0, hlen0, -⟩ := Interface.Lk.tcld_event hpre hX hf htl hget0
    subst hsh0
    obtain ⟨⟨mg, mk⟩, pcm, dstm, spm, accm, maskm, dm, Pm, -, hmc, hmget, hmσ, hms, hmi, hrsm⟩ :=
      hO htl hσ0 hs0 hget0
    obtain ⟨pc', dst', sp', acc', mask', he'⟩ := hev'
    have hmg : mg = g := by
      have h1 := l.mma_thread ⟨dstm, spm, accm, maskm, pcm, hmget⟩ (hmc.trans htc)
      have h2 := l.mma_thread ⟨dst', sp', acc', mask', pc', he'⟩ rfl
      exact h1.trans h2.symm
    subst hmg
    have hd0 : d0.i = ds.i := by rw [hd]
    have hmk : mk = k' :=
      Rd.pv7_unique hpre hX hf hR (len_of_get hmget) (len_of_get he') hmσ hms hσ' hs'
        (by omega)
    subst hmk
    -- the loaded word is the `f32` result of that MMA
    obtain ⟨xw, hxw⟩ := Qx.ldSource_result_at hX
      (fun {_ _ _ _ _} h1 h2 {_ _ _} h3 => hbelow _ hlt h1 h2 h3) hmget hget0 (hrsm j hj)
    have hLC : LoadCell L X (t, k0) j (tcDataCell L t (.s16x32bx2 64) a0 j) :=
      ⟨a0, vals0, .s16x32bx2 64, ⟨pc0, hget0⟩, by omega, rfl⟩
    obtain ⟨word, hword, hwc2⟩ :=
      hX.tcRead.1 (t, k0) _ _ _ j _ _ _ ⟨pc0, hget0⟩ hLC (hrsm j hj) (.inl hxw)
    have hy : ds.stg.ow j = .float .f32 xw := by
      rcases hwc2 with ⟨-, rfl⟩ | ⟨hb2, -⟩
      · rw [hd]
        show vals0.getD j (b32 0) = _
        rw [List.getD_eq_getElem?_getD, hword]
        rfl
      · simp [Value.bytes, FloatFmt.bytes] at hb2
    have hpw : Sm.prodO ds.stg.al (ds.stg.ow j) = .float .f32 (ds.stg.alr * xw) := by
      rw [hy, Sm.prodO_float hIv.four.al]
    refine ⟨_, hrs, .inr ⟨_, ds.stg.alr * xw,
      ⟨a, _, .s16x32bx2 64, j, ⟨pcs, hget⟩, hw j hj, hcj⟩, ?_⟩⟩
    rw [hpw]
    exact valFloat_float

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
