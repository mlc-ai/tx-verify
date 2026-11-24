-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RsOSource

@[expose] public section

/-!
# The accumulator source of the first PV step of an iteration (`OAcc.base`)

`Result.Mma.OAcc.base`: PV step 0 of iteration `i ≥ 2` accumulates onto the last PV MMA of
iteration `i - 1` (`Interface.pv_base_pred`: the state at an earlier event, step 7 of iteration
`i - 1`) through either no store (the lazy skip: `alpha = 1`, the MMA is the read source) or the
softmax thread's rescale `tcgen05.st` of iteration `i - 1` (the read source, whose word is `alpha`
times the value that MMA left).

The orders are proved here, by the case of whether a rescale store of iteration `b = i - 1`
covers the cell. If none does: the PV MMA of the earlier step is the accumulator read source (the
rescale stores of the iterations below `b` are before it by `Sr.pv_ost_B`, those above are after
the later step by `Sr.pv_ost_A`, the other PV MMAs by program order, and none of the lane lies
between the two steps: `Interface.between_bef`). If one does: it is the read source (the PV MMAs
before the earlier step are before it, `pv_ost_A`; the rescale stores of other iterations are before
or after by the program order of the thread's stores).

The value half is the softmax region's (`OAccPrem.skip`, `store`): that no store of iteration `b`
covers the cell only where `alpha = 1`, and what the store holds is `alpha` times the value the
earlier PV MMA left. These are the rows of "thread-layer gaps" for the `Sm` rescale (the
development notes).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rs
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)

noncomputable section

variable {Q : Params} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution}

/-- **The softmax region's part of `OAcc.base`**, for the rescale factors `alpha`:
* `ostIter`: the rescale stores of one thread are one per iteration, in the order of the
  iterations (a store has one iteration; a later store has a later one);
* `skip`: if no rescale store of iteration `b` covers a cell of `O` of a valid row
  (`QRowValid`), with `1 ≤ b < num_iters`, the factor of the cell's row is 1 (the warp skipped
  the rescale: the minimum of its alphas is at least 1). For `b ≥ num_iters` no iteration `b`
  exists and the factor need not be 1;
* `store`: the word a rescale store of iteration `b` writes to a cell of a valid row is `alpha`
  times the value the PV MMA at step 7 of iteration `b` (block `b - 1`) left in the cell (the
  loaded word, the product `alpha · word`). -/
structure OAccPrem (Q : Params) (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) (G : SrPkg L K A mem0 X) (alpha : Nat → Nat → Nat → ℝ) : Prop where
  ostIter : ∀ c, c < L.grid → ∀ {t sk sk' i i' a a' : Nat} {vals vals' : List Value}
      {sh sh' : TcShape},
    OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk i a vals sh →
    OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk' i' a' vals' sh' →
    (sk < sk' → i < i') ∧ (sk = sk' → i = i')
  skip : ∀ c, c < L.grid → ∀ {g b r n : Nat}, g / L.block = c → 1 ≤ b →
    b < Q.numIters (reqOf L g) (splitOf L g) → QRowValid Q L g r → n < 128 →
    (¬ ∃ (t sk a : Nat) (vals : List Value) (sh : TcShape) (j : Nat),
      X.TSt (t, sk) a vals sh ∧ OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk b a vals sh ∧
        j < 64 ∧ oCell c (G.tm c) r n = tcDataCell L t (.s16x32bx2 64) a j) →
    alpha g b r = 1
  store : ∀ c, c < L.grid → ∀ {g b r n t sk a j k' : Nat} {vals : List Value} {sh : TcShape}
      {d' : Mma.D} {P : Loader.Pro}, g / L.block = c → 1 ≤ b → QRowValid Q L g r →
    n < 128 →
    X.TSt (t, sk) a vals sh → OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk b a vals sh →
    j < 64 → oCell c (G.tm c) r n = tcDataCell L t (.s16x32bx2 64) a j →
    St Q L X (G.cm c) k' = some (some (.w (.mma d' P))) → d'.site = .pv 7 → d'.i = b →
    ∀ v : ℝ, Result L Assumptions.all X (G.cm c, k') (oCell c (G.tm c) r n) (.float .f32 v) →
      StoreValue L X (t, sk) (oCell c (G.tm c) r n) (.float .f32 (alpha g b r * v))

/-- **A PV step's destination is the lane's `O` columns.** -/
theorem pvAt_dst {c cm tm : Nat} {x : EvId} {m pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} (h : PvAt L X c cm tm x m)
    (he : X.get x = some ⟨pc, .tc (.mma dst sp acc mask)⟩) : dst = tm + 256 := by
  obtain ⟨jy, pcy, ey, hjy, hgy, dby, dscy, hdy, -, rfl⟩ := h.issue
  rw [he] at hgy
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hgy
  exact hgy.2.1

/-- **A PV MMA of the lane at or before a PV step is done before a rescale store of an iteration
after the step's block**: the commits to `o_done` before the MMA are at most the step's. -/
theorem pv_ost_A' {c cm p0 tm : Nat} {Soft Mma : Nat → Prop}
    (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma) (l : Lane L X c cm p0 tm Soft) {x y : EvId}
    {m t sk i a : Nat} {vals : List Value} {sh : TcShape} (hx : IsMma X x)
    (hxc : x.1 / L.block = c) (hy : PvAt L X c cm tm y m) (hxy : x.2 ≤ y.2)
    (ho : OSt L X c p0 Soft tm t sk i a vals sh) (hst : X.TSt (t, sk) a vals sh)
    (hm : m ≤ i - 1) : DoneBefore L X x (t, sk) := by
  have hmono := countP_take_mono (commitsTo (EvW.oDone L c)) (X.tr cm) hxy
  have hxy' : ((X.tr cm).take x.2).countP (commitsTo (EvW.oDone L c)) ≤
      ((X.tr cm).take y.2).countP (commitsTo (EvW.oDone L c)) := hmono
  exact mma_before_o_store H l.cm_ok.1 l.cm_ok.2 (fun hx hc => l.mma_thread hx hc) ho.gate hst
    hx hxc (le_trans hxy' (le_trans hy.oCommits hm))

/-- **Two rescale stores writing one cell are of one thread.** -/
theorem ost_same_thread {c cm p0 tm : Nat} {Soft Mma : Nat → Prop}
    (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma) (l : Lane L X c cm p0 tm Soft)
    {t sk i w j a t' sk' i' w' j' a' : Nat} {vals vals' : List Value} {sh sh' : TcShape}
    {cell : Cell} (hp : OSt L X c p0 Soft tm t sk i a vals sh) (hj : j < 64)
    (ha : a = tm + 256 + w * 2 ^ 21) (hc : cell = tcDataCell L t (.s16x32bx2 64) a j)
    (hp' : OSt L X c p0 Soft tm t' sk' i' a' vals' sh') (hj' : j' < 64)
    (ha' : a' = tm + 256 + w' * 2 ^ 21) (hc' : cell = tcDataCell L t' (.s16x32bx2 64) a' j') :
    t = t' := by
  obtain ⟨ht, htc, htb⟩ := soft_info H hp.gate.soft
  obtain ⟨ht', htc', htb'⟩ := soft_info H hp'.gate.soft
  have hba : tm + 256 + 64 < 2 ^ 16 := by
    have := l.tmOk
    unfold TmOk at this
    omega
  rw [ha] at hc
  rw [ha'] at hc'
  exact split_thread hba hj hj' htb htb' (htc.trans htc'.symm) (hc.symm.trans hc')

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hcomp : Complete L X)
    (hb : Interface.BaseWordRead L X) (hn : Interface.NumWordRead Q L X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (G : SrPkg L kernel Assumptions.all mem0 X) (st : Pr.MmaStates Q L G)
    {alpha : Nat → Nat → Nat → ℝ} (V : OAccPrem Q L kernel Assumptions.all mem0 X G alpha)
include hpre hX hf hB hcomp hb hn hnc hns G st V

/-- **`OAcc.base`** for the rescale factors `alpha`, from the softmax region's part (`OAccPrem`). -/
theorem oAccBase_of (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X) :
    ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro},
      St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv 0 → 2 ≤ d.i → ∀ {r n : Nat},
      QRowValid Q L g r → n < 128 →
      ∃ (k' : Nat) (d' : Mma.D), k' < k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
        d'.site = .pv 7 ∧ d'.i + 1 = d.i ∧ d'.tm = d.tm ∧
        (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
        ((TcMma.ReadSource L X .acc (g, k') (g, k) (oCell (g / L.block) d.tm r n) ∧
            alpha g (d.i - 1) r = 1) ∨
          ∃ st, TcMma.ReadSource L X .acc st (g, k) (oCell (g / L.block) d.tm r n) ∧
            ∀ v, Result L Assumptions.all X (g, k') (oCell (g / L.block) d.tm r n)
                (.float .f32 v) →
              StoreValue L X st (oCell (g / L.block) d.tm r n)
                (.float .f32 (alpha g (d.i - 1) r * v))) := by
  intro g k d P hσ hs hi r n hr hn'
  obtain ⟨hg, hk⟩ := Interface.mma_state_lt hX hf hcomp hσ
  obtain ⟨e, he0⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
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
    Interface.exists_pv7 hpre hX hf hlead (Interface.bcast_of_mma hf.roleWarp hB hg hk.le hσ)
      (i0 := d.i - 1)
      (by omega) k hk hσ (Or.inl (by omega))
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
    have := pvAt_dst hpvE he0
    omega
  have hrow : r < 64 := by have := hr.1; omega
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
      have h1d := pvAt_dst hv hgo
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
  have hσ'c : St Q L X (G.cm (g / L.block)) k' = some (some (.w (.mma d' P))) := by
    rw [← hgcm]; exact hσ'
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
    refine .inr ⟨(t, sk), ?_, ?_⟩
    · rw [readSource_acc]
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
            · exact .inr (.inr (.inl (.inl (.inl (pv_ost_A' H l hv'.isMma rfl hpvS h3 ho hst
                (by omega))))))
          · exact .inr (.inl (by rw [h2]))
          · exact .inr (.inr (.inr (pv_before l.cm_ok.1 hpvE hv' h2)))
        · obtain ⟨hsh1', hsh2', w', ha'⟩ := ho'.shape
          have htt' : t = t' := ost_same_thread H l ho hj ha hcj ho' hj' ha' hcj'
          subst htt'
          have hit := V.ostIter (g / L.block) hcl ho ho'
          have hit' := V.ostIter (g / L.block) hcl ho' ho
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
    · intro v hv
      rw [← hcG]
      exact V.store (g / L.block) hcl (g := g) (b := d.i - 1) (r := r) (n := n) rfl (by omega)
        hr hn' hst ho hj (by rw [hcG]; exact hcj) hσ'c hs' (by omega) v
        (by rw [hcG, ← hgcm]; exact hv)
  · -- no rescale store of the iteration covers the cell: the earlier PV MMA is the source
    have hiN : d.i - 1 < Q.numIters (reqOf L g) (splitOf L g) := by
      have hpv : Mma.PvSite d.site := by rw [hs]; trivial
      have h1 := ((Interface.mma_inv_at hX hf hk hσ).pv hpv).2.1
      have h2 := Interface.mma_iters_loop hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩ (.inr hpv)
      simp only at h2
      omega
    refine .inl ⟨?_, V.skip (g / L.block) hcl rfl (by omega) hiN hr hn'
      (fun ⟨t, sk, a, vals, sh, j, hst, ho, hj, hc⟩ =>
        hex ⟨t, sk, a, vals, sh, j, hst, ho, hj, by rw [← hcG]; exact hc⟩)⟩
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

/-- **`Out.Inputs.oAcc`**: both fields of `OAcc` for the rescale factors `alpha`: `next` is
`Pr.oAccNext_of`, `base` is `oAccBase_of` (the orders here, the values `OAccPrem`). -/
theorem oAcc_of (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X)
    : OAcc Q L X alpha where
  next := Pr.oAccNext_of hpre hX hf hnc hns G st ht hmd
  base := oAccBase_of hpre hX hf hB hcomp hb hn hnc hns G st V ht hmd

end
end PTX.Kernels.InklingRelDecode.Proof.Rs
