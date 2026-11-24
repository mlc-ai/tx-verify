-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SrLayer
public import Kernels.InklingRelDecode.Proof.Interface.ShapeMma
public import Kernels.InklingRelDecode.Proof.Result.MmaO

@[expose] public section

/-!
# The accumulator chains of the QK and PV MMAs (`Out.Inputs.qkChain`, `OAcc.next`)

`Result.Mma.QkChain.prev` and the `next` field of `Result.Mma.OAcc`: QK (PV) step `j + 1` of an
iteration accumulates onto step `j`, whose event is the thread's previous event, and step `j` is the
accumulator read source (`ReadSource .acc`) of every cell step `j + 1` writes.

The statement has a thread-layer half and a protocol half.

* **Thread layer** (`mma_pred_adj`, `qkChain_of`): the predecessor of an MMA state at step `j + 1`
  is the state at step `j`, reached by the event just before (adjacency: `k' + 1 = k`; the
  library's `Interface.qk_pred` only says `k' < k`). Only the adjacency is proved here; the rest is
  `Interface.qk_pred`'s argument.
* **Protocol layer** (`qk_acc_source`, `pv_acc_source`): with the adjacency, `ReadSource .acc`
  of the previous step: the step wrote the cell (same descriptor, destination and CTA); it is
  written before the later step (the pipelined D-write pair); every other writer of the cell is
  before it or after the later step: the other MMAs of the lane by their event index (the
  index decides between the pipelined pairs, as no MMA of the lane lies between the two), the
  `P` stores (`Sr.qk_pst_A`, `qk_pst_B`: the same case for both steps, since they are of one
  block) and the rescale stores (`Sr.pv_ost_A`, `pv_ost_B`); and the later step is completed
  before every release of the allocation (`sourceLive_mma`, from `MmaDoneDealloc`).

The premises are `Sr.SrPkg` (the handshake data of every CTA: `Mbar.Ctx` and `Sr.Lane`),
`MmaStates` (the coordinates of the MMA states: the QK (PV) event at a state with site `qk` (`pv`)
of iteration `d.i` is `QkAt` of block `d.i` (`PvAt` of block `d.i - 1`)), `Tmem1Facts` and
`MmaDoneDealloc` (`Tmem1`), and `ThreadFacts`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Pr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)

noncomputable section

variable {Q : Params} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution}

/-! ### The accumulator read source -/

/-- **A later MMA of the CTA completes before every release of the allocation**, so a source of
its read is live. -/
theorem sourceLive_mma (hX : Consistent L K A mem0 X) (ht : Tmem1.Tmem1Facts L X 0)
    (hmd : Tmem1.MmaDoneDealloc L X) {source e : EvId} {cell : Cell} (he : IsMma X e)
    (hc : cell.cta = e.1 / L.block) : SourceLive L X source e cell := by
  intro cta r hr hcov d hrel
  obtain ⟨⟨pc, grp, a, n, hd⟩, hdc⟩ := Tmem1.release_info hX ht.toTmem1Ops hr hrel
  have hown := Tmem1.covers_owner hcov
  obtain ⟨hlc, -⟩ := Tmem1.record_info hX ht.toTmem1Ops hr
  have hcell : d.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  refine .inl ⟨fun ⟨a', vals, sh, hld⟩ => ?_, fun ⟨a', vals, sh, hst⟩ => ?_,
    fun _ => hmd he hd hcell⟩
  · exfalso
    obtain ⟨dd, s, ac, mask, pc1, h1⟩ := he
    obtain ⟨pc2, h2⟩ := hld
    rw [h1] at h2
    simp at h2
  · exfalso
    obtain ⟨dd, s, ac, mask, pc1, h1⟩ := he
    obtain ⟨pc2, h2⟩ := hst
    rw [h1] at h2
    simp at h2

/-- **Step `j` of a QK block is the accumulator read source of step `j + 1`**: two adjacent
events (`x.2 + 1 = y.2`) of the MMA lane that are QK MMAs of one block. -/
theorem qk_acc_source (hX : Consistent L K A mem0 X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
    (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L K A mem0 X) (ht : Tmem1.Tmem1Facts L X 0)
    (hmd : Tmem1.MmaDoneDealloc L X) {c : Nat} (hcl : c < L.grid) {x y : EvId} {i : Nat}
    (hx : QkAt L X c (G.cm c) (G.tm c) x i) (hy : QkAt L X c (G.cm c) (G.tm c) y i)
    (hth : x.2 + 1 = y.2) {cell : Cell} (hc : X.MmaCell y cell) :
    ReadSource L X .acc x y cell := by
  have l := G.lane c hcl
  have H := G.ctx c hcl
  have hc0 := hc
  obtain ⟨jy0, pcy0, ey0, hgy0, hqy0⟩ := hy.issue
  obtain ⟨h1, h2⟩ := SO.qk_cells l.tmOk hqy0 hgy0 hc0
  obtain ⟨jy, pcy, ey, hgy, day, dby, dscy, hdy, -, -, rfl⟩ := hy.issue
  obtain ⟨jx, pcx, ex, hgx, dax, dbx, dscx, hdx, -, -, rfl⟩ := hx.issue
  have hdsc : dscx = dscy := Option.some.inj (hdx.symm.trans hdy)
  subst hdsc
  obtain ⟨d, s, acc, mask, row, col, ⟨pc, hgy'⟩, hw⟩ := hc
  rw [hgy] at hgy'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hgy'
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hgy'
  have ix : WInfo L X c (G.cm c) (G.p0 c) (G.tm c) (G.Soft c) y cell := .qk hy h1 h2
  have hthr : x.1 = y.1 := hx.thread.trans hy.thread.symm
  have hg : x.1 < L.threads := hx.thread ▸ l.cm_ok.1
  have hyc : y.1 / L.block = c := hy.thread ▸ l.cm_ok.2
  rw [readSource_acc]
  refine ⟨?_, ?_, ?_, ?_, sourceLive_mma hX ht hmd hy.isMma (by rw [h2, hyc])⟩
  · intro h
    rw [h] at hth
    omega
  · exact .inl ⟨_, _, _, _, row, col, ⟨pcx, hgx⟩, hw⟩
  · exact .inl (Before.of_mma_po ⟨pcx, hgx⟩ ⟨pcy, hgy⟩ hg hthr (by omega) (sameAcc_qk rfl))
  · intro other hw'
    have hol := cta_lt hX (write_event hnc hns hw')
    have iy := winfo hnc hns (G.lane _ hol) hw' rfl
    have hxy : other.1 / L.block = c := iy.cta.symm.trans ix.cta
    rw [hxy] at iy
    have hpos : other.2 < x.2 ∨ other.2 = x.2 ∨ other.2 = y.2 ∨ y.2 < other.2 := by omega
    cases iy with
    | @qk _ _ i' hq' h1' _ =>
      have hpar := inS_parity h1 h1'
      rcases hpos with hlt | heq | heq | hgt
      · exact .inr (.inr (.inl (.inl (qk_before l.cm_ok.1 hq' hx hpar.symm hlt))))
      · exact .inl (Prod.ext (hq'.thread.trans hx.thread.symm) heq)
      · exact .inr (.inl (Prod.ext (hq'.thread.trans hy.thread.symm) heq))
      · exact .inr (.inr (.inr (qk_before l.cm_ok.1 hy hq' hpar hgt)))
    | @pv _ _ m' hv' h1' _ =>
      exact absurd h1' (SO.inS_inO_disjoint (Nat.mod_lt _ (by omega)) h1)
    | @pst t sk i' w j' a' vals sh cell' hst hp hj ha hc' hin _ =>
      have hpar := inS_parity h1 (SO.inP_inS hin)
      by_cases hle : i / 2 ≤ i' / 2
      · exact .inr (.inr (.inr (.inl (qk_pst_A H l hy hp hst hpar hle))))
      · exact .inr (.inr (.inl (.inr (.inl (qk_pst_B H l hx hp hst hpar hle)))))
    | @ost t sk i' w j' a' vals sh cell' hst ho hj ha hc' hin _ =>
      exact absurd hin (SO.inS_inO_disjoint (Nat.mod_lt _ (by omega)) h1)

/-- **Step `j` of a PV block is the accumulator read source of step `j + 1`.** -/
theorem pv_acc_source (hX : Consistent L K A mem0 X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
    (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L K A mem0 X) (ht : Tmem1.Tmem1Facts L X 0)
    (hmd : Tmem1.MmaDoneDealloc L X) {c : Nat} (hcl : c < L.grid) {x y : EvId} {m : Nat}
    (hx : PvAt L X c (G.cm c) (G.tm c) x m) (hy : PvAt L X c (G.cm c) (G.tm c) y m)
    (hth : x.2 + 1 = y.2) {cell : Cell} (hc : X.MmaCell y cell) :
    ReadSource L X .acc x y cell := by
  have l := G.lane c hcl
  have H := G.ctx c hcl
  have hc0 := hc
  obtain ⟨jy0, pcy0, ey0, hjy0, hgy0, hqy0⟩ := hy.issue
  obtain ⟨h1, h2⟩ := SO.pv_cells l.tmOk hqy0 hgy0 hc0
  obtain ⟨jy, pcy, ey, hjy, hgy, dby, dscy, hdy, -, rfl⟩ := hy.issue
  obtain ⟨jx, pcx, ex, hjx, hgx, dbx, dscx, hdx, -, rfl⟩ := hx.issue
  have hdsc : dscx = dscy := Option.some.inj (hdx.symm.trans hdy)
  subst hdsc
  obtain ⟨d, s, acc, mask, row, col, ⟨pc, hgy'⟩, hw⟩ := hc
  rw [hgy] at hgy'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hgy'
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hgy'
  have iy0 : WInfo L X c (G.cm c) (G.p0 c) (G.tm c) (G.Soft c) y cell := .pv hy h1 h2
  have hthr : x.1 = y.1 := hx.thread.trans hy.thread.symm
  have hg : x.1 < L.threads := hx.thread ▸ l.cm_ok.1
  have hyc : y.1 / L.block = c := hy.thread ▸ l.cm_ok.2
  rw [readSource_acc]
  refine ⟨?_, ?_, ?_, ?_, sourceLive_mma hX ht hmd hy.isMma (by rw [h2, hyc])⟩
  · intro h
    rw [h] at hth
    omega
  · exact .inl ⟨_, _, _, _, row, col, ⟨pcx, hgx⟩, hw⟩
  · exact .inl (Before.of_mma_po ⟨pcx, hgx⟩ ⟨pcy, hgy⟩ hg hthr (by omega) sameAcc_pv)
  · intro other hw'
    have hol := cta_lt hX (write_event hnc hns hw')
    have iy := winfo hnc hns (G.lane _ hol) hw' rfl
    have hxy : other.1 / L.block = c := iy.cta.symm.trans iy0.cta
    rw [hxy] at iy
    have hpos : other.2 < x.2 ∨ other.2 = x.2 ∨ other.2 = y.2 ∨ y.2 < other.2 := by omega
    cases iy with
    | @qk _ _ i' hq' h1' _ =>
      exact absurd h1 (SO.inS_inO_disjoint (Nat.mod_lt _ (by omega)) h1')
    | @pv _ _ m' hv' h1' _ =>
      rcases hpos with hlt | heq | heq | hgt
      · exact .inr (.inr (.inl (.inl (pv_before l.cm_ok.1 hv' hx hlt))))
      · exact .inl (Prod.ext (hv'.thread.trans hx.thread.symm) heq)
      · exact .inr (.inl (Prod.ext (hv'.thread.trans hy.thread.symm) heq))
      · exact .inr (.inr (.inr (pv_before l.cm_ok.1 hy hv' hgt)))
    | @pst t sk i' w j' a' vals sh cell' hst hp hj ha hc' hin _ =>
      exact absurd h1 (SO.inP_inO_disjoint (Nat.mod_lt _ (by omega)) hin)
    | @ost t sk i' w j' a' vals sh cell' hst ho hj ha hc' hin _ =>
      by_cases hle : m ≤ i' - 1
      · exact .inr (.inr (.inr (.inl (pv_ost_A H l hy ho hst hle))))
      · exact .inr (.inr (.inl (.inr (.inl (pv_ost_B H l hx ho hst hle)))))


/-! ### The thread layer: the predecessor state -/

open PTX.Kernels.InklingRelDecode.Proof.Interface in
/-- **A state before event `k0 + 1` has its predecessor at `k0`** (adjacency). -/
theorem pred_adj {g k0 : Nat} {s : TSt} (hk : k0 < (X.tr g).length)
    (h : St Q L X g (k0 + 1) = some (some s)) :
    ∃ (e : Event) (s0 : TSt), (X.tr g)[k0]? = some e ∧ St Q L X g k0 = some (some s0) ∧
      (threadCode L g Q).next s0 e = some (some s) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  refine ⟨e, ?_⟩
  have hs' := h
  rw [St, Frame.stateAt_succ he] at hs'
  cases hk0 : St Q L X g k0 with
  | none => simp [St] at hk0 hs'; simp [hk0] at hs'
  | some σ =>
    cases σ with
    | none =>
      have : Frame.stateAt (code L Q) X g k0 = some none := hk0
      rw [this] at hs'
      simp [Code.toMachine] at hs'
    | some s0 =>
      have : Frame.stateAt (code L Q) X g k0 = some (some s0) := hk0
      rw [this] at hs'
      exact ⟨s0, he, rfl, hs'⟩

open PTX.Kernels.InklingRelDecode.Proof.Interface in
/-- **The MMA state before an MMA state at event `k0 + 1` is at `k0`**: the event `k0` fired from
an MMA state `d0` of the same worker, whose successor is the state. -/
theorem mma_pred_adj {g k0 : Nat} {d : Mma.D} {P : Loader.Pro} (hs : d.site ≠ .setMaxReg)
    (hk : k0 < (X.tr g).length) (hσ : St Q L X g (k0 + 1) = some (some (.w (.mma d P)))) :
    ∃ (e : Event) (d0 : Mma.D), X.get (g, k0) = some e ∧
      St Q L X g k0 = some (some (.w (.mma d0 P))) ∧ Mma.next L g d0 e = some (some d) := by
  obtain ⟨e, s0, he, hs0, hn⟩ := pred_adj hk hσ
  refine ⟨e, ?_⟩
  cases s0 with
  | d s =>
    rw [next_d] at hn
    obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
    cases h
  | w s =>
    rw [next_w] at hn
    obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
    cases h
    obtain ⟨d0, rfl, hd0⟩ := wcomp_next_mma ha hs
    exact ⟨d0, he, hs0, hd0⟩

/-- **The coordinates of the MMA states**: the event at a state with site `qk` of iteration `d.i`
is a QK MMA of block `d.i`, the event at a state with site `pv` is a PV MMA of block `d.i - 1`
(the thread layer: `SOMmaExec`'s counts at the state, the shapes `EvW.QkIssue`, `EvW.PvIssue`). -/
structure MmaStates (Q : Params) (L : Launch) (G : SrPkg L K A mem0 X) : Prop where
  qk : ∀ {g k : Nat} {j : Fin 8} {d : Mma.D} {P : Loader.Pro}, g < L.threads →
    k < (X.tr g).length → St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
    QkAt L X (g / L.block) (G.cm (g / L.block)) (G.tm (g / L.block)) (g, k) d.i
  pv : ∀ {g k : Nat} {j : Fin 8} {d : Mma.D} {P : Loader.Pro}, g < L.threads →
    k < (X.tr g).length → St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j →
    1 ≤ d.i ∧ PvAt L X (g / L.block) (G.cm (g / L.block)) (G.tm (g / L.block)) (g, k) (d.i - 1)

open PTX.Kernels.InklingRelDecode.Proof.Interface in
/-- **`Out.Inputs.qkChain`.** -/
theorem qkChain_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
    (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L kernel Assumptions.all mem0 X)
    (st : MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X) :
    Result.Mma.QkChain Q L X where
  prev := by
    intro g k j d P hj hσ hs
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have hg : g < L.threads := event_thread_lt hX he
      have hk1 : k ≠ 0 := by
        rintro rfl
        have h0 := hσ
        rw [St, Frame.stateAt_zero] at h0
        exact mma_ne_init d P (Option.some.inj (Option.some.inj h0)).symm
      obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
      have hk0 : k0 < (X.tr g).length := by omega
      obtain ⟨e0, d0, he0, hs0, hn⟩ := mma_pred_adj (by rw [hs]; simp) hk0 hσ
      obtain ⟨h1, h2⟩ := mma_next_qk hj hn hs
      have hd0 : d0 = { d with site := .qk ⟨j, by omega⟩ } := by
        cases d0
        cases d
        simp only [Mma.D.mk.injEq] at h2 ⊢
        simp_all
      subst hd0
      obtain ⟨pc, dst, sp, acc, mask, hev⟩ := mma_issue_event hpre hX hf hg he0 hs0
        (.inl ⟨⟨j, by omega⟩, rfl⟩)
      refine ⟨k0, by omega, hs0, ⟨pc, dst, sp, acc, mask, by rw [he0, hev]⟩, ?_⟩
      intro cell hc
      have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
      exact qk_acc_source hX hnc hns G ht hmd hcl (st.qk hg hk0 hs0 rfl)
        (st.qk (d := d) hg hk hσ hs) rfl hc
    · obtain ⟨k', hlt, hs0, hmma⟩ := qk_pred hpre hX hf hj hσ hs
      refine ⟨k', hlt, hs0, hmma, fun cell hc => ?_⟩
      exfalso
      obtain ⟨d', s', acc', mask', row, col, ⟨pc, hget⟩, -⟩ := hc
      exact hk (len_of_get hget)

open PTX.Kernels.InklingRelDecode.Proof.Interface in
/-- **`Result.Mma.OAcc.next`.** -/
theorem oAccNext_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
    (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L kernel Assumptions.all mem0 X)
    (st : MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hmd : Tmem1.MmaDoneDealloc L X) :
    ∀ {g k j : Nat} {d : Mma.D} {P : Loader.Pro} (hj : j + 1 < 8),
      St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv ⟨j + 1, hj⟩ →
      ∃ k', k' < k ∧ St Q L X g k' =
          some (some (.w (.mma { d with site := .pv ⟨j, by omega⟩ } P))) ∧
        (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
        ∀ cell, X.MmaCell (g, k) cell → TcMma.ReadSource L X .acc (g, k') (g, k) cell := by
  intro g k j d P hj hσ hs
  by_cases hk : k < (X.tr g).length
  · obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    have hg : g < L.threads := event_thread_lt hX he
    have hk1 : k ≠ 0 := by
      rintro rfl
      have h0 := hσ
      rw [St, Frame.stateAt_zero] at h0
      exact mma_ne_init d P (Option.some.inj (Option.some.inj h0)).symm
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    have hk0 : k0 < (X.tr g).length := by omega
    obtain ⟨e0, d0, he0, hs0, hn⟩ := mma_pred_adj (by rw [hs]; simp) hk0 hσ
    obtain ⟨h1, h2⟩ := mma_next_pv hj hn hs
    have hd0 : d0 = { d with site := .pv ⟨j, by omega⟩ } := by
      cases d0
      cases d
      simp only [Mma.D.mk.injEq] at h2 ⊢
      simp_all
    subst hd0
    obtain ⟨pc, dst, sp, acc, mask, hev⟩ := mma_issue_event hpre hX hf hg he0 hs0
      (.inr ⟨⟨j, by omega⟩, rfl⟩)
    refine ⟨k0, by omega, hs0, ⟨pc, dst, sp, acc, mask, by rw [he0, hev]⟩, ?_⟩
    intro cell hc
    have hcl : g / L.block < L.grid := cta_lt hX ⟨_, he⟩
    exact pv_acc_source hX hnc hns G ht hmd hcl (st.pv hg hk0 hs0 rfl).2
      (st.pv (d := d) hg hk hσ hs).2 rfl hc
  · obtain ⟨k', hlt, hs0, hmma⟩ := pv_pred hpre hX hf hj hσ hs
    refine ⟨k', hlt, hs0, hmma, fun cell hc => ?_⟩
    exfalso
    obtain ⟨d', s', acc', mask', row, col, ⟨pc, hget⟩, -⟩ := hc
    exact hk (len_of_get hget)

end
end PTX.Kernels.InklingRelDecode.Proof.Pr
