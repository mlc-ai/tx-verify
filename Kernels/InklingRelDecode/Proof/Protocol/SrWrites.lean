-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SrCoord

@[expose] public section

/-!
# The Tensor Memory write branch of `Unsafe` (`Safety.Protocol.tcWrites`)

`¬ TcMma.WritesUnsafe L X`: every two writers of one Tensor Memory cell are ordered. The writers
of the kernel are the QK MMAs (the score buffers `S b`), the PV MMAs (the accumulator `O`), the
`P` stores (the first half of `S b`) and the rescale stores (`O`); there is no `tcgen05.cp` or
`tcgen05.shift`. The orders, per pair of writer kinds:

* **QK, QK** and **PV, PV** (`qk_qk_order`, `pv_pv_order`): one thread (the MMA lane), the same
  accumulator, in program order: the pipelined D-write pair (`Before.of_mma_po`);
* **QK and `P` store** (`qk_pst_order`): a QK MMA of block `i` and a `P` store of block `i'` of the
  same buffer: if `i / 2 ≤ i' / 2` the MMA is done before the store (the store's thread polled
  `s_ready` for a use that follows the MMA's commit: `mma_before_s_store`), else the store is done
  before the MMA (the lane polled `p_ready` for the store's use, after the store's `wait::st` and
  the barrier before thread 0's arrival: `store_before_mma`);
* **PV and rescale store** (`pv_ost_order`): a PV MMA of block `m` and the rescale store of
  iteration `i`: if `m ≤ i - 1` the MMA is done before the store (the store's thread polled
  `o_done` after `i - 1` commits: `mma_before_o_store`), else the store is done before the MMA
  (the lane polled `p_ready (i % 2)` for a use above the iteration's);
* **`P` store, `P` store** and **rescale store, rescale store** (`pst_pst_order`,
  `ost_ost_order`): the cell fixes the thread (`Sr.split_thread`), and one thread's stores are
  pipelined in program order (`StoreDoneBefore.of_po`);
* the other pairs have no common cell: `S`, `P` and `O` are disjoint columns (`SOTmemCols`).

`no_writes_unsafe` is `Safety.Protocol.tcWrites`, from `Mbar.Ctx` and `Lane` of every CTA
(the development notes, "Protocol `Sr`").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InP InO TmOk below2)

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {c cm p0 tm : Nat} {Soft Mma : Nat → Prop}

/-! ### The writer kinds of one CTA -/

/-- **A Tensor Memory write of CTA `c`, classified**: a QK MMA of block `i` and a cell of
`S (i % 2)`, a PV MMA and a cell of `O`, or a `tcgen05.st` of a softmax thread, the `P` store or
the rescale store, with the register slot `j` and the cell. -/
inductive WInfo (L : Launch) (X : Execution) (c cm p0 tm : Nat) (Soft : Nat → Prop) :
    EvId → Cell → Prop
  | qk {x : EvId} {cell : Cell} {i : Nat} : QkAt L X c cm tm x i → InS tm (i % 2) cell.column →
      cell.cta = c → WInfo L X c cm p0 tm Soft x cell
  | pv {x : EvId} {cell : Cell} {m : Nat} : PvAt L X c cm tm x m → InO tm cell.column →
      cell.cta = c → WInfo L X c cm p0 tm Soft x cell
  | pst {t sk i w j a : Nat} {vals : List Value} {sh : TcShape} {cell : Cell} :
      X.TSt (t, sk) a vals sh → PSt L X c p0 Soft tm t sk i a vals sh → j < 32 →
      a = tm + 128 * (i % 2) + w * 2 ^ 21 →
      cell = tcDataCell L t (.s16x32bx2 32) a j → InP tm (i % 2) cell.column → cell.cta = c →
      WInfo L X c cm p0 tm Soft (t, sk) cell
  | ost {t sk i w j a : Nat} {vals : List Value} {sh : TcShape} {cell : Cell} :
      X.TSt (t, sk) a vals sh → OSt L X c p0 Soft tm t sk i a vals sh → j < 64 →
      a = tm + 256 + w * 2 ^ 21 →
      cell = tcDataCell L t (.s16x32bx2 64) a j → InO tm cell.column → cell.cta = c →
      WInfo L X c cm p0 tm Soft (t, sk) cell

/-- **A write of a cell by an event of CTA `c` is classified.** -/
theorem winfo (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (l : Lane L X c cm p0 tm Soft) {w : EvId} {cell : Cell} (hw : TmemWrite L X w cell)
    (hwc : w.1 / L.block = c) : WInfo L X c cm p0 tm Soft w cell := by
  rcases tmemWrite_of_no_copy hnc hns hw with hm | ⟨a, vals, sh, j, hst, hj, hcell⟩
  · obtain ⟨d, s, acc, mask, row, col, hi, -⟩ := id hm
    rcases l.mma ⟨d, s, acc, mask, hi⟩ hwc with ⟨i, hq⟩ | ⟨m, hv⟩
    · obtain ⟨j, pc, e, hget, hq'⟩ := hq.issue
      obtain ⟨h1, h2⟩ := SO.qk_cells l.tmOk hq' hget hm
      exact .qk hq h1 h2
    · obtain ⟨j, pc, e, hj, hget, hq'⟩ := hv.issue
      obtain ⟨h1, h2⟩ := SO.pv_cells l.tmOk hq' hget hm
      exact .pv hv h1 h2
  · obtain ⟨t, sk⟩ := w
    rcases l.st hst hwc with ⟨i, hp⟩ | ⟨i, ho⟩
    · obtain ⟨rfl, hl, w, ha⟩ := hp.shape
      have hj' : j < 32 := hl ▸ hj
      have hc := pstore_cells (L := L) (g := t) (b := i % 2) (w := w) (j := j) (c := c) l.tmOk
        (Nat.mod_lt _ (by omega)) hj' hwc
      rw [← ha] at hc
      exact .pst hst hp hj' ha hcell (by rw [hcell]; exact hc.1) (by rw [hcell]; exact hc.2)
    · obtain ⟨rfl, hl, w, ha⟩ := ho.shape
      have hj' : j < 64 := hl ▸ hj
      have hc := ostore_cells (L := L) (g := t) (w := w) (j := j) (c := c) l.tmOk hj' hwc
      rw [← ha] at hc
      exact .ost hst ho hj' ha hcell (by rw [hcell]; exact hc.1) (by rw [hcell]; exact hc.2)

/-! ### The pairs -/

/-- The ordered-or-equal relation of two writers. -/
def WOrd (L : Launch) (X : Execution) (x y : EvId) : Prop :=
  x = y ∨ WriteBefore L X x y ∨ WriteBefore L X y x

theorem WOrd.symm {x y : EvId} (h : WOrd L X x y) : WOrd L X y x := by
  rcases h with h | h | h
  · exact .inl h.symm
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- Two columns of distinct buffers are distinct. -/
theorem inS_parity {i i' col : Nat} (h : InS tm (i % 2) col) (h' : InS tm (i' % 2) col) :
    i % 2 = i' % 2 := by
  by_contra hne
  exact SO.inS_disjoint hne h h'

theorem inP_parity {i i' col : Nat} (h : InP tm (i % 2) col) (h' : InP tm (i' % 2) col) :
    i % 2 = i' % 2 := by
  by_contra hne
  unfold InP at h h'
  omega

/-- The accumulators of two QK MMAs of one buffer are the same. -/
theorem sameAcc_qk {dsc : Descriptor} {da db da' db' : TcShared.Descriptor} {b b' cta : Nat}
    (h : b = b') :
    SameAccumulator (tm + 128 * b) ⟨dsc, da, db, cta, cta, none, {}⟩
      (tm + 128 * b') ⟨dsc, da', db', cta, cta, none, {}⟩ :=
  ⟨by rw [h], rfl, rfl, rfl, rfl⟩

/-- **Two QK MMAs of one buffer are ordered** (the pipelined D-write pair). -/
theorem qk_qk_order (hcm : cm < L.threads) {x y : EvId} {i i' : Nat}
    (hx : QkAt L X c cm tm x i) (hy : QkAt L X c cm tm y i') (hpar : i % 2 = i' % 2) :
    x = y ∨ Before L X x y ∨ Before L X y x := by
  obtain ⟨j, pc, e, hxg, da, db, dsc, hd, -, -, rfl⟩ := hx.issue
  obtain ⟨j', pc', e', hyg, da', db', dsc', hd', -, -, rfl⟩ := hy.issue
  have hdsc : dsc = dsc' := Option.some.inj (hd.symm.trans hd')
  subst hdsc
  have hthr : x.1 = y.1 := hx.thread.trans hy.thread.symm
  have hg : x.1 < L.threads := hx.thread ▸ hcm
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact .inr (.inl (Before.of_mma_po ⟨pc, hxg⟩ ⟨pc', hyg⟩ hg hthr hlt
      (sameAcc_qk (tm := tm) (by rw [hpar]))))
  · exact .inl (Prod.ext hthr heq)
  · exact .inr (.inr (Before.of_mma_po ⟨pc', hyg⟩ ⟨pc, hxg⟩ (hthr ▸ hg) hthr.symm hgt
      (sameAcc_qk (tm := tm) (by rw [hpar]))))

/-- The accumulators of two PV MMAs are the same. -/
theorem sameAcc_pv {dsc : Descriptor} {db db' : TcShared.Descriptor} {tm cta ta ta' : Nat} :
    SameAccumulator (tm + 256) ⟨dsc, db, db, cta, cta, some ta, {}⟩
      (tm + 256) ⟨dsc, db', db', cta, cta, some ta', {}⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Two PV MMAs are ordered** (the pipelined D-write pair). -/
theorem pv_pv_order (hcm : cm < L.threads) {x y : EvId} {m m' : Nat}
    (hx : PvAt L X c cm tm x m) (hy : PvAt L X c cm tm y m') :
    x = y ∨ Before L X x y ∨ Before L X y x := by
  obtain ⟨j, pc, e, hj, hxg, db, dsc, hd, -, rfl⟩ := hx.issue
  obtain ⟨j', pc', e', hj', hyg, db', dsc', hd', -, rfl⟩ := hy.issue
  have hdsc : dsc = dsc' := Option.some.inj (hd.symm.trans hd')
  subst hdsc
  have hthr : x.1 = y.1 := hx.thread.trans hy.thread.symm
  have hg : x.1 < L.threads := hx.thread ▸ hcm
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact .inr (.inl (Before.of_mma_po ⟨pc, hxg⟩ ⟨pc', hyg⟩ hg hthr hlt sameAcc_pv))
  · exact .inl (Prod.ext hthr heq)
  · exact .inr (.inr (Before.of_mma_po ⟨pc', hyg⟩ ⟨pc, hxg⟩ (hthr ▸ hg) hthr.symm hgt
      sameAcc_pv))

/-- **A QK MMA is `Before` a later QK MMA of the same buffer** (the pipelined D-write pair). -/
theorem qk_before (hcm : cm < L.threads) {x y : EvId} {i i' : Nat}
    (hx : QkAt L X c cm tm x i) (hy : QkAt L X c cm tm y i') (hpar : i % 2 = i' % 2)
    (hlt : x.2 < y.2) : Before L X x y := by
  obtain ⟨j, pc, e, hxg, da, db, dsc, hd, -, -, rfl⟩ := hx.issue
  obtain ⟨j', pc', e', hyg, da', db', dsc', hd', -, -, rfl⟩ := hy.issue
  have hdsc : dsc = dsc' := Option.some.inj (hd.symm.trans hd')
  subst hdsc
  exact Before.of_mma_po ⟨pc, hxg⟩ ⟨pc', hyg⟩ (hx.thread ▸ hcm) (hx.thread.trans hy.thread.symm)
    hlt (sameAcc_qk (tm := tm) hpar)

/-- **A PV MMA is `Before` a later PV MMA** (the pipelined D-write pair). -/
theorem pv_before (hcm : cm < L.threads) {x y : EvId} {m m' : Nat}
    (hx : PvAt L X c cm tm x m) (hy : PvAt L X c cm tm y m') (hlt : x.2 < y.2) :
    Before L X x y := by
  obtain ⟨j, pc, e, hj, hxg, db, dsc, hd, -, rfl⟩ := hx.issue
  obtain ⟨j', pc', e', hj', hyg, db', dsc', hd', -, rfl⟩ := hy.issue
  have hdsc : dsc = dsc' := Option.some.inj (hd.symm.trans hd')
  subst hdsc
  exact Before.of_mma_po ⟨pc, hxg⟩ ⟨pc', hyg⟩ (hx.thread ▸ hcm) (hx.thread.trans hy.thread.symm)
    hlt sameAcc_pv

/-- A QK MMA is an MMA. -/
theorem QkAt.isMma {x : EvId} {i : Nat} (h : QkAt L X c cm tm x i) : IsMma X x := by
  obtain ⟨j, pc, e, hget, da, db, dsc, hd, -, -, rfl⟩ := h.issue
  exact ⟨_, _, _, _, pc, hget⟩

/-- A PV MMA is an MMA. -/
theorem PvAt.isMma {x : EvId} {m : Nat} (h : PvAt L X c cm tm x m) : IsMma X x := by
  obtain ⟨j, pc, e, hj, hget, db, dsc, hd, -, rfl⟩ := h.issue
  exact ⟨_, _, _, _, pc, hget⟩

/-- The events of the MMA lane are in range. -/
theorem lane_len {x : EvId} (hx : x.1 = cm) {ev : Event} (h : X.get x = some ev) :
    x.2 < (X.tr cm).length := hx ▸ len_of_get h

variable (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma) (l : Lane L X c cm p0 tm Soft)
include H l

/-- **A QK MMA is done before the `P` store of a use that is not before its own**
(`i / 2 ≤ i' / 2`, one buffer). -/
theorem qk_pst_A {x : EvId} {i t sk i' a : Nat} {vals : List Value} {sh : TcShape}
    (hq : QkAt L X c cm tm x i) (hp : PSt L X c p0 Soft tm t sk i' a vals sh)
    (hst : X.TSt (t, sk) a vals sh) (hpar : i % 2 = i' % 2) (hle : i / 2 ≤ i' / 2) :
    DoneBefore L X x (t, sk) := by
  have hxc : x.1 / L.block = c := hq.thread ▸ l.cm_ok.2
  refine mma_before_s_store H (Nat.mod_lt _ (by omega)) l.cm_ok.1 l.cm_ok.2
    (fun hx hc => l.mma_thread hx hc) hp.gate hst hq.isMma hxc ?_
  rw [← hpar]
  exact le_trans hq.sCommits hle

/-- **The `P` store of an earlier use is done before a QK MMA** (`i' / 2 < i / 2`, one buffer). -/
theorem qk_pst_B {x : EvId} {i t sk i' a : Nat} {vals : List Value} {sh : TcShape}
    (hq : QkAt L X c cm tm x i) (hp : PSt L X c p0 Soft tm t sk i' a vals sh)
    (hst : X.TSt (t, sk) a vals sh) (hpar : i % 2 = i' % 2) (hlt : ¬ i / 2 ≤ i' / 2) :
    StoreDoneBefore L X (t, sk) x := by
  have hb : i' % 2 < 2 := Nat.mod_lt _ (by omega)
  have hf : i' / 2 + 1 ≤ okPolls (pReady L c (i' % 2)) ((X.tr cm).take x.2) := by
    rw [← hpar]
    have := hq.pPolls
    omega
  obtain ⟨j, pc, e, hget, -⟩ := hq.issue
  have h := store_before_mma H hb l.cm_ok.1 l.cm_ok.2
    (fun hw => l.pAcq hb hw) hp.gate hst hf (lane_len hq.thread hget)
  have hx : x = (cm, x.2) := Prod.ext hq.thread rfl
  rw [hx]
  exact h

/-- **A QK MMA and a `P` store of one buffer are ordered**: by the polls of `s_ready`
(`i / 2 ≤ i' / 2`) or of `p_ready` (otherwise). -/
theorem qk_pst_order {x : EvId} {i t sk i' a : Nat} {vals : List Value} {sh : TcShape}
    (hq : QkAt L X c cm tm x i) (hp : PSt L X c p0 Soft tm t sk i' a vals sh)
    (hst : X.TSt (t, sk) a vals sh) (hpar : i % 2 = i' % 2) :
    DoneBefore L X x (t, sk) ∨ StoreDoneBefore L X (t, sk) x := by
  by_cases hle : i / 2 ≤ i' / 2
  · exact .inl (qk_pst_A H l hq hp hst hpar hle)
  · exact .inr (qk_pst_B H l hq hp hst hpar hle)

/-- **A PV MMA is done before the rescale store of an iteration after its block** (`m ≤ i - 1`). -/
theorem pv_ost_A {x : EvId} {m t sk i a : Nat} {vals : List Value} {sh : TcShape}
    (hv : PvAt L X c cm tm x m) (ho : OSt L X c p0 Soft tm t sk i a vals sh)
    (hst : X.TSt (t, sk) a vals sh) (hm : m ≤ i - 1) : DoneBefore L X x (t, sk) := by
  have hxc : x.1 / L.block = c := hv.thread ▸ l.cm_ok.2
  exact mma_before_o_store H l.cm_ok.1 l.cm_ok.2 (fun hx hc => l.mma_thread hx hc) ho.gate hst
    hv.isMma hxc (le_trans hv.oCommits hm)

/-- **The rescale store of iteration `i` is done before a PV MMA of block `m ≥ i`.** -/
theorem pv_ost_B {x : EvId} {m t sk i a : Nat} {vals : List Value} {sh : TcShape}
    (hv : PvAt L X c cm tm x m) (ho : OSt L X c p0 Soft tm t sk i a vals sh)
    (hst : X.TSt (t, sk) a vals sh) (hm : ¬ m ≤ i - 1) : StoreDoneBefore L X (t, sk) x := by
  have hb : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hf : i / 2 + 1 ≤ okPolls (pReady L c (i % 2)) ((X.tr cm).take x.2) := by
    have := hv.pPolls (i % 2) hb
    unfold SO.below2 at this
    omega
  obtain ⟨j, pc, e, hj, hget, -⟩ := hv.issue
  have h := store_before_mma H hb l.cm_ok.1 l.cm_ok.2
    (fun hw => l.pAcq hb hw) ho.gate hst hf (lane_len hv.thread hget)
  have hx : x = (cm, x.2) := Prod.ext hv.thread rfl
  rw [hx]
  exact h

/-- **A PV MMA and the rescale store are ordered**: by the polls of `o_done` (`m ≤ i - 1`) or of
`p_ready` (otherwise). -/
theorem pv_ost_order {x : EvId} {m t sk i a : Nat} {vals : List Value} {sh : TcShape}
    (hv : PvAt L X c cm tm x m) (ho : OSt L X c p0 Soft tm t sk i a vals sh)
    (hst : X.TSt (t, sk) a vals sh) :
    DoneBefore L X x (t, sk) ∨ StoreDoneBefore L X (t, sk) x := by
  by_cases hm : m ≤ i - 1
  · exact .inl (pv_ost_A H l hv ho hst hm)
  · exact .inr (pv_ost_B H l hv ho hst hm)

/-- **Two `P` stores writing one cell are ordered** (one thread, program order). -/
theorem pst_pst_order {t sk i w j a t' sk' i' w' j' a' : Nat} {vals vals' : List Value}
    {sh sh' : TcShape} {cell : Cell} (hst : X.TSt (t, sk) a vals sh)
    (hp : PSt L X c p0 Soft tm t sk i a vals sh) (hj : j < 32)
    (ha : a = tm + 128 * (i % 2) + w * 2 ^ 21)
    (hc : cell = tcDataCell L t (.s16x32bx2 32) a j) (hin : InP tm (i % 2) cell.column)
    (hst' : X.TSt (t', sk') a' vals' sh') (hp' : PSt L X c p0 Soft tm t' sk' i' a' vals' sh')
    (hj' : j' < 32) (ha' : a' = tm + 128 * (i' % 2) + w' * 2 ^ 21)
    (hc' : cell = tcDataCell L t' (.s16x32bx2 32) a' j')
    (hin' : InP tm (i' % 2) cell.column) : WOrd L X (t, sk) (t', sk') := by
  obtain ⟨ht, htc, htb⟩ := soft_info H hp.gate.soft
  obtain ⟨ht', htc', htb'⟩ := soft_info H hp'.gate.soft
  have hpar := inP_parity hin hin'
  have hba : tm + 128 * (i % 2) + 32 < 2 ^ 16 := by
    have := l.tmOk
    unfold TmOk at this
    omega
  rw [ha] at hc
  rw [ha', ← hpar] at hc'
  have hteq : t = t' :=
    split_thread hba hj hj' htb htb' (htc.trans htc'.symm) (hc.symm.trans hc')
  subst hteq
  have hg : (t, sk).1 < L.threads := ht
  rcases Nat.lt_trichotomy sk sk' with hlt | heq | hgt
  · exact .inr (.inl (.inr (.inl (StoreDoneBefore.of_po hst hst' hg rfl hlt))))
  · exact .inl (by rw [heq])
  · exact .inr (.inr (.inr (.inl (StoreDoneBefore.of_po hst' hst hg rfl hgt))))

/-- **Two rescale stores writing one cell are ordered** (one thread, program order). -/
theorem ost_ost_order {t sk i w j a t' sk' i' w' j' a' : Nat} {vals vals' : List Value}
    {sh sh' : TcShape} {cell : Cell} (hst : X.TSt (t, sk) a vals sh)
    (hp : OSt L X c p0 Soft tm t sk i a vals sh) (hj : j < 64)
    (ha : a = tm + 256 + w * 2 ^ 21) (hc : cell = tcDataCell L t (.s16x32bx2 64) a j)
    (hst' : X.TSt (t', sk') a' vals' sh') (hp' : OSt L X c p0 Soft tm t' sk' i' a' vals' sh')
    (hj' : j' < 64) (ha' : a' = tm + 256 + w' * 2 ^ 21)
    (hc' : cell = tcDataCell L t' (.s16x32bx2 64) a' j') : WOrd L X (t, sk) (t', sk') := by
  obtain ⟨ht, htc, htb⟩ := soft_info H hp.gate.soft
  obtain ⟨ht', htc', htb'⟩ := soft_info H hp'.gate.soft
  have hba : tm + 256 + 64 < 2 ^ 16 := by
    have := l.tmOk
    unfold TmOk at this
    omega
  rw [ha] at hc
  rw [ha'] at hc'
  have hteq : t = t' :=
    split_thread hba hj hj' htb htb' (htc.trans htc'.symm) (hc.symm.trans hc')
  subst hteq
  have hg : (t, sk).1 < L.threads := ht
  rcases Nat.lt_trichotomy sk sk' with hlt | heq | hgt
  · exact .inr (.inl (.inr (.inl (StoreDoneBefore.of_po hst hst' hg rfl hlt))))
  · exact .inl (by rw [heq])
  · exact .inr (.inr (.inr (.inl (StoreDoneBefore.of_po hst' hst hg rfl hgt))))

/-- **Two writers of one cell of CTA `c` are ordered.** -/
theorem winfo_order {x y : EvId} {cell : Cell} (hx : WInfo L X c cm p0 tm Soft x cell)
    (hy : WInfo L X c cm p0 tm Soft y cell) : WOrd L X x y := by
  have hb2 : ∀ n : Nat, n % 2 < 2 := fun n => Nat.mod_lt _ (by omega)
  cases hx with
  | qk hq h1 _ =>
    cases hy with
    | qk hq' h1' _ =>
      rcases qk_qk_order l.cm_ok.1 hq hq' (inS_parity h1 h1') with h | h | h
      · exact .inl h
      · exact .inr (.inl (.inl h))
      · exact .inr (.inr (.inl h))
    | pv _ h1' _ => exact absurd h1' (SO.inS_inO_disjoint (hb2 _) h1)
    | pst hst hp hj ha hc hin _ =>
      rcases qk_pst_order H l hq hp hst (inS_parity h1 (SO.inP_inS hin)) with h | h
      · exact .inr (.inl (WriteBefore.of_done h))
      · exact .inr (.inr (.inr (.inl h)))
    | ost _ _ _ _ _ hin _ => exact absurd hin (SO.inS_inO_disjoint (hb2 _) h1)
  | pv hv h1 _ =>
    cases hy with
    | qk _ h1' _ => exact absurd h1 (SO.inS_inO_disjoint (hb2 _) h1')
    | pv hv' h1' _ =>
      rcases pv_pv_order l.cm_ok.1 hv hv' with h | h | h
      · exact .inl h
      · exact .inr (.inl (.inl h))
      · exact .inr (.inr (.inl h))
    | pst _ _ _ _ _ hin _ => exact absurd h1 (SO.inP_inO_disjoint (hb2 _) hin)
    | ost hst ho hj ha hc hin _ =>
      rcases pv_ost_order H l hv ho hst with h | h
      · exact .inr (.inl (WriteBefore.of_done h))
      · exact .inr (.inr (.inr (.inl h)))
  | pst hst hp hj ha hc hin _ =>
    cases hy with
    | qk hq' h1' _ =>
      rcases qk_pst_order H l hq' hp hst (inS_parity h1' (SO.inP_inS hin)) with h | h
      · exact .inr (.inr (WriteBefore.of_done h))
      · exact .inr (.inl (.inr (.inl h)))
    | pv _ h1' _ => exact absurd h1' (SO.inP_inO_disjoint (hb2 _) hin)
    | pst hst' hp' hj' ha' hc' hin' _ =>
      exact pst_pst_order H l hst hp hj ha hc hin hst' hp' hj' ha' hc' hin'
    | ost _ _ _ _ _ hin' _ => exact absurd hin' (SO.inP_inO_disjoint (hb2 _) hin)
  | ost hst ho hj ha hc hin _ =>
    cases hy with
    | qk _ h1' _ => exact absurd hin (SO.inS_inO_disjoint (hb2 _) h1')
    | pv hv' h1' _ =>
      rcases pv_ost_order H l hv' ho hst with h | h
      · exact .inr (.inr (WriteBefore.of_done h))
      · exact .inr (.inl (.inr (.inl h)))
    | pst _ _ _ _ _ hin' _ => exact absurd hin (SO.inP_inO_disjoint (hb2 _) hin')
    | ost hst' ho' hj' ha' hc' _ _ =>
      exact ost_ost_order H l hst ho hj ha hc hst' ho' hj' ha' hc'

omit H l in
/-- The cell of a classified write is in its CTA. -/
theorem WInfo.cta {x : EvId} {cell : Cell} (h : WInfo L X c cm p0 tm Soft x cell) :
    cell.cta = c := by
  cases h <;> assumption

omit H l in
/-- A write of Tensor Memory is an event. -/
theorem write_event (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    {w : EvId} {cell : Cell} (hw : TmemWrite L X w cell) : ∃ ev, X.get w = some ev := by
  rcases tmemWrite_of_no_copy hnc hns hw with ⟨d, s, acc, mask, row, col, ⟨pc, h⟩, -⟩ |
    ⟨a, vals, sh, j, ⟨pc, h⟩, -⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

omit H l in
/-- **`Safety.Protocol.tcWrites`**: no two Tensor Memory writes of one cell are unordered, given the
reuse paths (`Mbar.Ctx`) and the coordinates (`Lane`) of every CTA of the launch. -/
theorem no_writes_unsafe (hX : Consistent L K A mem0 X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (cm p0 tm : Nat → Nat) (Soft Mma : Nat → Nat → Prop)
    (H : ∀ c, c < L.grid → Mbar.Ctx L K A mem0 X c (cm c) (p0 c) (Soft c) (Mma c))
    (l : ∀ c, c < L.grid → Lane L X c (cm c) (p0 c) (tm c) (Soft c)) :
    ¬ WritesUnsafe L X := by
  refine fun hn => hn fun x y cell hx hy => ?_
  have hcl : ∀ {w : EvId}, (∃ ev, X.get w = some ev) → w.1 / L.block < L.grid := by
    rintro w ⟨ev, he⟩
    have := event_thread_lt hX he
    unfold Launch.threads at this
    rw [Nat.mul_comm] at this
    exact Nat.div_lt_of_lt_mul this
  have hxl := hcl (write_event hnc hns hx)
  have hyl := hcl (write_event hnc hns hy)
  have ix := winfo hnc hns (l _ hxl) hx rfl
  have iy := winfo hnc hns (l _ hyl) hy rfl
  have hxy : y.1 / L.block = x.1 / L.block := iy.cta.symm.trans ix.cta
  rw [hxy] at iy
  exact winfo_order (H _ hxl) (l _ hxl) ix iy

end
end PTX.Kernels.InklingRelDecode.Proof.Sr
