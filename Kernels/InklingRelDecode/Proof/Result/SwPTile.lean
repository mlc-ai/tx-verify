-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Result.RsOAcc
public import Kernels.InklingRelDecode.Proof.Result.SvVals
public import Kernels.InklingRelDecode.Proof.Result.SwStore

@[expose] public section

/-!
# The A operand of a PV MMA is the probabilities in Tensor Memory (`Out.Inputs.pTile`)

`Mma.PTile`: element `(r, kk)` of PV MMA `j` of iteration `i ≥ 1` is the `bf16` probability
`pElemE g r (i - 1) (16 j + kk)`. The A operand is read from Tensor Memory
(`sp.aTmem = tm + 128 ((i - 1) % 2) + 8 j`, `TcMma.aCell`), so its bytes are the bytes of the
word the read source wrote (`TcMma.AReadOk`).

* `pv_aTmem`: the A address of the event at the state of step `j` (from `EvW.PvIssue`);
* `pv_a_cell`: the cell and byte of A byte `32 r + 2 kk + z` is `sCell` of the buffer
  `(i - 1) % 2`, row `r`, word column `8 j + kk / 2`, byte `2 (kk % 2) + z` (the TMEM A-operand
  decode, the analogue of `Mma.pv_b_loc` for the B operand);
* `PReadSrc`: the premise this file leaves: the read source of that cell is the thread's `P` store
  of iteration `i - 1` (the existence of the covering store and the order of every other writer:
  `Sr.aread_order`, `SO.p_store_before_read`, and for the existence the `bar.sync 0, 128` of
  `Sr.PStSync`);
* `pTile_of`: `PTile` from `PReadSrc`, the words of the `P` store (`Sv.pstore_words`) and
  `AReadOk`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rs
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (pvDesc pvDesc_valid)
open PTX.Kernels.InklingRelDecode.Proof.Sv (ValidRow SvPrem)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The A address of a PV MMA event** at the state of step `j` of iteration `i`:
`tm + 128 ((i - 1) % 2) + 8 j`. -/
theorem pv_aTmem (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8} (hs : d.site = .pv j) :
    sp.aTmem = some (d.tm + 128 * ((d.i - 1) % 2) + 8 * j.val) := by
  obtain ⟨d', P', hσ', hsh⟩ := Interface.mma_event_state hpre hX hf.sound hf.tracked hg he
    (Or.inl ⟨dst, sp, acc, mask, rfl⟩)
  have hdd : d = d' := by
    have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
    simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
    exact this.1
  subst hdd
  unfold EvW.MmShape at hsh
  rw [hs] at hsh
  obtain ⟨db, dsc, hd, hdb, he'⟩ := hsh
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
  obtain ⟨-, -, rfl, -, -⟩ := he'
  rfl

/-- **The cell and byte of an A byte of a PV MMA**: byte `32 r + 2 kk + z` of the A operand
(`r < 64`, `kk < 16`, `z < 2`) is byte `2 (kk % 2) + z` of the word at row `r`, column
`tm + 128 (b % 2) + 8 j + kk / 2`, of CTA `cta`. -/
theorem pv_a_cell {sp : OperandSpec} (hD : sp.descriptor = pvDesc) {cta tm b j : Nat}
    (hlow : sp.lowCta = cta) (hat : sp.aTmem = some (tm + 128 * (b % 2) + 8 * j))
    (hj : j < 8) (htm : tm + 384 ≤ 512) {r kk z : Nat} (hr : r < 64) (hk : kk < 16) (hz : z < 2) :
    aCell sp (32 * r + 2 * kk + z) =
      some (sCell cta tm b r (8 * j + kk / 2), 2 * (kk % 2) + z) := by
  have hrows : Operand.rows .a pvDesc = 64 := by decide
  have hbytes : pvDesc.kind.k * pvDesc.kind.width = 32 := by decide
  have hhalf : halfDatapath pvDesc = true := by decide
  have hm : pvDesc.m = 64 := rfl
  have hg : pvDesc.group.size = 1 := rfl
  have hb2 : b % 2 < 2 := Nat.mod_lt _ (by omega)
  have hf : (tm + 128 * (b % 2) + 8 * j) / 2 ^ 16 = 0 := by omega
  have hmod : (tm + 128 * (b % 2) + 8 * j) % 2 ^ 16 = tm + 128 * (b % 2) + 8 * j := by omega
  unfold aCell
  rw [hat, hD]
  simp only [Option.bind_some, hrows, hbytes, hhalf, hm, hg, hf, hmod]
  have h1 : (32 * r + 2 * kk + z) / 32 = r := by omega
  have h2 : (32 * r + 2 * kk + z) % 32 = 2 * kk + z := by omega
  have h3 : (2 * kk + z) / 4 = kk / 2 := by omega
  have h4 : (2 * kk + z) % 4 = 2 * (kk % 2) + z := by omega
  rw [h1, h2, h3, h4]
  have hr1 : r < 64 / 1 := by omega
  have h5 : tm + 128 * (b % 2) + 8 * j + 8 ≤ 512 := by omega
  simp [sCell, hlow, hr1, pvDesc_valid, h5]
  omega

/-- **The premise on the `A` read**: for the A element column `w = 8 j + kk / 2` of PV MMA `j` of
iteration `i ≥ 1` (a valid row `r`), the read source (`ReadSource .a`) of the cell of buffer
`(i - 1) % 2`, row `r`, column `w` is the `P` store (a `tcgen05.st` at the state `tmemSt`) of
iteration `i - 1` of a softmax thread of the CTA. The existence of the covering store is the
`bar.sync 0, 128` of `Sr.PStSync` (every thread reaches its store before thread 0's arrival on
`p_ready`); the order of every other writer is `Sr.aread_order`. -/
structure PReadSrc (Q : Params) (L : Launch) (X : Execution) : Prop where
  src : ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro} {j : Fin 8} {r w : Nat},
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j → 1 ≤ d.i →
    QRowValid Q L g r → 8 * j.val ≤ w → w < 8 * j.val + 8 →
    ∃ (t ks pcs a : Nat) (ds : Sm.D) (vals : List Value) (sh : TcShape),
      t < L.threads ∧ t / L.block = g / L.block ∧
      St Q L X t ks = some (some (.d (.sm ds))) ∧ ds.site = .tmemSt ∧ ds.i = d.i - 1 ∧
      X.get (t, ks) = some ⟨pcs, .tc (.st a vals sh)⟩ ∧
      ReadSource L X .a (t, ks) (g, k) (sCell (g / L.block) d.tm (d.i - 1) r w)

/-- **The shape of the `P` store's event** (no row condition): the address and the shape. -/
theorem pstore_shape (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {t : Nat} (ht : t < L.threads) {k pc a : Nat} {d : Sm.D}
    {vals : List Value} {sh : TcShape} (hσ : St Q L X t k = some (some (.d (.sm d))))
    (hs : d.site = .tmemSt) (he : X.get (t, k) = some ⟨pc, .tc (.st a vals sh)⟩) :
    a = Sm.tileAddr L t d ∧ sh = .s16x32bx2 32 := by
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf ht he hσ (by simp [Interface.ExitState])
  obtain ⟨vals', hl, hw, -, hev⟩ := Sm.shape_tmemSt (Interface.fired_sm hF) hs
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
  exact ⟨hev.2.1, hev.2.2.2⟩

theorem pElemE_cta {g g' : Nat} (h : g' / L.block = g / L.block) (r b k : Nat) :
    pElemE Q L g' r b k = pElemE Q L g r b k := by
  obtain ⟨h1, h2, h3⟩ := cta_eq (L := L) h
  unfold pElemE
  rw [h1, h2, h3]

theorem pair_byteAt (x y : ℝ) (z : Nat) (hz : z < 2) :
    (Value.pair (.float .bf16 x) (.float .bf16 y)).byteAt z = (Value.float .bf16 x).byteAt z ∧
    (Value.pair (.float .bf16 x) (.float .bf16 y)).byteAt (2 + z) =
      (Value.float .bf16 y).byteAt z := by
  simp [Value.byteAt, Value.bytes, FloatFmt.bytes]
  omega

/-- **`Out.Inputs.pTile`**, from the read source of the A cells (`PReadSrc`), the base word of the
softmax region (`SmBaseZero`), the words of the `P` store (`Sv.pstore_words`) and `AReadOk`. -/
theorem pTile_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hcomp : Complete L X) (P : SvPrem Q L X)
    (hre : Interface.Lk.SmReal Q L X)
    (S : PReadSrc Q L X) (hw : MmaWords Q L X) (hT : SmBaseZero Q L X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s) :
    PTile Q L X (pElemE Q L) where
  elem := by
    intro g k d P' j ops r kk hσ hs hops hr hk
    obtain ⟨hg, hklen⟩ := Interface.mma_state_lt hX hf hcomp hσ
    obtain ⟨e, he0⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hklen⟩
    obtain ⟨pc, dst, sp, acc, mask, hev⟩ :=
      Interface.mma_issue_event hpre hX hf hg he0 hσ (.inr ⟨j, hs⟩)
    rw [hev] at he0
    have hd0 : d.tm = 0 := hw.tm (m := (g, k)) ⟨P', hσ⟩
    obtain ⟨hqo, -, -, -, hIn⟩ := pv_event hpre hX hf hg he0 hσ hs
    have hi1 : 1 ≤ d.i := (hIn.pv (by rw [hs]; trivial)).1
    have hr64 : r < 64 := by have := hr.1; omega
    have hat := pv_aTmem hpre hX hf hg he0 hσ hs
    rw [hd0] at hat
    have hbyte : ∀ z, z < 2 → ops.a[2 * (r * 16 + kk) + z]? = some (some
        ((Value.float .bf16 (pElemE Q L g r (d.i - 1) (16 * j.val + kk))).byteAt z)) := by
      intro z hz
      rw [← idx_eq]
      have hcellA := pv_a_cell hqo.desc (cta := g / L.block) (tm := 0) (b := d.i - 1)
        (j := j.val) hqo.low hat j.isLt (by omega) hr64 hk hz
      obtain ⟨t, ks, pcs, a, ds, vals, sh, ht, htc, hσs, hsite, hdi, hget, hrs⟩ :=
        S.src hσ hs hi1 hr (w := 8 * j.val + kk / 2) (by omega) (by omega)
      rw [hd0] at hrs
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
      have hlen : ks < (X.tr t).length := len_of_get hget
      obtain ⟨hae, hsh⟩ := pstore_shape hX hf ht hσs hsite hget
      subst hsh
      have hT128 : t % L.block < 128 := (hf.reach ht hσs).1
      have hTm := hT ht hσs
      have hte : Sm.tileAddr L t ds = ds.e.tm + 128 * (ds.i % 2) + t % L.block / 32 * 2 ^ 21 :=
        Sm.tileAddr_eq hT128 (by omega)
          (Interface.sm_bw' hpre hX hf ht hσs (by rw [hsite]; trivial))
      rw [hTm] at hte
      -- the cell fixes the thread's row and half
      have hcell := hcell1
      rw [hae, hte] at hcell
      unfold sCell at hcell
      rw [Sr.cell_split L t (0 + 128 * (ds.i % 2)) 32 (t % L.block / 32) w1 (by omega)] at hcell
      simp only [Cell.mk.injEq] at hcell
      obtain ⟨hc1, hc2, hc3⟩ := hcell
      unfold laneOf at hc2 hc3
      have hrt : r = Sm.row (t % L.block) := by unfold Sm.row; omega
      have hvt : ValidRow Q L t := by
        obtain ⟨h1, h2⟩ := hr
        unfold Sv.ValidRow
        refine ⟨by rw [← hrt]; exact h1, ?_⟩
        have e1 : Sm.tokOf (t % L.block) = r / 6 := by rw [← Sv.row_div6, hrt]
        have e2 : ProA.cta L t .z = reqOf L g := (cta_eq (L := L) htc).1
        rw [e1, e2]
        exact h2
      obtain ⟨-, -, hlen32, hwv⟩ := Sv.pstore_words hpre hX hf P hre ht hvt hlen.le hσs hsite hget
      have hw1' : w1 < 32 := by omega
      have hvw := hwv w1 hw1'
      have hwrote : Wrote L Assumptions.all X (t, ks)
          (sCell (g / L.block) 0 (d.i - 1) r (8 * j.val + kk / 2)) _ :=
        .inr (.inl ⟨_, vals, .s16x32bx2 32, w1, ⟨pcs, hget⟩, hvw, hcell1⟩)
      have hpos : 2 * (kk % 2) + z < (Value.pair
          (.float .bf16 (pElemE Q L t (Sm.row (t % L.block)) ds.i
            (64 * Sm.half (t % L.block) + 2 * w1)))
          (.float .bf16 (pElemE Q L t (Sm.row (t % L.block)) ds.i
            (64 * Sm.half (t % L.block) + (2 * w1 + 1))))).bytes := by
        simp [Value.bytes, FloatFmt.bytes]
        omega
      have hread := hX.tcRead.2 (g, k) (32 * r + 2 * kk + z)
        (sCell (g / L.block) 0 (d.i - 1) r (8 * j.val + kk / 2)) (2 * (kk % 2) + z) (t, ks) _ ops
        ⟨dst, sp, acc, mask, ⟨pc, he0⟩, hcellA⟩ hrs hwrote hops hpos
      rw [hread]
      congr 2
      have hk0 : 64 * Sm.half (t % L.block) + 2 * w1 = 16 * j.val + 2 * (kk / 2) := by
        unfold Sm.half
        split_ifs at hc3 <;> omega
      rw [← hrt, hdi, pElemE_cta htc]
      rcases Nat.mod_two_eq_zero_or_one kk with h0 | h1
      · rw [h0, mul_zero, zero_add, (pair_byteAt _ _ z hz).1]
        have : 16 * j.val + kk = 64 * Sm.half (t % L.block) + 2 * w1 := by omega
        rw [this]
      · have e : 2 * (kk % 2) + z = 2 + z := by omega
        rw [e, (pair_byteAt _ _ z hz).2]
        have : 16 * j.val + kk = 64 * Sm.half (t % L.block) + (2 * w1 + 1) := by omega
        rw [this, pElemE_cta htc]
    exact element_bf16 (hbyte 0 (by omega)) (hbyte 1 (by omega))

end
end PTX.Kernels.InklingRelDecode.Proof.Rs
