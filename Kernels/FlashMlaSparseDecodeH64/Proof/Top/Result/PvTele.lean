-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PWordVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvChain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvRec
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PvCellGeom
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvBSlot

@[expose] public section

/-! # The chain of a block is the sum of the blocks' weighted values

By induction on the block `d`: the chain of PV MMA `6 + p` of block `d` at the cell of lane `g`,
times `2 ^ (M (d + 1))`, is the sum over the blocks `t ≤ d` and their 64 slots of weight times
value at the cell's feature (`pv_total`): the base step of `pv_rec` and the sum of the terms
(`pv_sum`). -/

/-! # One product of a PV MMA's chain is a weight times a value

The element `t` of the A row of a PV MMA of block `d` is the probability the lane of the cell's
pair stored for the slot `16 (k / 2) + t` (`pv_a_val`, `pword_val`: the weight times `2 ^ (-M)`),
the B element is the slot's value at the feature of the cell (`pv_b_slot`): their product is
`weight * slotValue * 2 ^ (-M)` (`pv_elem`; for an invalid slot the weight is zero). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The epilogue reads of the lanes of a pair**: each has a read at pc 1157 with all of the
CTA's blocks finished. -/
def PairEpi (P : Params) (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ y, (y = g ∨ y = w0Partner L g) → ∃ K e1, X.get (y, K) = some e1 ∧ e1.pc = 1157 ∧
    (w0Fin ((X.tr y).take K)).1.length = blocksOf P L (g / L.block)

/-- A lane of the CTA of `g` whose thread is `64 hh + row` with the row of `g` is `g` or its
partner. -/
theorem lane_pair (hp : Pre P L mem0) {g h hh row : Nat} (hw : warp L g < 4)
    (hg : g < L.threads) (hdiv : h / L.block = g / L.block) (hth : tidOf L h = 64 * hh + row)
    (hhh : hh < 2) (hrow : row = g % 384 % 64) : h = g ∨ h = w0Partner L g := by
  obtain ⟨-, -, hdiv', hmod⟩ := w0Partner_facts hp hw hg
  have hb : L.block = 384 := by have := hp.block; omega
  have hx := tidOf_x_eq hp h
  have hxg := tidOf_x_eq hp g
  have hlt : g % 384 < 128 := by simp only [warp, tidOf_x_eq hp] at hw; omega
  simp only [tidOf] at hth
  rw [hx] at hth
  have hxor := xor64_of_lt (g % 384) hlt
  by_cases hc : (g % 384) / 64 = hh
  · left
    refine thread_eq ?_ hdiv
    rw [hb]
    omega
  · right
    refine thread_eq ?_ (hdiv.trans hdiv'.symm)
    rw [hb] at hmod ⊢
    rw [hmod, hxor]
    split_ifs <;> omega

private theorem pvPc_inj_t {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

/-- **One product of a PV MMA's chain** (valid rows, complete): element `t` of the A row times
element `t` of the B column of PV MMA `k` of block `d` at the cell of lane `g` is the weight of the
slot `16 (k / 2) + t` times its value at the cell's feature times `2 ^ (-M)`. -/
theorem pv_elem (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hC : Complete L X) (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV)
    {g gm j k d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {ops : AsyncCopy.MmaOperands}
    {row col : Nat} {cell : TcMma.Cell} {xs ys : Nat → ℝ}
    (hw : warp L g < 4) (hg : g < L.threads) (hEp : PairEpi P L X g)
    (hcta : gm / L.block = g / L.block) (hlane : cell.lane = g % 384)
    (hd : d < blocksOf P L (g / L.block))
    (hget : X.get (gm, j) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * (k % 2)) s acc [0, 0, 0, 0])⟩)
    (hops : X.async.mmaOperands (gm, j) = some ops)
    (hpos : TcMma.writeCell s (128 * (k % 2)) [0, 0, 0, 0] row col = some cell)
    (hx : ∀ t < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
      (TcMma.operandRow s.descriptor row col) t = .ok (xs t))
    (hy : ∀ t < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col t = .ok (ys t))
    (hiss : mmaIssues ((X.tr gm).take j) = 24 * d + 16 + k) :
    ∀ t < 16, xs t * ys t =
      weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) d)
          (w0BlockSlot P (w0Batch L g) d (16 * (k / 2) + t)) *
        slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) d)
          (w0BlockSlot P (w0Batch L g) d (16 * (k / 2) + t))
          (128 * (cell.lane / 64) + 128 * (k % 2) + cell.column) *
        (2 : ℝ) ^ (-(w0Carry P.scale ((w0Fin (X.tr g)).1.take (d + 1))).1) := by
  intro t ht
  have env := Safe.tmEnv hp hIn hR hX hFw hnu
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.dequant hp X hX hFw
  have hBr := hIn.bar hp X hX hFw
  have hRaw := hIn.raw hp X hX hFw
  have hNc := hIn.coord hp X hX hFw
  have hW : ∀ y, warp L y < 4 → W0Trace P X y := fun y hy => w0Trace_of_rows hV hX hy
  have hSh : ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.IssueShape L i d s mask :=
    fun _ _ _ _ _ hi => Safe.issueShape hp hX hFw hi
  have hbb : 128 * (k % 2) < 256 := by omega
  obtain ⟨k0, hk0, hpc0, -, -, hon, -⟩ := TmRace.pv_pc hT hX hget hbb
  obtain ⟨d', k1, hk1, hpc1, -, hiss1, -, hD, -⟩ := mma_pvAt hp hX hFw hget hon.1 hbb
  obtain rfl := pvPc_inj_t hpc1
  have hdd : d = d' := by omega
  subst hdd
  obtain ⟨hrow, hcol, hlan, hcolm⟩ := MmaFoot.pv_cell_geom hD (b := k % 2) (by omega) hpos
  have ht' : t < 16 := ht
  obtain ⟨d1, k2, hk2, hpc2, hiss2, h, kst, e, hwh, hdivh, htid, hge, hp1, hp2, hlen, hxv⟩ :=
    TmRace.pv_a_val hp hX hFw hnu hMb hI hB hBr hSh hT hW hget hbb hops hrow hcol ht'
      (hx t ht)
  obtain rfl := pvPc_inj_t hpc2
  have hd1 : d = d1 := by omega
  subst hd1
  obtain ⟨d2, k3, hk3, hpc3, hiss3, yy, hyy, hyv⟩ :=
    pv_b_slot hp hX hFw hMb hI hB hN hRaw hNc env.hv hget hon.1 hbb hops hcol ht'
  obtain rfl := pvPc_inj_t hpc3
  have hd2 : d = d2 := by omega
  subst hd2
  have hlg : cell.lane = g % 384 := hlane
  have hgl : g % 384 < 128 := by
    simp only [warp, tidOf_x_eq hp] at hw
    omega
  have hhlf : (2 * (k / 2) + t / 8) / 4 < 2 := by omega
  have hrowg : row = g % 384 % 64 := by omega
  have hpair := lane_pair hp hw hg (hdivh.trans hcta) htid hhlf hrowg
  have hxh := tidOf_x_eq hp h
  have hbat : w0Batch L h = w0Batch L g := by
    unfold w0Batch; rw [hdivh.trans hcta]
  have hqu : w0Query L h = w0Query L g := by
    unfold w0Query; rw [hdivh.trans hcta]
  have hhd : w0Head L h = w0Head L g := by
    unfold w0Head
    simp only [tidOf] at htid
    rw [htid, tidOf_x_eq hp g]
    omega
  have hhf : w0Half L h = (2 * (k / 2) + t / 8) / 4 := by
    unfold w0Half
    simp only [tidOf] at htid
    rw [htid]
    omega
  obtain ⟨K, e1, hK, hpc1157, hKn⟩ := hEp h hpair
  have hpw := pword_val hp hX hFw hnu hBr hC hV hS hM hw hg hpair hge ⟨hp1, hp2⟩ hK hpc1157 hKn
    hlen hd (n := 8 * ((2 * (k / 2) + t / 8) % 4) + t % 8) (by omega)
  rw [hbat, hqu, hhd, hhf] at hpw
  have hslot : 32 * ((2 * (k / 2) + t / 8) / 4) + (8 * ((2 * (k / 2) + t / 8) % 4) + t % 8) =
      16 * (k / 2) + t := by omega
  rw [hslot] at hpw
  have hy2 : yy = ys t := by
    have := hyy.symm.trans (hy t ht)
    exact Except.ok.inj this
  rw [hxv, hpw, ← hy2]
  have hy3 := hyv
  by_cases hv : slotValid P (ctaidY L gm) (ctaidX L gm) (w0BlockExtra P (ctaidY L gm) d)
      (w0BlockSlot P (ctaidY L gm) d (16 * (k / 2) + t))
  · have hc : ctaidY L gm = w0Batch L g ∧ ctaidX L gm = w0Query L g := by
      exact ⟨by simp only [ctaidY, ctaOf, w0Batch, hcta],
        by simp only [ctaidX, ctaOf, w0Query, hcta]⟩
    rw [hc.1, hc.2] at hv hy3
    have := hy3 hv
    rw [this]
    have hF : 256 * (k % 2) + col = 128 * (cell.lane / 64) + 128 * (k % 2) + cell.column := by
      omega
    rw [hF]
    ring
  · have hc : ctaidY L gm = w0Batch L g ∧ ctaidX L gm = w0Query L g := by
      exact ⟨by simp only [ctaidY, ctaOf, w0Batch, hcta],
        by simp only [ctaidX, ctaOf, w0Query, hcta]⟩
    rw [hc.1, hc.2] at hv
    have hw0 : weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) d)
        (w0BlockSlot P (w0Batch L g) d (16 * (k / 2) + t)) = 0 := by
      unfold weight
      simp only [hv, ↓reduceIte]
    rw [hw0]
    ring

/-- **The terms of a PV chain** (valid rows, complete): the sum of the four slices' products of
the chain of PV MMA `p + 6` of block `d` at the cell of lane `g`, times `2 ^ M`, is the sum over
the 64 slots of block `d` of weight times value at the cell's feature. -/
theorem pv_sum (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hC : Complete L X) (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV)
    {g gm d p : Nat} {cell : TcMma.Cell} {j : Nat → Nat} {a : Nat → ℝ}
    (hw : warp L g < 4) (hg : g < L.threads) (hEp : PairEpi P L X g)
    (hcta : gm / L.block = g / L.block) (hlane : cell.lane = g % 384)
    (hd : d < blocksOf P L (g / L.block)) (hp2 : p < 2)
    (hterm : ∀ m ≤ 3, TmRace.PvTerm X gm (j m) (p + 2 * m) cell (a m))
    (hiss : ∀ m ≤ 3, mmaIssues ((X.tr gm).take (j m)) = 24 * d + 16 + (p + 2 * m)) :
    (∑ m ∈ Finset.range 4, a m) *
        (2 : ℝ) ^ (w0Carry P.scale ((w0Fin (X.tr g)).1.take (d + 1))).1 =
      ∑ j' ∈ Finset.range 64,
        weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) d)
            (w0BlockSlot P (w0Batch L g) d j') *
          slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) d)
            (w0BlockSlot P (w0Batch L g) d j')
            (128 * (cell.lane / 64) + 128 * p + cell.column) := by
  set M := (w0Carry P.scale ((w0Fin (X.tr g)).1.take (d + 1))).1 with hMdef
  have h2M : (2 : ℝ) ^ (-M) * (2 : ℝ) ^ M = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have hm : ∀ m ∈ Finset.range 4, a m * (2 : ℝ) ^ M = ∑ t ∈ Finset.range 16,
      (weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) d)
          (w0BlockSlot P (w0Batch L g) d (16 * m + t)) *
        slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) d)
          (w0BlockSlot P (w0Batch L g) d (16 * m + t))
          (128 * (cell.lane / 64) + 128 * p + cell.column)) := by
    intro m hm4
    have hm3 : m ≤ 3 := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hm4
    obtain ⟨s, acc, ops, row, col, xs, ys, hget, hops, hpos, hx, hy, hsum⟩ := hterm m hm3
    have hk2 : (p + 2 * m) % 2 = p := by omega
    have hk3 : (p + 2 * m) / 2 = m := by omega
    have hel := pv_elem hp hIn hR hX hFw hnu hC hV hS hM hw hg hEp hcta hlane hd hget hops hpos
      hx hy (hiss m hm3)
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    have := hel t (Finset.mem_range.mp ht)
    rw [hk2, hk3] at this
    rw [this, mul_assoc, h2M, mul_one]
  rw [Finset.sum_mul, Finset.sum_congr rfl hm]
  rw [show (64 : Nat) = 16 * 4 from rfl, PTX.Numeric.sum_range_blocks]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem rpow_cancel (a b : ℝ) : (2 : ℝ) ^ (a - b) * (2 : ℝ) ^ b = (2 : ℝ) ^ a := by
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- **The chain of block `d` times `2 ^ M`** (valid rows, complete). -/
theorem pv_total (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hC : Complete L X) (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV)
    {g c jj p : Nat} (hw : warp L g < 4) (hg : g < L.threads) (hEp : PairEpi P L X g)
    (hc : c < 4) (hjj : jj < 64) (hp2 : p = (64 * c + jj) / 128) :
    ∀ d, d < blocksOf P L (g / L.block) → ∀ (i : Nat) (x : ℝ),
      TmRace.PvChain L X (mmaLane L X (g / L.block)) i (6 + p)
        (tcDataCell L g .s32x32b (64 * c) jj) (.float .f32 x) →
      mmaIssues ((X.tr (mmaLane L X (g / L.block))).take i) = 24 * d + 16 + (6 + p) →
      X.async.mmaDone (mmaLane L X (g / L.block), i) = true →
      x * (2 : ℝ) ^ carryM P X g (d + 1) = ∑ t ∈ Finset.range (d + 1), ∑ j' ∈ Finset.range 64,
        weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) t)
            (w0BlockSlot P (w0Batch L g) t j') *
          slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) t)
            (w0BlockSlot P (w0Batch L g) t j')
            (128 * (g % 384 / 64) + 128 * p + (64 * c + jj)) := by
  have hv0 : W0Trace P X g := w0Trace_of_rows hV hX hw
  obtain ⟨K, e1, hK, hpc, hKn⟩ := hEp g (Or.inl rfl)
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  obtain ⟨hcta, hlane, hcol⟩ := stCell hp hw hc (j := jj)
  have hp2' : p < 2 := by omega
  have hsum : ∀ d, d < blocksOf P L (g / L.block) → ∀ (j : Nat → Nat) (a : Nat → ℝ),
      (∀ m ≤ 3, TmRace.PvTerm X (mmaLane L X (g / L.block)) (j m) (p + 2 * m)
        (tcDataCell L g .s32x32b (64 * c) jj) (a m)) →
      (∀ m ≤ 3, mmaIssues ((X.tr (mmaLane L X (g / L.block))).take (j m)) =
        24 * d + 16 + (p + 2 * m)) →
      (∑ m ∈ Finset.range 4, a m) * (2 : ℝ) ^ carryM P X g (d + 1) =
        ∑ j' ∈ Finset.range 64,
          weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) d)
              (w0BlockSlot P (w0Batch L g) d j') *
            slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) d)
              (w0BlockSlot P (w0Batch L g) d j')
                (128 * (g % 384 / 64) + 128 * p + (64 * c + jj)) := by
    intro d hd j a hterm hiss
    obtain ⟨s, acc, ops, row, col, xs, ys, hget, hops, hpos, -⟩ := hterm 0 (by omega)
    have hmc : X.MmaCell (mmaLane L X (g / L.block), j 0) (tcDataCell L g .s32x32b (64 * c) jj) :=
      ⟨_, _, _, _, row, col, ⟨_, hget⟩, hpos⟩
    have hgc := (TmRace.writer_cases hp hX hT (.inl hmc)).1
    have hres := pv_sum hp hIn hR hX hFw hnu hC hV hS hM hw hg hEp (gm := mmaLane L X (g / L.block))
      (cell := tcDataCell L g .s32x32b (64 * c) jj) (d := d) (p := p) (j := j) (a := a)
      (hgc.symm.trans hcta) (by rw [hlane]) hd hp2' hterm hiss
    rw [hlane, hcol] at hres
    exact hres
  intro d
  induction d with
  | zero =>
    intro hd i x hch hiss hdone
    obtain ⟨j, a, base, hterms, hr, hx, hb⟩ :=
      pv_rec hp hIn hR hX hFw hnu hw hv0 hKn hd hc hjj hp2 hch hiss hdone
    rcases hb with ⟨-, hb0⟩ | ⟨h1, -⟩
    · have := hsum 0 hd j a hterms hr
      rw [hx, hb0, zero_add, Finset.sum_range_one]
      exact this
    · omega
  | succ d ih =>
    intro hd i x hch hiss hdone
    obtain ⟨j, a, base, hterms, hr, hx, hb⟩ :=
      pv_rec hp hIn hR hX hFw hnu hw hv0 hKn hd hc hjj hp2 hch hiss hdone
    rcases hb with ⟨h0, -⟩ | ⟨-, i', x', hiss', hdone', hch', hbase⟩
    · omega
    · have ih' := ih (by omega) i' x' hch' (by simpa using hiss') hdone'
      have hs := hsum (d + 1) hd j a hterms hr
      have hcan := rpow_cancel (carryM P X g (d + 1)) (carryM P X g (d + 1 + 1))
      rw [hx, hbase, Finset.sum_range_succ _ (d + 1), ← ih', ← hs, ← hcan]
      ring

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
