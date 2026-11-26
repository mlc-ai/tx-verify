-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.DqTile
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QkCellGeom
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Gemm
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkB
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqBElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqSlotValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaSum
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkAElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkSource

@[expose] public section

/-! # The result of QK MMA 15 at a cell is the sum of the products of the lane's features

The chain of QK MMA 15 of block `r` at a cell (`qk_chain`) is the sum over the MMAs `k < 16` and
the elements `t < 16` of the product of the A element (the query value of head `lane % 64`,
feature `QueryTile.feature k lane t`, `qk_a_elem`) and the B element (the dequantized value of the
block's slot `column - 400` at the same feature, `qk_b_slot`, for a valid slot): `qk_cell_sum`.
Each MMA of the chain is the one of the same block (`24 r + k`). -/

/-! # The B elements of a QK MMA are the slot's dequantized values

B element `(col, t)` of QK MMA `k` of block `d` (`col < 128`, `t < 16`) is the bf16 number
`e4m3Val x * ue8m0Val b` of the chunk store of the use (`dq_b_elem`); the byte is the chunk
`(8 (y % 16) + F % 64 / 8, y / 16, F / 64)` of the dequantizer lane, byte `2 (F % 8)`, where
`y = col % 64` is the token and `F` the feature (`qk_b_addr`, `dqChunk_inj`). The store is of use
`d / 2` of tile `d % 2`, so its block is `d`, and `dq_store_slot` gives the value of the slot at
position `y` of block `d` when that slot is valid (`qk_b_slot`). -/

/-! # The QK chain: the result of QK MMA `k` is the sum of the products of slots `0 .. k`

QK MMA `k` of a block accumulates the result of QK MMA `k - 1` of the same block at the same cell
(`acc_source_qk`), and QK MMA 0 overwrites. With the value of one result (`mma_result_sum`) this
gives, by induction on `k`, `QkChain`: the result at a cell is the single-precision number
`Σ_{k' ≤ k} Σ_{t < 16} x_{k'} t y_{k'} t`, the terms `x`, `y` the decoded operand elements of the
MMAs `0 .. k` of one block (`QkTerm`: the MMA's own A row and B column of the cell). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

/-- **One term of the chain**: QK MMA `k` at event `(g, j)` has the operand snapshot `ops`, the
cell is its output `(row, col)`, and `a` is the sum of the sixteen products of the decoded
elements of its A row and its B column. -/
def QkTerm (X : Execution) (g j k : Nat) (cell : TcMma.Cell) (a : ℝ) : Prop :=
  ∃ (s : TcMma.OperandSpec) (ops : AsyncCopy.MmaOperands) (row col : Nat) (x y : Nat → ℝ),
    X.get (g, j) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s (k != 0) [0, 0, 0, 0])⟩ ∧
    X.async.mmaOperands (g, j) = some ops ∧
    TcMma.writeCell s 400 [0, 0, 0, 0] row col = some cell ∧
    (∀ t < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
      (TcMma.operandRow s.descriptor row col) t = .ok (x t)) ∧
    (∀ t < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col t = .ok (y t)) ∧
    a = ∑ t ∈ Finset.range 16, x t * y t

/-- **The chain of a result**: the events `j 0 < … < j k = i` of the lane (the MMA issues
`24 r + 0 … 24 r + k` of one block `r`), their terms `a k'`, and the value
`Σ_{k' ≤ k} a k'`. -/
def QkChain (X : Execution) (g i k : Nat) (cell : TcMma.Cell) (v : Value) : Prop :=
  ∃ (j : Nat → Nat) (a : Nat → ℝ), j k = i ∧ (∀ k' ≤ k, QkTerm X g (j k') k' cell (a k')) ∧
    (∀ k' < k, j k' < j (k' + 1)) ∧
    (∃ r, ∀ k' ≤ k, mmaIssues ((X.tr g).take (j k')) = 24 * r + k') ∧
    v = .float .f32 (∑ k' ∈ Finset.range (k + 1), a k')

private theorem qkPc_inj {k k' : Nat} (h : TmemRow.qkPc k = TmemRow.qkPc k') : k = k' := by
  simp only [TmemRow.qkPc] at h
  split_ifs at h <;> omega

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (hE : QkElements X) (b : EvId)
  (hold : ∀ i src old cell, (i = b ∨ Relation.TransGen (TcMma.TcStep L X) i b) →
      Relation.TransGen (TcMma.TcStep L X) src i →
      ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
        TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r)
include hp hX hFw hT hO hPS hG ht hmd hE hold

/-- **The QK chain**: a done QK MMA `k` of the lane at event `(g, i)`, with its result at a
cell, has the chain of slots `0 .. k`. -/
theorem qk_chain {g : Nat} : ∀ k, k < 16 → ∀ {i : Nat} {s : TcMma.OperandSpec} {mask : List Nat}
    {cell : TcMma.Cell} {v : Value},
    X.get (g, i) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s (k != 0) mask)⟩ →
    X.async.mmaDone (g, i) = true → TcMma.Result L Assumptions.all X (g, i) cell v →
    ((g, i) = b ∨ Relation.TransGen (TcMma.TcStep L X) (g, i) b) →
    QkChain X g i k cell v := by
  intro k
  induction k with
  | zero =>
    intro hk i s mask cell v he hd hr hb
    obtain ⟨d, s', acc, mask', row, col, ops, x, y, prev, hi, hpos, hops, hx, hy, hv, hprev⟩ :=
      mma_result_sum hp hX hT hO hG (hE g i _ s _ mask he)
        (fun src old hdep h => hold (g, i) src old cell hb hdep h) hd hr
    obtain ⟨pc, he'⟩ := id hi
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he'
    obtain ⟨-, -, -, -, hm0, -⟩ := qk_pc hT hX he
    subst hm0
    obtain ⟨-, hp0⟩ := hprev.resolve_right (by simp)
    obtain ⟨r, hr⟩ := mma_qkCount hp hX hFw he hk
    refine ⟨fun _ => i, fun _ => ∑ t ∈ Finset.range 16, x t * y t, rfl, fun k' hk' => ?_,
      fun k' h => absurd h (by omega), ⟨r, fun k' hk' => ?_⟩, ?_⟩
    · obtain rfl : k' = 0 := by omega
      exact ⟨s, ops, row, col, x, y, he, hops, hpos, hx, hy, rfl⟩
    · obtain rfl : k' = 0 := by omega
      simpa using hr
    · rw [hv, hp0]
      simp
  | succ k ih =>
    intro hk i s mask cell v he hd hr hb
    obtain ⟨d, s', acc, mask', row, col, ops, x, y, prev, hi, hpos, hops, hx, hy, hv, hprev⟩ :=
      mma_result_sum hp hX hT hO hG (hE g i _ s _ mask he)
        (fun src old hdep h => hold (g, i) src old cell hb hdep h) hd hr
    obtain ⟨pc, he'⟩ := id hi
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he'
    obtain ⟨-, -, -, -, hm0, -⟩ := qk_pc hT hX he
    subst hm0
    have hacc : ((k + 1) != 0) = true := by simp
    rw [hacc] at he hprev
    obtain ⟨-, src, old, hsrc, hold', hpv⟩ := hprev.resolve_left (by simp)
    have hrd : X.MmaReadCell (g, i) cell :=
      ⟨_, _, _, row, col, hi, TcMma.writeCell_resultCell hpos⟩
    obtain ⟨j, hji, ⟨s2, a2, m2, hj⟩, hrr, hmc, hsrc'⟩ :=
      acc_source_qk hp hX hFw hT hO hPS hG ht hmd (k := k + 1) he (by omega) hk hrd
    have hsj : src = (g, j) := TcMma.readSource_unique hX hG hsrc hsrc'
    subst hsj
    have hdj := acc_mma_done hp hX hT hO hG hd hrd hsrc' hmc
    have hb' : (g, j) = b ∨ Relation.TransGen (TcMma.TcStep L X) (g, j) b := by
      rcases hb with h | h
      · exact .inr (h ▸ hsrc'.2.2.1.tcStep)
      · exact .inr (hsrc'.2.2.1.tcStep.trans h)
    rcases hold' with hres | ⟨a3, vals, sh, jj, ⟨pcs, hst⟩, -, -⟩
    · have hkk : k + 1 - 1 = k := by omega
      rw [hkk] at hj
      obtain ⟨k3, -, hpc3, ha3, -⟩ := qk_pc hT hX hj
      obtain rfl := qkPc_inj hpc3
      rw [ha3] at hj
      obtain ⟨jf, af, hjf, hterms, hmono, ⟨r, hr'⟩, hold2⟩ :=
        ih (by omega) (s := s2) (mask := m2) hj hdj hres hb'

      obtain ⟨r0, hr0, hr1⟩ := hrr
      have hrj := hr' k le_rfl
      rw [hjf] at hrj
      have hrr0 : r = r0 := by omega
      subst hrr0
      have hpr : prev = ∑ k' ∈ Finset.range (k + 1), af k' := by
        rw [hold2] at hpv
        simp [valFloat] at hpv
        exact (Except.ok.inj hpv).symm
      refine ⟨fun k' => if k' = k + 1 then i else jf k',
        fun k' => if k' = k + 1 then ∑ t ∈ Finset.range 16, x t * y t else af k',
        by simp, fun k' hk' => ?_, fun k' hk' => ?_, ⟨r, fun k' hk' => ?_⟩, ?_⟩
      · by_cases h : k' = k + 1
        · subst h
          simp only [ite_true]
          exact ⟨s, ops, row, col, x, y, by rw [hacc]; exact he, hops, hpos, hx, hy, rfl⟩
        · simp only [h, ite_false]
          exact hterms k' (by omega)
      · by_cases h : k' = k
        · subst h
          simp only [hjf, ite_true, show k' ≠ k' + 1 by omega, ite_false]
          exact hji
        · simp only [show k' ≠ k + 1 by omega, show k' + 1 ≠ k + 1 by omega, ite_false]
          exact hmono k' (by omega)
      · by_cases h : k' = k + 1
        · subst h
          simpa using hr0
        · simp only [h, ite_false]
          exact hr' k' (by omega)
      · have hs : ∑ k' ∈ Finset.range (k + 1), (if k' = k + 1 then
            (∑ t ∈ Finset.range 16, x t * y t) else af k') = ∑ k' ∈ Finset.range (k + 1), af k' :=
          Finset.sum_congr rfl fun k' hk' => by
            simp only [Finset.mem_range] at hk'
            simp [show k' ≠ k + 1 by omega]
        rw [hv, hpr, Finset.sum_range_succ _ (k + 1), hs, add_comm]
        simp
    · cases get_tc_inj hj hst

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow PTX.AsyncCopy MmaFoot

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
  (hRaw : RawInputs L X) (hNc : CoordInputs L X)
  (hv : ∀ h k, NoUbBefore X h k → DqValid X h k)
include hp hX hFw hR hI hB hN hRaw hNc hv

/-- **A QK MMA's B element is the slot's dequantized value** (valid data): for the block `d` of the
MMA, B element `(col, t)` of QK MMA `k` is a number, which is `slotValue` of the slot at position
`col % 64` of block `d`, feature `QueryTile.feature k col t`, when that slot is valid. -/
theorem qk_b_slot {g i pc : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : MmaOperands} (he : X.get (g, i) = some ⟨pc, .tc (.mma 400 s acc mask)⟩)
    (hat : MbarRow.MmaAt L g pc) (hops : X.async.mmaOperands (g, i) = some ops) {col t : Nat}
    (hc : col < 128) (ht : t < 16) :
    ∃ d k, k < 16 ∧ mmaIssues ((X.tr g).take i) = 24 * d + k ∧
      ∃ y : ℝ, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col t = .ok y ∧
        (slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) d)
            (w0BlockSlot P (ctaidY L g) d (col % 64)) →
          y = slotValue P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) d)
            (w0BlockSlot P (ctaidY L g) d (col % 64)) (QueryTile.feature k col t)) := by
  obtain ⟨d, k, hk16, hiss, hD, hsb, hlow, hall⟩ := mma_qkB hp hX hFw he hat
  have hS1024 : L.sharedBase % 1024 = 0 := hp.sharedBase ▸ hp.sharedAlignment
  have hb2 : d % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨hmu, -⟩ := hall ⟨d % 2, hb2⟩ rfl
  have hu' : ringUses 2 (d % 2) d = d / 2 := PTX.Flow.ringUses_here rfl hb2
  have hF : QueryTile.feature k col t < 512 := by simp only [QueryTile.feature]; omega
  have hl : s.byteLoc .b (2 * (col * 16 + t)) = some ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (QueryTile.linear (L.sharedBase + 65536 * (d % 2))
        (col % 64) (QueryTile.feature k col t) 0)⟩ := by
    have := QueryTile.qk_b_loc hD hsb hc ht (z := 0) (by omega)
    rwa [show 32 * col + 2 * t + 0 = 2 * (col * 16 + t) by omega] at this
  have hadr := QueryTile.qk_b_addr (Bt := L.sharedBase + 65536 * (d % 2)) (k := k) (col := col)
    (t := t) (z := 0) (by omega) (by omega)
  have hi0 : 8 * (col % 64 % 16) + QueryTile.feature k col t % 64 / 8 < 128 := by omega
  have hlt0 := MemRow.dqChunk_lt (i := 8 * (col % 64 % 16) + QueryTile.feature k col t % 64 / 8)
    (r := col % 64 / 16) (s := QueryTile.feature k col t / 64) hi0 (by omega) (by omega)
  have hal0 := MemRow.dqChunk_al (i := 8 * (col % 64 % 16) + QueryTile.feature k col t % 64 / 8)
    (r := col % 64 / 16) (s := QueryTile.feature k col t / 64) hi0
  have hlg : MemRow.LocIn L (g / L.block) (.dequant ⟨d % 2, hb2⟩) ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (QueryTile.linear (L.sharedBase + 65536 * (d % 2))
        (col % 64) (QueryTile.feature k col t) 0)⟩ := by
    refine ⟨rfl, hlow, ?_, ?_⟩ <;> simp only [Region.lo, Region.size] <;> rw [hadr] <;> omega
  obtain ⟨x, hx, h, k2, pcw, ac, bs, bw, r, s', j, hW, hpcw, hcta, hws, harr, hcov, hj8, hladdr,
      hxval⟩ := dq_b_elem hp hX hFw hR hI hB hN hv he hat hops (n := col * 16 + t)
    (by rw [hD]; rfl) (by rw [hsb]; simp only [keyDesc]; exact ⟨by omega, trivial, trivial⟩) hl
    hlg hmu
  have hA : ac.loc.addr =
      L.sharedBase + ((Region.dequant bw).lo + MemRow.dqChunk (h % 128) r s') := by
    rw [hws.1]; rfl
  have hL2 : TensorSwizzle.offset .b128 0 (QueryTile.linear (L.sharedBase + 65536 * (d % 2))
      (col % 64) (QueryTile.feature k col t) 0) = ac.loc.addr + 2 * j := hladdr
  rw [hadr, hA] at hL2
  have hltr := MemRow.dqChunk_lt (i := h % 128) (r := r) (s := s') (Nat.mod_lt _ (by decide))
    r.isLt s'.isLt
  have hal1 := MemRow.dqChunk_al (i := h % 128) (r := r) (s := s') (Nat.mod_lt _ (by decide))
  simp only [Region.lo] at hL2
  have hbwl := bw.isLt
  obtain ⟨hbv, hch, hjj⟩ : bw.val = d % 2 ∧
      MemRow.dqChunk (h % 128) r s' = MemRow.dqChunk
        (8 * (col % 64 % 16) + QueryTile.feature k col t % 64 / 8) (col % 64 / 16)
        (QueryTile.feature k col t / 64) ∧ j = QueryTile.feature k col t % 8 := by omega
  obtain ⟨hi', hr', hs'⟩ := MemRow.dqChunk_inj (Nat.mod_lt _ (by decide)) hi0 r.isLt
    (by omega) hch
  have hbw : bw = ⟨d % 2, hb2⟩ := Fin.ext hbv
  subst hbw
  have hW' : X.get (h, k2) = some ⟨dqStorePc r s', .wr ac bs⟩ := hpcw ▸ hW
  have harr' : arrivals (mbarLoc L (h / L.block) (.dequantReady ⟨d % 2, hb2⟩))
      ((X.tr h).take k2) = d / 2 := by
    rw [hcta, harr]; exact hu'
  have hslot := dq_store_slot hp hX hFw hR hI hB hRaw (noUbInner hX) hNc r.isLt
    s'.isLt hW' (hv h k2 (noUbBefore_of_get hX hW')) hws harr' (j := j) hj8
  refine ⟨d, k, hk16, hiss, x, Result.bf16MmaElement_of_bytes hx, fun hvalid => ?_⟩
  have e1 : 2 * (d / 2) + d % 2 = d := by omega
  have e2 : h % 128 / 8 + 16 * r.val = col % 64 := by omega
  have e3 : ctaidY L h = ctaidY L g := by simp only [ctaidY, ctaOf, hcta]
  have e4 : ctaidX L h = ctaidX L g := by simp only [ctaidX, ctaOf, hcta]
  have e5 : 64 * s'.val + 8 * (h % 8) + j = QueryTile.feature k col t := by omega
  simp only [e1, e2, e3, e4, e5] at hslot
  exact hxval.trans (hslot hvalid)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hR : MbarRows P L X)
  (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
  (hRaw : RawInputs L X) (hNc : CoordInputs L X)
  (hv : ∀ h k, NoUbBefore X h k → DqValid X h k)
  (hPS : PvStoreOrder L X) (hG : SyncGuarded L kernel X)
  (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
  (hE : QkElements X) (b : EvId)
  (hold : ∀ i src old cell, (i = b ∨ Relation.TransGen (TcMma.TcStep L X) i b) →
      Relation.TransGen (TcMma.TcStep L X) src i →
      ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
        TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r)
include hp hX hFw hT hO hR hI hB hN hRaw hNc hv hPS hG ht hmd hE hold

/-- **The result of QK MMA 15 of block `r` at a cell**: the sum over the sixteen MMAs and elements
of the query value times the slot's value, at the feature of the cell's lane, for a valid slot. -/
theorem qk_cell_sum {g i r : Nat} {s : TcMma.OperandSpec} {mask : List Nat} {cell : TcMma.Cell}
    {v : Value} (he : X.get (g, i) = some ⟨TmemRow.qkPc 15, .tc (.mma 400 s true mask)⟩)
    (hd : X.async.mmaDone (g, i) = true) (hr : TcMma.Result L Assumptions.all X (g, i) cell v)
    (hb : (g, i) = b ∨ Relation.TransGen (TcMma.TcStep L X) (g, i) b)
    (hiss : mmaIssues ((X.tr g).take i) = 24 * r + 15)
    (hvalid : slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) r)
      (w0BlockSlot P (ctaidY L g) r (cell.column - 400))) :
    v = .float .f32 (∑ k ∈ Finset.range 16, ∑ t ∈ Finset.range 16,
      P.q (ctaidY L g) (ctaidX L g) (cell.lane % 64) (QueryTile.feature k cell.lane t) *
        slotValue P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) r)
          (w0BlockSlot P (ctaidY L g) r (cell.column - 400))
          (QueryTile.feature k cell.lane t)) := by
  obtain ⟨j, a, hj, hterm, -, ⟨r', hcnt0⟩, hval⟩ :=
    qk_chain hp hX hFw hT hO hPS hG ht hmd hE b hold 15 (by omega) he hd hr hb
  have hrr : r' = r := by
    have := hcnt0 15 le_rfl
    rw [hj, hiss] at this
    omega
  have hcnt : ∀ k' ≤ 15, mmaIssues ((X.tr g).take (j k')) = 24 * r + k' := hrr ▸ hcnt0
  rw [hval]
  congr 1
  refine Finset.sum_congr rfl fun k' hk' => ?_
  have hk16 : k' < 16 := by simpa using hk'
  obtain ⟨s', ops, row, col, x, y, he', hops, hpos, hx, hy, hsum⟩ := hterm k' (by omega)
  obtain ⟨_, -, -, -, -, hon, hmo⟩ := qk_pc hT hX he'
  have hD : s'.descriptor = MmaFoot.qkD := MmaFoot.qkD_eq hmo.2.1
  obtain ⟨hrow, hcol, hlane, hcolumn, hopr⟩ := MmaFoot.qk_cell_geom hD hpos
  have hcl : cell.column - 400 = col % 64 := by omega
  rw [hsum]
  refine Finset.sum_congr rfl fun t htm => ?_
  have htt : t < 16 := by simpa using htm
  have hfe : QueryTile.feature k' col t = QueryTile.feature k' cell.lane t := by
    simp only [QueryTile.feature]
    omega
  have hxe := qk_a_elem hp hX hFw hT hO hR hI hB ht hmd (noUbInner hX) he' hk16 hops
    (r := TcMma.operandRow s'.descriptor row col) (by omega) htt
  obtain ⟨d, kk, hkk16, hcn, yy, hyy, hyv⟩ :=
    qk_b_slot hp hX hFw hR hI hB hN hRaw hNc hv he' hon.1 hops hcol htt
  have hdr : d = r ∧ kk = k' := by
    have := hcnt k' (by omega)
    omega
  obtain ⟨rfl, rfl⟩ := hdr
  have hxv := hx t htt
  have hyv' := hy t htt
  rw [hxe] at hxv
  rw [hyy] at hyv'
  rw [← Except.ok.inj hxv, ← Except.ok.inj hyv']
  have hvv := hyv (by rw [hcl] at hvalid; exact hvalid)
  rw [hopr, hvv, hfe, hcl]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
