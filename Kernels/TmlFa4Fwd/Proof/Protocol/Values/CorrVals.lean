-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CorrStore
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LseStore
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.OutSource
import Kernels.TmlFa4Fwd.Proof.Correction.Export.StoreData
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Final
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Lemmas.Tensor.TensorSwizzle
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The values of the correction lanes' final and log-sum-exp stores

`StatVals`: the row-sum and row-maximum reads of a valid row's correction lane return those of its
softmax lane. With it, and with the lanes' data reads (`StatReads`, the loads' numbers), the final
stores hold the loaded elements over the row sum (`final_vals`) and the log-sum-exp stores the row's
(`lse_vals`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Site StatTo LoadTo)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The statistics reads of the final stage**: the row-sum and the row-maximum read of a valid
row's correction lane return the sum and the maximum of the row's softmax lane. -/
structure StatVals (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop where
  sum : ∀ {h i : Nat} {a : Acc} {bs : List (Option Byte)} (st : Fin 2) {t : Tile},
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 →
    X.get (h, i) = some ⟨(Site.fsum st).pc, .rd a bs⟩ → T (h / L.block) = some t →
    t.Valid p st.val (rowIx L h) →
      rebuild 3 bs = .ok (.float .f32 (D (softLane L (h / L.block) st.val (rowIx L h))).rs)
  max : ∀ {h i : Nat} {a : Acc} {bs : List (Option Byte)} (st : Fin 2) {t : Tile},
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 →
    X.get (h, i) = some ⟨(Site.fmax st).pc, .rd a bs⟩ → T (h / L.block) = some t →
    t.Valid p st.val (rowIx L h) →
      rebuild 3 bs = .ok (.float .f32 (D (softLane L (h / L.block) st.val (rowIx L h))).rm)

/-- The row sums of the valid rows are not zero. -/
def RowSums (p : Params) (T : Nat → Option Tile) (L : Launch) (D : Nat → RowData) : Prop :=
  ∀ {c : Nat} {t : Tile} {st ρ : Nat}, T c = some t → st < 2 → ρ < 128 → t.Valid p st ρ →
    (D (softLane L c st ρ)).rs ≠ 0

/-- **The row sums are positive**, from the links of the values. -/
theorem rowSums (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {T : Nat → Option Tile} {I : Nat → Inputs} {D : Nat → RowData}
    (hL : ValueLinks p L X T I D) : RowSums p T L D := by
  intro c t st ρ hT hst hρ hv
  obtain ⟨hF, -⟩ := row_fold hp hX hFw hL hT hst hρ hv
  have hn := (hL.tile c t hT).2.blocks
  rw [hF.sum, weights_mass hL hT hst hρ hv]
  exact (mul_pos (hF.pos _ (by omega)) (mass_pos hp hL hT hv)).ne'

private theorem xor_cancel : ∀ a < 8, ∀ x < 8, ∀ k < 8, a ^^^ k = x ^^^ a → k = x := by decide

private theorem xor_lt : ∀ a < 8, ∀ b < 8, a ^^^ b < 8 := by decide

private theorem ln2_abi : abiFloat 0x3F317218 = Correction.ln2F := by
  have h : f32Value 0x3F317218 = some (1453635 / 2097152) := by
    norm_num [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
      Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  simp [abiFloat, h]

/-- The address of a staging word's byte. -/
theorem stageLoc_addr (hs : L.sharedBase % 1024 = 0) {c st ρ d k : Nat} (hk : k < 4) :
    (stageLoc L c st ρ d k).addr = L.sharedBase + 3072 + 65536 * st + 16384 * (d / 32) + 128 * ρ +
      16 * ((d % 32 / 4) ^^^ (ρ % 8)) + (4 * (d % 4) + k) := by
  have h1 : (128 * ρ + 4 * (d % 32) + k) / 128 = ρ := by omega
  have h2 : (128 * ρ + 4 * (d % 32) + k) / 16 % 8 = d % 32 / 4 := by omega
  have h3 : (128 * ρ + 4 * (d % 32) + k) % 16 = 4 * (d % 4) + k := by omega
  have h4 : ((L.sharedBase + (3072 + 65536 * st + 16384 * (d / 32))) / 128 + ρ) % 8 = ρ % 8 := by
    generalize d / 32 = e
    omega
  simp only [stageLoc, TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors, h1, h3, h4, BitVec.toNat_xor, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ 3 = 8 from rfl, h2, Nat.mod_mod]
  omega

/-- The final store that covers a staging byte. -/
private theorem fst_cell (hp : Pre p L m) {h st d k : Nat} {st' : Fin 2} {j : Fin 16} {hh : Fin 2}
    {s : Nat} {a : Acc} (hd : d < 128) (hk : k < 4) (hs : s < 4)
    (hF : Correction.FstIs L h st' ⟨2 * (j.val % 4) + hh.val, by omega⟩ (j.val / 4) s a)
    (hc : a.Covers (stageLoc L (h / L.block) st (rowIx L h) d k)) :
    st'.val = st ∧ 8 * j.val + (4 * hh.val + s) = d ∧
      (stageLoc L (h / L.block) st (rowIx L h) d k).addr - a.loc.addr = k := by
  obtain ⟨hz, hl⟩ := hF
  have hcol := Correction.colW_col (L := L) (g := h) hp st' ⟨2 * (j.val % 4) + hh.val, by omega⟩
  change (Correction.colW L h st' _).toNat = _ + 16 * ((h % L.block % 8) ^^^ _) at hcol
  simp only at hcol
  obtain ⟨-, -, c3, c4⟩ := hc
  rw [hl] at c3 c4 ⊢
  rw [hz] at c4
  have hsb := hp.shared.1
  rw [stageLoc_addr hsb hk] at c3 c4 ⊢
  simp only [hcol] at c3 c4 ⊢
  simp only [Correction.lineAt, Correction.rowN, rowIx] at c3 c4 ⊢
  have hρ : h % L.block % 128 % 8 = h % L.block % 8 := by omega
  rw [hρ] at c3 c4 ⊢
  have hρ1 : h % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have h8 : h % L.block % 8 < 8 := Nat.mod_lt _ (by decide)
  have hj := j.isLt
  have hh2 := hh.isLt
  have hst' := st'.isLt
  have hA := xor_lt _ h8 (2 * (j.val % 4) + hh.val) (by omega)
  have hC := xor_lt (d % 32 / 4) (by omega) _ h8
  have hX := xor_cancel _ h8 (d % 32 / 4) (by omega) (2 * (j.val % 4) + hh.val) (by omega)
  generalize (h % L.block % 8) ^^^ (2 * (j.val % 4) + hh.val) = A at hA hX c3 c4 ⊢
  generalize (d % 32 / 4) ^^^ (h % L.block % 8) = C at hC hX c3 c4 ⊢
  generalize h % L.block % 128 = ρ at hρ1 c3 c4 ⊢
  have e1 : st'.val = st := by omega
  have e2 : j.val / 4 = d / 32 := by omega
  have e3 : A = C := by omega
  have e4 := hX e3
  have e5 : s = d % 4 := by omega
  refine ⟨e1, by omega, ?_⟩
  rw [e1, e2, e3, e5]
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hS : StatReads L X)
  (hLd : ∀ {e : EvId} {a : Nat} {vals : List Value}, X.TLd e a vals .s32x32b → F32s vals)
  {D : Nat → RowData} (hV : StatVals p L X (tileOf p L) D) (hR : RowSums p (tileOf p L) L D)
include hp hX hFw hS hLd hV hR

omit hp hX hFw hV hR in
/-- The reads of a correction lane before a position. -/
private theorem reads_to {h : Nat} (i : Nat)
    (hh : h < L.threads) (h8 : 8 ≤ Prologue.warpIndex L h) (h12 : Prologue.warpIndex L h < 12) :
    StatTo X h i ∧ LoadTo X h i :=
  ⟨fun _ _ s _ hg hpc hs => hS s hh h8 h12 hg hpc hs fun _ _ _ hl _ _ => hLd hl,
    fun _ _ _ _ hl => hLd hl⟩

/-- **The final stores of the correction lanes hold the loaded elements over the row sum.** -/
theorem final_vals : FinalVals p L X (tileOf p L) D := by
  intro h i pc a bs st d k h8 h12 he hst hd hk hc t hT hv
  have hh := Frame.lt_of_get hX he
  obtain ⟨h1, h2⟩ := reads_to hS hLd i hh h8 h12
  obtain ⟨st', j, hh', s, hs, ys, rs, hF, hbs, ⟨i1, a1, bs1, hg1, hv1⟩, i2, ad, vals, hl, hlen,
    hy, hcol, R, hRn, hpa⟩ :=
    Correction.corr_fst_data hp hX hFw h8 (by omega) h1 h2 he (hc.1.symm.trans rfl)
  obtain ⟨rfl, hdj, hoff⟩ := fst_cell hp hd hk hs hF hc
  have hr := hV.sum st' h8 h12 hg1 hT hv
  rw [hv1] at hr
  simp only [Except.ok.injEq, Value.float.injEq, true_and] at hr
  have hne := hR hT hst (Nat.mod_lt _ (by decide)) hv
  rw [← hr] at hne
  have hhl := hh'.isLt
  have hx : 4 * hh'.val + s < 8 := by omega
  obtain ⟨t', hT', hn⟩ := tile_rounds hp hh (hRn.mma hp hh)
  rw [hT] at hT'
  cases hT'
  refine ⟨i2, ad, 4 * hh'.val + s, ys (4 * hh'.val + s), vals, hl, by omega, ?_, by rw [hpa, hn],
    ?_, ?_⟩
  · simp only [tcDataCell32, show (2 : Nat) ^ 16 = 65536 from rfl, hcol]
    omega
  · exact hy _ hx
  · rw [← hr, wbyte, hoff, hbs, Correction.fRecip, ite_eq_left hne]
    have hWidth : (Value.float .f32 (ys (4 * hh'.val + s) * rs⁻¹)).bytes = 4 := rfl
    simp only [Value.toBytes, List.getElem?_map, hWidth, List.getElem?_range hk, Option.map_some]

/-- **The log-sum-exp stores hold the row's log-sum-exp.** -/
theorem lse_vals : LseVals p L X (tileOf p L) D := by
  intro h i pc a bs h8 h12 he hg t hT st hst hv hloc
  have hh := Frame.lt_of_get hX he
  obtain ⟨h1, h2⟩ := reads_to hS hLd i hh h8 h12
  obtain ⟨b, hb, hlo, hhi, st', rs, rm, hal, rfl, ⟨i1, a1, bs1, hg1, hv1⟩, i2, a2, bs2, hg2, hv2⟩ :=
    Correction.corr_lse_data hp hX hFw h8 (by omega) h1 h2 he hg
  have hT' := tileOf_eq (p := p) (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hh))
    ⟨hb, hlo, hhi⟩
  rw [hT] at hT'
  cases hT'
  obtain rfl : st'.val = st := by
    rw [hloc] at hal
    have := congrArg Loc.addr hal
    simp only [Params.lseLoc, globalLoc, workTile, Tile.rowOf, rowIx] at this
    omega
  have hr := hV.sum st' h8 h12 hg1 hT hv
  have hm := hV.max st' h8 h12 hg2 hT hv
  have hne := hR hT hst (Nat.mod_lt _ (by decide)) hv
  rw [hv1] at hr
  simp only [Except.ok.injEq, Value.float.injEq, true_and] at hr
  rw [hv2] at hm
  simp only [Except.ok.injEq] at hm
  rw [← erealValue_coe] at hm
  have hm := congrArg (Assumption.readEReal .f32) hm
  simp only [readEReal_erealValue_f32, Option.some.injEq, Except.ok.injEq] at hm
  rw [← hr] at hne ⊢
  have hc : Assumption.erealCompare .ne (rs : EReal) ((0 : ℝ) : EReal) = true := by
    rw [erealCompare_coe_ne]
    exact decide_eq_true hne
  rw [Correction.lseSel, ite_eq_left hc, Correction.lseOf, hm, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_mul, erealValue_coe, ln2_abi]
  rfl

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
