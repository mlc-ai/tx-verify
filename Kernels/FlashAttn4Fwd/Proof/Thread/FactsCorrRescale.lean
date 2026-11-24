-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrValues
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrRstSite
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread
public import Lemmas.Flow.SplitJoin

@[expose] public section

/-! # The correction warps' rescale values (`CorrValues.rescale`, `TcMmaThreadFacts.corr_f32`)

A correction thread's `tcgen05.st` is the store of a rescale chunk (`corr_tst_vals`): value `p` is
half `p % 2` of the product `rs d (p / 2) (p % 2)` of pair `p / 2` of the chunk with the factor
word packed twice. The run invariant names the chunk's load in the trip's credit (`Counts.rsLd`)
and the read of `α` after the trip's sync (`Counts.rsSt`). When the load returned
single-precision floats and the read a canonical word (`rst_operands`; at the end from
`Safety.LoadFloats` and `Safety.StatsFloats`), the products are the real products: a canonical
word, the payload `α` or a 32-bit pattern encoding it, packs with itself into a pair whose halves
both read as `α` (`rcPair_split`), so value `p` is `o · α` for the loaded value `o`
(`rs_val_f32`, `CorrValues_rescale`), a single-precision float (`TcMmaThreadFacts_corr_f32`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Half `p % 2` of the product of pair `p / 2` with `α`**, for a chunk of sixteen
single-precision floats and a canonical factor word reading as `α`. -/
theorem rs_val_f32 (d : Correction.D) (p : Nat) (o α : ℝ) (hF : F32s d.o)
    (hl : d.o.length = 16) (hp : p < 16) (ho : d.o.getD p (b32 0) = .float .f32 o)
    (ha : F32Val d.aw α) :
    Correction.rs d (p / 2) (p % 2) = .float .f32 (o * α) := by
  obtain ⟨x, hx⟩ := f32s_getD hF (show 2 * (p / 2) < d.o.length by omega)
  obtain ⟨y, hy⟩ := f32s_getD hF (show 2 * (p / 2) + 1 < d.o.length by omega)
  have hpr := prodV_rc d (p / 2) hx hy ha
  unfold Correction.rs
  rw [hpr]
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · rw [ite_eq_left h]
    rw [show 2 * (p / 2) = p by omega, ho] at hx
    simp only [Value.float.injEq, true_and] at hx
    rw [hx]
    rfl
  · rw [ite_eq_right (by omega)]
    rw [show 2 * (p / 2) + 1 = p by omega, ho] at hy
    simp only [Value.float.injEq, true_and] at hy
    rw [hy]
    rfl

/-- On such a chunk and factor, every half of a product is a single-precision float. -/
theorem rs_f32 (d : Correction.D) (q h : Nat) (hq : q < 8) (hF : F32s d.o)
    (hl : d.o.length = 16) {α : ℝ} (ha : F32Val d.aw α) :
    ∃ x, Correction.rs d q h = .float .f32 x := by
  obtain ⟨x, hx⟩ := f32s_getD hF (show 2 * q < d.o.length by omega)
  obtain ⟨y, hy⟩ := f32s_getD hF (show 2 * q + 1 < d.o.length by omega)
  unfold Correction.rs
  rw [prodV_rc d q hx hy ha]
  split_ifs <;> exact ⟨_, rfl⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **The operands of a rescale store**: when the thread's loads before event `i` return
single-precision floats and its reads before `i` canonical words, the chunk of a rescale store
site is sixteen floats and its factor word reads as a number. -/
theorem rst_operands {g i : Nat} {d : Correction.D} {st : Fin 2} {j : Fin 8}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (hc : Correction.Counts L g d ((X.tr g).take i)) (hs : d.site = .rst st j)
    (hL : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals')
    (hR : ∀ k < i, ∀ pc (ac : Acc) (bs : List (Option Byte)),
      X.get (g, k) = some ⟨pc, .rd ac bs⟩ → ∃ x, F32Read bs x) :
    F32s d.o ∧ d.o.length = 16 ∧ ∃ α, F32Val d.aw α := by
  obtain ⟨r, hr, pcl, hgl, -⟩ := hc.rsLd st j (by unfold Correction.rsChunk; exact .inr hs)
  rw [List.length_take] at hr
  have hri : r < i := by omega
  rw [take_get hri] at hgl
  obtain ⟨_, _, _, -, -, -, -, -, hlen⟩ := corr_tld hpre hX ht hw hw' hgl
  obtain ⟨r', hr', pcr, ac, bs, hgr, -, hvr, -⟩ := hc.rsSt st (by
    unfold Correction.rsSite Correction.rsChunk; exact .inr (.inr (.inl ⟨j, .inr hs⟩)))
  rw [List.length_take] at hr'
  have hri' : r' < i := by omega
  rw [take_get hri'] at hgr
  obtain ⟨α, v, hv, hF⟩ := hR r' hri' _ _ _ hgr
  rw [hv] at hvr
  injection hvr with hvr
  rw [hvr] at hF
  exact ⟨hL r hri _ _ _ hgl, hlen, α, hF⟩

/-- **A correction thread's `tcgen05.st`** is a rescale chunk's store of the products. -/
theorem corr_tst_vals {g i pc a : Nat} {vals : List Value} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, i) = some ⟨pc, .tc (.st a vals .s32x32b)⟩) :
    ∃ (d : Correction.D) (st : Fin 2) (j : Fin 8),
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧ d.site = .rst st j ∧
      a = Correction.tmem L g (256 + 128 * st.val + 16 * j.val) ∧ vals.length = 16 ∧
      ∀ p < 16, vals[p]? = some (Correction.rs d (p / 2) (p % 2)) := by
  obtain ⟨d, st, j, hσ, hc, hi, hs, ha, hl⟩ := corr_tst hpre hX ht hw hw' he
  refine ⟨d, st, j, hc, hi, hs, ha, hl, fun p hp => ?_⟩
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨q, hq, -⟩ |
    ⟨d', t, ins, o, hσ', -, -, hat, hcode, hf, -⟩
  · rw [hσ] at hq; cases hq
  rw [hσ] at hσ'
  injection hσ' with hσ'
  injection hσ' with hσ'
  injection hσ' with hσ'
  injection hσ' with hσ'
  subst hσ'
  exact Correction.rst_store hs hat hcode hf rfl hp

/-- **`TcMmaThreadFacts.corr_f32`**: a correction store writes single-precision floats, when the
thread's earlier loads returned single-precision floats and its earlier reads canonical words. -/
theorem TcMmaThreadFacts_corr_f32 {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12) (hs : X.TSt (h, i) a vals .s32x32b)
    (hL : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (h, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals')
    (hR : ∀ k < i, ∀ pc (ac : Acc) (bs : List (Option Byte)),
      X.get (h, k) = some ⟨pc, .rd ac bs⟩ → ∃ x, F32Read bs x) :
    F32s vals := by
  obtain ⟨pc, he⟩ := hs
  obtain ⟨d, _, _, hc, -, hsd, -, hl, hv⟩ := corr_tst_vals hpre hX ht hw hw' he
  obtain ⟨hF, hlo, α, ha⟩ := rst_operands hpre hX ht hw hw' hc hsd hL hR
  intro v hm
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hm
  have := hv p (by omega)
  rw [List.getElem?_eq_getElem hp, Option.some.injEq] at this
  rw [this]
  exact rs_f32 d _ _ (by omega) hF hlo ha

/-- **`CorrValues.rescale`**: a rescale store of credit `q` holds, at each cell, the product of the
value the load of the cell in credit `q` returned and the factor the statistics load of the trip
read. -/
theorem CorrValues_rescale {g i a p st q : Nat} {vals : List Value} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : X.TSt (g, i) a vals .s32x32b) (hst : st < 2)
    (hq : pArr L X g st i = q) (hp : p < vals.length) (hin : InO st (tcDataCell32 L g a p)) :
    ∃ i' a' p' r, ∃ vals' : List Value, ∃ bs : List (Option Byte), i' < i ∧
      X.TLd (g, i') a' vals' .s32x32b ∧ pArr L X g st i' = q ∧ p' < vals'.length ∧
      tcDataCell32 L g a' p' = tcDataCell32 L g a p ∧ r < i ∧
      StatRead L X g st ((kvBlocks P + 1) * ((q - 1) / kvBlocks P) + 1 +
        (q - 1) % kvBlocks P) r bs ∧
      (F32s vals' → ∀ o α : ℝ, vals'[p']? = some (.float .f32 o) →
        F32Read bs α → vals[p]? = some (.float .f32 (o * α))) := by
  obtain ⟨pc, he⟩ := hs
  obtain ⟨d, st0, j, hc, hi, hsd, rfl, hl, hv⟩ := corr_tst_vals hpre hX ht hw hw' he
  rw [hl] at hp
  have hcol := tmem_column L g g (256 + 128 * st0.val + 16 * j.val) p (by omega)
  simp only [InO, hcol] at hin
  obtain rfl : st = st0.val := by omega
  have hkv := corr_trips_eq hpre
  have htr := hi.trip
  have hT := corr_trips_pos hpre
  obtain ⟨site, I, t, aw, aa, o⟩ := d
  simp only at hsd htr
  subst hsd
  have ht1 := htr (by fin_cases st0 <;> rfl)
  -- the credit
  have hfp : Correction.freePos L st0.val ⟨.rst st0 j, I, t, aw, aa, o⟩ = 1 + t := by
    fin_cases st0 <;> simp [Correction.freePos]
  have hq' : q = Correction.trips L * I + (1 + t) := by
    rw [← hq, pArr, pReadyBar_lead, hc.free st0.val st0.isLt, hfp]
  -- the load of the chunk
  obtain ⟨r, hr, pcl, hgl, hcl⟩ := hc.rsLd st0 j (by unfold Correction.rsChunk; exact .inr rfl)
  rw [List.length_take] at hr
  have hri : r < i := by omega
  rw [take_get hri] at hgl
  rw [take_take_le hri.le] at hcl
  obtain ⟨_, _, _, -, -, -, -, -, hlen⟩ := corr_tld hpre hX ht hw hw' hgl
  -- the read of `α`
  obtain ⟨r', hr', pcr, ac, bs, hgr, hlr, hvr, hcr⟩ :=
    hc.rsSt st0 (by
      unfold Correction.rsSite Correction.rsChunk; exact .inr (.inr (.inl ⟨j, .inr rfl⟩)))
  rw [List.length_take] at hr'
  have hri' : r' < i := by omega
  rw [take_get hri'] at hgr
  rw [take_take_le hri'.le] at hcr
  obtain ⟨_, str, -, -, -, -, hcl'⟩ := corr_rd hpre hX ht hw hw' hgr
  have hstr : str = st0 := by
    obtain ⟨-, hl2, -⟩ := hcl'
    rw [hlr] at hl2
    simp only [Correction.ownLoc, statsWord, Correction.sb, Loc.mk.injEq, Correction.rowOf,
      Correction.tidOf, rowOf] at hl2
    exact Fin.ext (by omega)
  subst hstr
  refine ⟨r, _, p, r', o, bs, hri, ⟨pcl, hgl⟩, ?_, by rw [hlen]; omega, rfl, hri',
    ⟨pcr, ac, hgr, hcl', ?_⟩,
    ?_⟩
  · rw [pArr, pReadyBar_lead, hcl, hq']
  · have hkw := corr_kOf hw hw'
    rw [corr_barOrd hpre hX ht hw hw' r' (by omega),
      show warpOf L g - 5 + 4 * str.val = Correction.kOf L g + 3 + 4 * str.val by omega, hcr,
      hq', ← hkv]
    have hdiv : (Correction.trips L * I + (1 + t) - 1) / Correction.trips L = I := by
      rw [show Correction.trips L * I + (1 + t) - 1 = t + Correction.trips L * I by omega,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]
      simp
    have hmod : (Correction.trips L * I + (1 + t) - 1) % Correction.trips L = t := by
      rw [show Correction.trips L * I + (1 + t) - 1 = t + Correction.trips L * I by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hdiv, hmod]
    ring
  · intro hFo ov α ho ⟨v, hreb, hF⟩
    rw [hreb] at hvr
    injection hvr with hvr
    subst hvr
    have ho' : o.getD p (b32 0) = .float .f32 ov := by
      rw [List.getD_eq_getElem?_getD, ho]; rfl
    rw [hv p hp, rs_val_f32 _ p ov α hFo hlen hp ho' hF]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
