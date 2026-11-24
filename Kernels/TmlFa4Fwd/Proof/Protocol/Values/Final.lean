-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Links
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.OOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceFacts
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The results of the value recursion

From the links of a complete execution (`ValueLinks`): the softmax loads return the rows' dot
products (`Score.lean`), so the probabilities are the running softmax of the rows' weights
(`row_fold`). The accumulator of a cell is rescaled by the row's factors (`before_eq`), so after the
last tile it is the last scale times the weighted sum of the values, and a final load over the row
sum is the row's attention (`final_attention`). The row sum and maximum give the row's log-sum-exp
(`row_lse`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {T : Nat → Option Tile}
  {I : Nat → Inputs} {D : Nat → RowData}

/-- The weights of the loaded scores are the specification's. -/
theorem weightOf_eq {t : Tile} {J : Inputs} (hJ : InputsAre p t J) {st ρ : Nat} (hst : st < 2)
    (hρ : ρ < 128) (hv : t.Valid p st ρ) {u k : Nat} (hu : u < t.n) (hk : k < 128) :
    weightOf p t (t.rowOf st ρ) (fun u k => dot J st u ρ k) u k =
      if t.key u k < p.keyCount t.batch (t.rowOf st ρ) then
        weight p t.batch t.head (t.rowOf st ρ) (t.key u k) else 0 := by
  unfold weightOf
  by_cases h : t.key u k < p.keyCount t.batch (t.rowOf st ρ)
  · rw [ite_eq_left h, ite_eq_left h]
    have hkl : t.key u k < p.kLength t.batch := by
      unfold Params.keyCount at h
      omega
    have hdot : dot J st u ρ k = ∑ d ∈ Finset.range 128,
        p.q (p.qOffset t.batch + t.rowOf st ρ) t.head d *
          p.k (p.page t.batch (t.key u k / 16)) (t.head / 6) (t.key u k % 16) d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := Finset.mem_range.mp hd
      rw [hJ.q st hst ρ hρ hv d hd', hJ.k u hu k hk hkl d hd']
    simp only [weight, score, hdot, biasAt]
  · rw [ite_eq_right h, ite_eq_right h]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hL : ValueLinks p L X T I D)
include hp hX hFw hL

/-- The scores a softmax lane loads. -/
theorem soft_scores {h : Nat} (hw : Prologue.warpIndex L h < 8) {i a j u : Nat}
    {vals : List Value} (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length)
    (hu : sPolls L X h (Prologue.warpIndex L h / 4) i = u + 1) :
    vals[j]? = some (.float .f32 (dot (I (h / L.block)) (Prologue.warpIndex L h / 4) u
      (rowIx L h) ((tcDataCell32 L h a j).column - 128 * (Prologue.warpIndex L h / 4)))) := by
  have hl : (tcDataCell32 L h a j).lane = rowIx L h := by
    have hb := hp.block
    simp only [tcDataCell32, laneBase, laneOf, rowIx]
    rw [hb]
    omega
  rw [← hl]
  exact score_load hp hX hFw hL.bytes hw hld hj hu

/-- **The probabilities of a CTA's softmax lanes.** -/
theorem ctaP (c : Nat) : CtaP L X (fun h => (D h).P) c := fun h hh hw _ =>
  (hL.soft h hh hw (fun u k => dot (I (h / L.block)) (Prologue.warpIndex L h / 4) u (rowIx L h) k)
    (fun hld hj hu => soft_scores hp hX hFw hL hw hld hj hu)).1

/-- **The correction stores are numbers.** -/
theorem corrF32 : CorrF32 L X := by
  intro h i a vals hh h8 h12 hst v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨st, hst2, hcells, -⟩ := (oAccFacts hp hX hFw).corr_st hh h8 h12 hst
  obtain ⟨_, _, _, x, _, _, _, _, _, _, hval⟩ :=
    hL.corr.store hst2 h8 h12 hst hj (hcells j hj) rfl
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hval
  exact ⟨_, hval⟩

omit hX hFw hL in
/-- A softmax lane of a row of a launched CTA. -/
theorem softLane_spec {c st ρ : Nat} (hc : c < L.grid) (hst : st < 2) (hρ : ρ < 128) :
    softLane L c st ρ < L.threads ∧ Prologue.warpIndex L (softLane L c st ρ) < 8 ∧
      Prologue.warpIndex L (softLane L c st ρ) / 4 = st ∧ softLane L c st ρ / L.block = c ∧
      rowIx L (softLane L c st ρ) = ρ := by
  have hb := hp.block
  unfold softLane Prologue.warpIndex rowIx Launch.threads
  rw [hb]
  have := Nat.mul_le_mul_right 512 (show c + 1 ≤ L.grid by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The running softmax of a valid row.** -/
theorem row_fold {c : Nat} {t : Tile} (hT : T c = some t) {st ρ : Nat} (hst : st < 2)
    (hρ : ρ < 128) (hv : t.Valid p st ρ) :
    Fold t.n (fun u k => if t.key u k < p.keyCount t.batch (t.rowOf st ρ) then
        weight p t.batch t.head (t.rowOf st ρ) (t.key u k) else 0)
      (D (softLane L c st ρ)).P (D (softLane L c st ρ)).c (D (softLane L c st ρ)).f
      (D (softLane L c st ρ)).rs ∧
    (D (softLane L c st ρ)).c (t.n - 1) =
      (2 : ℝ) ^ (-(abiFloat p.scaleLog2Bits * (D (softLane L c st ρ)).rm)) := by
  obtain ⟨hc, -⟩ := hL.tile c t hT
  obtain ⟨h1, h2, h3, h4, h5⟩ := softLane_spec hp hc hst hρ
  obtain ⟨-, hf⟩ := hL.soft _ h1 h2
    (fun u k => dot (I (softLane L c st ρ / L.block))
      (Prologue.warpIndex L (softLane L c st ρ) / 4) u (rowIx L (softLane L c st ρ)) k)
    (fun hld hj hu => soft_scores hp hX hFw hL h2 hld hj hu)
  obtain ⟨hF, hm⟩ := hf t (by rw [h4]; exact hT) (by rw [h3, h5]; exact hv)
  rw [h3, h4, h5] at hF
  refine ⟨?_, hm⟩
  have hw := fun {u k : Nat} (hu : u < t.n) (hk : k < 128) =>
    weightOf_eq (hL.inputs c t hT) hst hρ hv hu hk
  refine ⟨hF.pos, fun u hu k hk => ?_, fun u hu => ?_, hF.le, ?_⟩
  · rw [hF.prob u hu k hk, hw hu hk]
  · rcases hF.factor u hu with h | h
    · exact .inl h
    · exact .inr fun v hv' k hk => (hw (by omega) hk).symm.trans (h v hv' k hk)
  · rw [hF.sum]
    congr 1
    exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun k hk =>
      hw (Finset.mem_range.mp hu) (Finset.mem_range.mp hk)

/-- **The accumulator before a later tile** is the one after the tile before, rescaled. -/
theorem before_eq {c : Nat} {t : Tile} (hT : T c = some t) {st ρ d u : Nat} (hst : st < 2)
    (hρ : ρ < 128) (hd : d < 128) (hv : t.Valid p st ρ) (hu : u + 1 < t.n) :
    before L X (D (softLane L c st ρ)).P (I c) st ⟨c, ρ, 256 + 128 * st + d⟩ d (u + 1) =
      acc L X (D (softLane L c st ρ)).P (I c) st ⟨c, ρ, 256 + 128 * st + d⟩ d u *
        (D (softLane L c st ρ)).f (u + 1) := by
  obtain ⟨hc, -⟩ := hL.tile c t hT
  obtain ⟨hF, -⟩ := row_fold hp hX hFw hL hT hst hρ hv
  have hO : InO st (⟨c, ρ, 256 + 128 * st + d⟩ : Cell) :=
    ⟨by simp only; omega, by simp only; omega⟩
  by_cases hex : ∃ y, CorrStored L X st ⟨c, ρ, 256 + 128 * st + d⟩ (u + 1) y
  · obtain ⟨y, hy⟩ := hex
    rw [before_stored hy (fun y' hy' => corrStored_unique hp hX hFw hO hy' hy)]
    obtain ⟨g, k, a, j, vals, hs, hj, hceq, hpa, hval⟩ := hy
    have ht := scoreFacts hp hX hFw
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hs)
    have h8 : 8 ≤ Prologue.warpIndex L g := by
      by_contra h8
      have hP' := (ht.soft_st hgl (by omega) hs).1 j hj
      rw [hceq] at hP'
      unfold InP at hP'
      unfold InO at hO
      omega
    obtain ⟨k', a', j', x, vals', hld, hj', hcc, hpa', hx, hy'⟩ :=
      hL.corr.store hst h8 hgw hs hj (by rw [hceq]; exact hO) hpa
    have hgc : g / L.block = c := congrArg Cell.cta hceq
    have hgr : rowIx L g = ρ := by
      have h := congrArg Cell.lane hceq
      have hb := hp.block
      simp only [tcDataCell32, laneBase, laneOf] at h
      unfold rowIx
      rw [hb] at h ⊢
      omega
    have hloaded := corr_load hp hX hFw hL.bytes (corrF32 hp hX hFw hL) (P := fun h => (D h).P)
      h8 hgw (ctaP hp hX hFw hL _) hld hj' (st := st) (by rw [hcc, hceq]; exact hO)
    rw [hcc, hceq, hgc, hpa', hx] at hloaded
    simp only [Option.some.injEq, Value.float.injEq, true_and, Nat.add_sub_cancel,
      Nat.add_sub_cancel_left] at hloaded
    rw [hval, hgc, hgr, hloaded] at hy'
    simpa using hy'
  · rw [before_skip hex]
    have h1 := hL.corr.skip t hT rfl hc hst hρ hd hv (by omega) hu hex
    have h2 := hF.le (u + 1) hu
    rw [le_antisymm h2 h1, mul_one]

/-- **The accumulator after the last tile** is the last scale times the weighted sum of values. -/
theorem acc_final {c : Nat} {t : Tile} (hT : T c = some t) {st ρ d : Nat} (hst : st < 2)
    (hρ : ρ < 128) (hd : d < 128) (hv : t.Valid p st ρ) :
    acc L X (D (softLane L c st ρ)).P (I c) st ⟨c, ρ, 256 + 128 * st + d⟩ d (t.n - 1) =
      (D (softLane L c st ρ)).c (t.n - 1) *
        ∑ j ∈ Finset.range (p.keyCount t.batch (t.rowOf st ρ)),
          weight p t.batch t.head (t.rowOf st ρ) j *
            p.v (p.page t.batch (j / 16)) (t.head / 6) (j % 16) d := by
  obtain ⟨hc, hok⟩ := hL.tile c t hT
  obtain ⟨hF, -⟩ := row_fold hp hX hFw hL hT hst hρ hv
  have hn := hok.blocks
  have h := hF.acc_eq (v := fun u k => (I c).v u k d)
    (a := acc L X (D (softLane L c st ρ)).P (I c) st ⟨c, ρ, 256 + 128 * st + d⟩ d)
    (by simp only [acc, before, zero_add, pvSum])
    (fun u hu => by
      rw [acc, before_eq hp hX hFw hL hT hst hρ hd hv hu]
      rfl) (t.n - 1) (by omega)
  rw [h, show t.n - 1 + 1 = t.n by omega]
  congr 1
  rw [← visit_sum_lt (hok.keys st hst ρ hρ hv) (fun j => weight p t.batch t.head (t.rowOf st ρ) j *
    p.v (p.page t.batch (j / 16)) (t.head / 6) (j % 16) d)]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun k hk => ?_
  simp only [ite_mul, zero_mul]
  by_cases hkey : t.key u k < p.keyCount t.batch (t.rowOf st ρ)
  · have hkl : t.key u k < p.kLength t.batch := by
      unfold Params.keyCount at hkey
      omega
    rw [ite_eq_left hkey, ite_eq_left (by exact hkey),
      (hL.inputs c t hT).v u (Finset.mem_range.mp hu) k (Finset.mem_range.mp hk) hkl d hd]
    rfl
  · rw [ite_eq_right hkey, ite_eq_right (by exact hkey)]

omit hp hX hFw in
/-- The sum of a row's weights is the row's mass. -/
theorem weights_mass {c : Nat} {t : Tile} (hT : T c = some t) {st ρ : Nat} (hst : st < 2)
    (hρ : ρ < 128) (hv : t.Valid p st ρ) :
    ∑ u ∈ Finset.range t.n, ∑ k ∈ Finset.range 128,
        (if t.key u k < p.keyCount t.batch (t.rowOf st ρ) then
          weight p t.batch t.head (t.rowOf st ρ) (t.key u k) else 0) =
      mass p t.batch t.head (t.rowOf st ρ) :=
  visit_sum_lt ((hL.tile c t hT).2.keys st hst ρ hρ hv) _

/-- **A final load over the row sum is the row's attention.** -/
theorem final_attention {t : Tile} {st g i a j d : Nat} {x : ℝ} {vals : List Value}
    (hT : T (g / L.block) = some t) (hst : st < 2) (h8 : 8 ≤ Prologue.warpIndex L g)
    (h12 : Prologue.warpIndex L g < 12) (hd : d < 128) (hv : t.Valid p st (rowIx L g))
    (hld : X.TLd (g, i) a vals .s32x32b) (hj : j < vals.length)
    (hcol : (tcDataCell32 L g a j).column = 256 + 128 * st + d) (hpa : pArr L X g st i = t.n)
    (hx : vals[j]? = some (.float .f32 x)) :
    x * (D (softLane L (g / L.block) st (rowIx L g))).rs⁻¹ =
      attention p t.batch t.head (t.rowOf st (rowIx L g)) d := by
  have hρ : rowIx L g < 128 := Nat.mod_lt _ (by decide)
  have hcell : tcDataCell32 L g a j = ⟨g / L.block, rowIx L g, 256 + 128 * st + d⟩ := by
    have hb := hp.block
    simp only [tcDataCell32, laneBase, laneOf, rowIx, Cell.mk.injEq, true_and] at hcol ⊢
    rw [hb]
    exact ⟨by omega, hcol⟩
  have hload := corr_load hp hX hFw hL.bytes (corrF32 hp hX hFw hL) (P := fun h => (D h).P)
    h8 h12 (ctaP hp hX hFw hL _) hld hj (st := st)
    (by rw [hcell]; exact ⟨by simp only; omega, by simp only; omega⟩)
  rw [hcell, hpa, hx] at hload
  simp only [Option.some.injEq, Value.float.injEq, true_and, Nat.add_sub_cancel_left] at hload
  obtain ⟨hF, -⟩ := row_fold hp hX hFw hL hT hst hρ hv
  have hacc := acc_final hp hX hFw hL hT hst hρ hd hv
  rw [hF.mean (hL.tile _ _ hT).2.blocks (hload.trans hacc),
    weights_mass hL hT hst hρ hv]
  rfl

omit hX hFw in
/-- A valid row has a key. -/
theorem mass_pos {c : Nat} {t : Tile} (hT : T c = some t) {st ρ : Nat} (hv : t.Valid p st ρ) :
    0 < mass p t.batch t.head (t.rowOf st ρ) := by
  have hb := (hL.tile c t hT).2.batch
  have hl := (hp.lengths t.batch hb).2.1
  unfold mass
  refine Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (by norm_num) _) ⟨0, ?_⟩
  rw [Finset.mem_range]
  unfold Params.keyCount
  unfold Tile.Valid at hv
  omega

/-- **The row sum and maximum give the row's log-sum-exp.** -/
theorem row_lse {c : Nat} {t : Tile} (hT : T c = some t) {st ρ : Nat} (hst : st < 2)
    (hρ : ρ < 128) (hv : t.Valid p st ρ) :
    (abiFloat p.scaleLog2Bits * (D (softLane L c st ρ)).rm +
        Real.logb 2 (D (softLane L c st ρ)).rs) * abiFloat 0x3F317218 =
      lse p t.batch t.head (t.rowOf st ρ) := by
  obtain ⟨hF, hm⟩ := row_fold hp hX hFw hL hT hst hρ hv
  rw [hF.sum, weights_mass hL hT hst hρ hv, hm,
    log_scaled (mass_pos hp hL hT hv), lse]
  ring

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
