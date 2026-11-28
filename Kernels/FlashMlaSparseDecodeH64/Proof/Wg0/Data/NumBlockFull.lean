-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumChain2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumRd
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumVote
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondP
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondRmax
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.NumPld
import Lemmas.Flow.SetpReads

@[expose] public section

/-! # The value of one block, and the conditions of its runs

From the words of a valid block (`W0Ok`) and the statistics it starts from (`m`, `l`, `mx`, read
as numbers), the facts at the probability stores (`f_ost`) hold the new maximum (`w0Max`), the new
running sum (`w0Next`) and the sixteen bf16 probabilities; the conditions of the row-maximum, the
maximum exchange, the vote and the probability runs hold at their stages. -/

/-! # The scale pair

The pair of the scale's word twice reads as the scale. -/

/-! # The peer maximum's run has no fault outcome

`mld_cond_of_reads` (pcs 573-577) and `vt_cond_of_reads` (pcs 582-585): the conditions of the
runs (`Gen.mld_cond`: each item's outcome is no fault) from the readings of the words they read
(`%r1109`, `%r1110`, the true maximum `%r2885`, the carried maximum `%r2950`). The strict twin of
the tolerant `Reach` of the sites. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- `max.f32` of two words that read as lanes is no fault. -/
theorem w0k_max {r1 r2 : Nat} (hne : r1 ≠ r2) {va vb : Value} {x y : EReal} (ha : Rd va x)
    (hb : Rd vb y) : ∃ v, fF maxFL [.reg r1, .reg r2] [va, vb] = .ok v := by
  have e : fF maxFL [.reg r1, .reg r2] [va, vb] = maxFE va vb := by
    have h21 : (r2 == r1) = false := beq_false_of_ne (Ne.symm hne)
    simp [fF, fOpnd, lk, regsOf, regOf, maxFL, List.lookup, h21]
  exact ⟨_, e.trans (maxFE_reads (rd_read ha) (rd_read hb))⟩

/-- **The run of `mld` has no fault outcome.** -/
theorem mld_cond_of_reads (V : Nat → Value) {loc pm mx : EReal} {mR : ℝ} (h1 : Rd (V 1109) loc)
    (h2 : Rd (V 1110) pm) (h3 : Rd (V 2885) mx) (h4 : Rd (V 2950) (mR : EReal)) : mld_cond V := by
  have h479 : Rd (mld_v573 V) (max loc pm) := w0r_max (by decide) h1 h2
  unfold mld_cond
  simp only [mld_items0, xCond]
  refine ⟨w0k_max (by decide) h1 h2, ?_⟩
  rw [upd_one _ _ (d := 479) (v := mld_v573 V) rfl]
  refine ⟨w0k_max (by decide) h3 h479, ?_⟩
  rw [upd_one _ _ (d := 2885) (v := mld_v574 V) rfl]
  have hl : SK.ni.Lane (max loc pm) := rd_lane h479
  have hz : addEReal (max loc pm) (-(mR : EReal)) = some (max loc pm + -(mR : EReal)) := by
    have hn : ¬ ((max loc pm = ⊤ ∧ -(mR : EReal) = ⊥) ∨ (max loc pm = ⊥ ∧ -(mR : EReal) = ⊤)) := by
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact absurd h (by simp)
    simp only [addEReal, hn, ↓reduceIte]
  have hne : max loc pm + -(mR : EReal) ≠ ⊤ := by
    rcases hl with ⟨r, hr⟩ | hr <;> rw [hr] <;> simp [← EReal.coe_neg, ← EReal.coe_add]
  have hsub : subE true (mld_v573 V) (V 2950) =
      .ok (erealValue .f32 (max loc pm + -(mR : EReal))) :=
    subE_reads (rd_read h479) (rd_read h4) hz
  refine ⟨⟨_, hsub⟩, ?_⟩
  rw [upd_one _ _ (d := 1111) (v := erealValue .f32 (max loc pm + -(mR : EReal))) (by
    show [(1111, okVal _ (subE true (mld_v573 V) (V 2950)))] = _
    rw [hsub]; rfl)]
  refine ⟨⟨_, setpE_reads (c := .ord .gt) (fz := true) (Or.inl rfl)
    (x := max loc pm + -(mR : EReal)) (y := ((6 : ℝ) : EReal)) (readEReal_erealValue hne)
    (readEReal_of_valFloat valFloat_six)⟩, ?_⟩
  exact ⟨⟨_, rfl⟩, trivial⟩

/-- **The run of `vt` has no fault outcome**: `r21` and the carried maximum read as numbers. -/
theorem vt_cond_of_reads (V : Nat → Value) {r21 : EReal} {m : ℝ} (h479 : Rd (V 479) r21)
    (h2950 : Rd (V 2950) (m : EReal)) : vt_cond V := by
  have hmax : Rd (vt_v582 V) (max r21 (m : EReal)) := w0r_max (by decide) h479 h2950
  rw [w0Moved_eq (rd_lane h479)] at hmax
  have hv : SK.ni.Lane r21 := rd_lane h479
  unfold vt_cond
  simp only [vt_items0, xCond]
  refine ⟨w0k_max (by decide) h479 h2950, ?_⟩
  rw [upd_one _ _ (d := 480) (v := vt_v582 V) rfl]
  have e : vt_v583 V = .float .f32 (m - w0Moved r21 m) :=
    okVal_ok (w0v_sub (rd_read h2950) (rd_read hmax))
  refine ⟨⟨_, w0v_sub (rd_read h2950) (rd_read hmax)⟩, ?_⟩
  rw [upd_one _ _ (d := 1114) (v := vt_v583 V) rfl]
  refine ⟨⟨_, by
    show ex2E true (vt_v583 V) = _
    rw [e]; exact ex2E_real (readEReal_float _)⟩, ?_⟩
  rw [upd_one _ _ (d := 2951) (v := vt_v584 V) rfl]
  exact ⟨hmax.1.1, trivial⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

theorem w0c_scPair {x : BitVec 64} {sc : ℝ} (hx : Rd (.bits 32 x) (sc : EReal)) :
    pairRead (scPair x) = some (.ok ((sc : EReal), (sc : EReal))) := by
  have h32 : x.toNat < 2 ^ 32 := hx.1.2.2 32 x rfl
  have e : truncBits (64 / 2) (x ||| (0 <<< 32)) = x := by
    simp only [truncBits]
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.zero_shiftLeft, Nat.cast_zero, BitVec.or_zero, BitVec.toNat_ofNat,
      show 64 / 2 = 32 by norm_num]
    rw [show (x ||| 0 : BitVec 64) = x by ext i; simp, Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega)]
  unfold scPair
  rw [e]
  exact pairRead_join hx hx

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

/-- The statistics a block starts from, read as numbers: the value the block gives and the
conditions of its runs. -/
theorem w0_block_full_has {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {m l mx sk : Value} {lo : List Value} {mR lR : ℝ}
    (hm : Rd m (mR : EReal)) (hl : Rd l (lR : EReal)) {r0 : EReal} (hmx : Rd mx r0) :
    let V := lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
      (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)
    let Vr := lookupD (f_pld8 x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7))
    let Vm := lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)
    let Vh := lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)
    let Vj := lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)
    (Rd (V 2950) ((w0Max sc mR w : ℝ) : EReal) ∧
      Rd (V 2955) (((w0Next sc (mR, lR) w).2 : ℝ) : EReal) ∧
      (∀ t < 16, V (1115 + 3 * t) =
        Assumptions.bf16Pair (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t)))
          (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t + 1)))) ∧
      Rd (V 2885) (max r0 (max (w0Loc sc w) (w0FE w.pm))) ∧
      Rd (lookupD (f_mst x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
        (w.pw 5) (w.pw 6) (w.pw 7)) 1109) (w0Loc sc w)) ∧
    rmax_cond Vr ∧ mld_cond Vm ∧ vt_cond Vh ∧ pw_cond Vj ∧
      SK.ni.Has (lookupD (f_mst x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
        (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7)) 1109) := by
  intro V Vr Vm Vh Vj
  have hsc := hw.scale
  have hS : ∀ c < 32, SK.ni.Lane (w0Score w c) := fun c _ => w0Score_lane w c
  obtain ⟨hj0, pa0, pb0, h20, h30, h40, h50⟩ := w0b_pld0 hw x m l mx sk lo
  have st0 := w0s_sum0
    (lookupD (s_pld0 x m l mx sk lo w.hi w.mw
      (w.pw 0))) (w0A w) (w0PeerF w) hj0
    (w0A_lane w 0) (w0A_lane w 1) h20 h30 pa0 pb0
  obtain ⟨hj1, pa1, pb1, h21, h31, h41, h51⟩ := w0b_pld1 hw x m l mx sk lo
  have st1 := w0s_sum1
    (lookupD (s_pld1 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1))) (w0A w) (w0PeerF w) hj1
    (w0A_lane w 4) (w0A_lane w 5) h21 h31 pa1 pb1
  obtain ⟨hj2, pa2, pb2, h22, h32, h42, h52⟩ := w0b_pld2 hw x m l mx sk lo
  have st2 := w0s_sum2
    (lookupD (s_pld2 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1) (w.pw 2))) (w0A w) (w0PeerF w) hj2
    (w0A_lane w 8) (w0A_lane w 9) h22 h32 pa2 pb2
  obtain ⟨hj3, pa3, pb3, h23, h33, h43, h53⟩ := w0b_pld3 hw x m l mx sk lo
  have st3 := w0s_sum3
    (lookupD (s_pld3 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3))) (w0A w) (w0PeerF w) hj3
    (w0A_lane w 12) (w0A_lane w 13) h23 h33 pa3 pb3
  obtain ⟨hj4, pa4, pb4, h24, h34, h44, h54⟩ := w0b_pld4 hw x m l mx sk lo
  have st4 := w0s_sum4
    (lookupD (s_pld4 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4))) (w0A w) (w0PeerF w) hj4
    (w0A_lane w 16) (w0A_lane w 17) h24 h34 pa4 pb4
  obtain ⟨hj5, pa5, pb5, h25, h35, h45, h55⟩ := w0b_pld5 hw x m l mx sk lo
  have st5 := w0s_sum5
    (lookupD (s_pld5 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4) (w.pw 5))) (w0A w) (w0PeerF w) hj5
    (w0A_lane w 20) (w0A_lane w 21) h25 h35 pa5 pb5
  obtain ⟨hj6, pa6, pb6, h26, h36, h46, h56⟩ := w0b_pld6 hw x m l mx sk lo
  have st6 := w0s_sum6
    (lookupD (s_pld6 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4) (w.pw 5)
      (w.pw 6))) (w0A w) (w0PeerF w) hj6
    (w0A_lane w 24) (w0A_lane w 25) h26 h36 pa6 pb6
  obtain ⟨hj7, pa7, pb7, h27, h37⟩ := w0b_pld7 hw x m l mx sk lo
  have st7 := w0s_sum7
    (lookupD (s_pld7 x m l mx sk lo w.hi w.mw
      (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4) (w.pw 5)
      (w.pw 6) (w.pw 7))) (w0A w) (w0PeerF w) hj7
    (w0A_lane w 28) (w0A_lane w 29) h27 h37 pa7 pb7
  have hVp : ∀ j < 16, lookupD (f_pld8 x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw
      3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7)) (w0SumReg j) =
      w0SumV (w0Score w (2 * j)) (w0Score w (2 * j + 1)) := by
    intro j hj
    match j, hj with
    | 0, _ =>
      show lookupD _ 3242 = w0SumV (w0Score w 0) (w0Score w 1)
      rw [w0c_up0 3242 (by decide), w0c_hs0 3242 (by decide), (st0).1,
        w0A_add, w0A_add]
    | 1, _ =>
      show lookupD _ 3247 = w0SumV (w0Score w 2) (w0Score w 3)
      rw [w0c_up0 3247 (by decide), w0c_hs0 3247 (by decide), (st0).2,
        w0A_add, w0A_add]
    | 2, _ =>
      show lookupD _ 3252 = w0SumV (w0Score w 4) (w0Score w 5)
      rw [w0c_up1 3252 (by decide), w0c_hs1 3252 (by decide), (st1).1,
        w0A_add, w0A_add]
    | 3, _ =>
      show lookupD _ 3256 = w0SumV (w0Score w 6) (w0Score w 7)
      rw [w0c_up1 3256 (by decide), w0c_hs1 3256 (by decide), (st1).2,
        w0A_add, w0A_add]
    | 4, _ =>
      show lookupD _ 3260 = w0SumV (w0Score w 8) (w0Score w 9)
      rw [w0c_up2 3260 (by decide), w0c_hs2 3260 (by decide), (st2).1,
        w0A_add, w0A_add]
    | 5, _ =>
      show lookupD _ 3264 = w0SumV (w0Score w 10) (w0Score w 11)
      rw [w0c_up2 3264 (by decide), w0c_hs2 3264 (by decide), (st2).2,
        w0A_add, w0A_add]
    | 6, _ =>
      show lookupD _ 3268 = w0SumV (w0Score w 12) (w0Score w 13)
      rw [w0c_up3 3268 (by decide), w0c_hs3 3268 (by decide), (st3).1,
        w0A_add, w0A_add]
    | 7, _ =>
      show lookupD _ 3272 = w0SumV (w0Score w 14) (w0Score w 15)
      rw [w0c_up3 3272 (by decide), w0c_hs3 3272 (by decide), (st3).2,
        w0A_add, w0A_add]
    | 8, _ =>
      show lookupD _ 3276 = w0SumV (w0Score w 16) (w0Score w 17)
      rw [w0c_up4 3276 (by decide), w0c_hs4 3276 (by decide), (st4).1,
        w0A_add, w0A_add]
    | 9, _ =>
      show lookupD _ 3280 = w0SumV (w0Score w 18) (w0Score w 19)
      rw [w0c_up4 3280 (by decide), w0c_hs4 3280 (by decide), (st4).2,
        w0A_add, w0A_add]
    | 10, _ =>
      show lookupD _ 3284 = w0SumV (w0Score w 20) (w0Score w 21)
      rw [w0c_up5 3284 (by decide), w0c_hs5 3284 (by decide), (st5).1,
        w0A_add, w0A_add]
    | 11, _ =>
      show lookupD _ 3288 = w0SumV (w0Score w 22) (w0Score w 23)
      rw [w0c_up5 3288 (by decide), w0c_hs5 3288 (by decide), (st5).2,
        w0A_add, w0A_add]
    | 12, _ =>
      show lookupD _ 3292 = w0SumV (w0Score w 24) (w0Score w 25)
      rw [w0c_up6 3292 (by decide), w0c_hs6 3292 (by decide), (st6).1,
        w0A_add, w0A_add]
    | 13, _ =>
      show lookupD _ 3296 = w0SumV (w0Score w 26) (w0Score w 27)
      rw [w0c_up6 3296 (by decide), w0c_hs6 3296 (by decide), (st6).2,
        w0A_add, w0A_add]
    | 14, _ =>
      show lookupD _ 3300 = w0SumV (w0Score w 28) (w0Score w 29)
      rw [w0c_up7 3300 (by decide), w0c_hs7 3300 (by decide), (st7).1,
        w0A_add, w0A_add]
    | 15, _ =>
      show lookupD _ 3304 = w0SumV (w0Score w 30) (w0Score w 31)
      rw [w0c_up7 3304 (by decide), w0c_hs7 3304 (by decide), (st7).2,
        w0A_add, w0A_add]
    | _ + 16, h => exact absurd h (by omega)
  have h467 : readEReal .f32 (lookupD (f_pld8 x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7)) 467) = some (.ok (sc : EReal)) := by
    rw [w0c_sc_p8 467 (by decide), w0c_vm_car x m l mx sk lo w.hi w.mw 467 (by decide),
      w0c_car_467]
    exact rd_read hx
  have hr := w0r_rmax (lookupD (f_pld8 x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw
      3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7))) (w0Score w) sc hsc h467 hVp hS
  have h1109 : Rd (lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 1109)
      ((sc : EReal) * (Finset.range 32).sup (w0Score w)) := by
    rw [w0c_sn_mld 1109 (by decide)]
    unfold f_mst
    rw [lk_head_mem (by simp only [rmax_facts2, List.map_cons, List.map_nil]; decide)]
    exact hr.1
  have h1110 : Rd (lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 1110) (w0FE w.pm) := by
    rw [w0c_hd_mld]; exact w0_rd_pm hw
  have hmxr : Rd (lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 2885) r0 := by
    rw [w0c_sc_mld 2885 (by decide), w0c_vm_car x m l mx sk lo w.hi w.mw 2885 (by decide),
      w0c_car_2885]
    exact hmx
  have mld := w0v_mld (lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)) h1109 h1110 hmxr
  have h479 : Rd (lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw
      4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 479)
      (max ((sc : EReal) * (Finset.range 32).sup (w0Score w)) (w0FE w.pm)) := by
    rw [w0c_fr_vh 479 (by decide)]
    unfold f_vote
    rw [lk_head_mem (by simp only [mld_facts1, List.map_cons, List.map_nil]; decide)]
    exact mld.1
  have h2950 : Rd (lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 2950) (mR : EReal) := by
    rw [w0c_sc_vh 2950 (by decide), w0c_vm_car x m l mx sk lo w.hi w.mw 2950 (by decide),
      w0c_car_2950]
    exact hm
  have h2951 : lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
      (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 2951 = .bits 32 (BitVec.ofNat 64 1065353216) := by
    unfold f_vh
    simp [lookupD, List.lookup]
  have jn := w0v_join (lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)) w.vt h479 h2950 h2951
  have hmax : (if w.vt then w0Moved (max ((sc : EReal) * (Finset.range 32).sup (w0Score w))
      (w0FE w.pm)) mR else mR) = w0Max sc mR w := rfl
  rw [hmax] at jn
  have e2950 : lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw
      4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 2950 =
      if w.vt then vt_v585 (lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2)
          (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)) else lookupD (f_vh x m l mx sk lo
          w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)
          2950 := by
    dsimp only [f_join]
    exact lk_head (by simp [List.lookup])
  have e2951 : lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw
      4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 2951 =
      if w.vt then vt_v584 (lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2)
          (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)) else lookupD (f_vh x m l mx sk lo
          w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)
          2951 := by
    dsimp only [f_join]
    exact lk_head (by simp [List.lookup])
  have hVj : ∀ j < 16, lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw
      3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) (w0SumReg j) =
      w0SumV (w0Score w (2 * j)) (w0Score w (2 * j + 1)) := by
    intro j hj
    rw [w0c_su_join (w0SumReg j) (by revert hj; revert j; decide)]
    exact hVp j hj
  have h3243 : pairRead (lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw
      3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 3243) =
      some (.ok ((sc : EReal), (sc : EReal))) := by
    rw [w0c_sc_join 3243 (by decide), w0c_vm_car x m l mx sk lo w.hi w.mw 3243 (by decide),
      w0c_car_3243]
    exact w0c_scPair hx
  have h2955 : readEReal .f32 (lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2)
      (w.pw 3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 2955) = some (.ok (lR : EReal)) :=
      by
    rw [w0c_sc_join 2955 (by decide), w0c_vm_car x m l mx sk lo w.hi w.mw 2955 (by decide),
      w0c_car_2955]
    exact rd_read hl
  have hP := w0p_block (lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw
      3) (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)) (w0Score w) sc (w0Max sc mR w) lR
    ((2 : ℝ) ^ (mR - w0Max sc mR w)) hsc hS hVj h3243 (by rw [e2950]; exact jn.1)
    (by rw [e2951]; exact jn.2) h2955
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show Rd (lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
      (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 2950) _
    unfold f_ost
    rw [lk_frame (K := w0KeepOst) (r := 2950) (by decide)
      (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide) (by decide)]
    rw [e2950]; exact jn.1
  · show Rd (lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
      (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 2955) _
    unfold f_ost
    rw [lk_head_mem (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide)]
    exact hP.2
  · intro t ht
    show lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
        (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) (1115 + 3 * t) = _
    unfold f_ost
    rw [lk_head_mem (by
      simp only [pw_facts4, List.map_cons, List.map_nil]
      revert ht; revert t; decide)]
    exact hP.1 t ht
  · show Rd (lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
        (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt) 2885) (max r0 (max (w0Loc sc w) (w0FE w.pm)))
    unfold f_ost
    rw [lk_frame (K := w0KeepOst) (r := 2885) (by decide)
      (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide) (by decide)]
    rw [w0c_fr_join 2885 (by decide), w0c_fr_vh 2885 (by decide)]
    unfold f_vote
    rw [lk_head_mem (by simp only [mld_facts1, List.map_cons, List.map_nil]; decide)]
    exact mld.2
  · unfold f_mst
    rw [lk_head_mem (by simp only [rmax_facts2, List.map_cons, List.map_nil]; decide)]
    exact hr.1
  · exact rmax_cond_of_reads _ (w0Score w) sc hsc h467 hVp hS
  · have h2950s : Rd (Vm 2950) (mR : EReal) := by
      show Rd (lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
        (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm) 2950) _
      rw [w0c_sc_mld 2950 (by decide), w0c_vm_car x m l mx sk lo w.hi w.mw 2950 (by decide),
        w0c_car_2950]
      exact hm
    exact mld_cond_of_reads _ h1109 h1110 hmxr h2950s
  · exact vt_cond_of_reads _ h479 h2950
  · exact pw_cond_of_reads _ (w0Score w) sc (w0Max sc mR w) lR ((2 : ℝ) ^ (mR - w0Max sc mR w))
      hsc hS hVj h3243 (by simp only [Vj]; rw [e2950]; exact jn.1)
      (by simp only [Vj]; rw [e2951]; exact jn.2) h2955
  · unfold f_mst
    rw [lk_head_mem (by simp only [rmax_facts2, List.map_cons, List.map_nil]; decide)]
    exact hr.2

/-- The block's statistics read as numbers (without the kind of the row maximum). -/
theorem w0_block_full {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {m l mx sk : Value} {lo : List Value} {mR lR : ℝ}
    (hm : Rd m (mR : EReal)) (hl : Rd l (lR : EReal)) {r0 : EReal} (hmx : Rd mx r0) :
    let V := lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
      (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)
    let Vr := lookupD (f_pld8 x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7))
    let Vm := lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)
    let Vh := lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)
    let Vj := lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)
    (Rd (V 2950) ((w0Max sc mR w : ℝ) : EReal) ∧
      Rd (V 2955) (((w0Next sc (mR, lR) w).2 : ℝ) : EReal) ∧
      (∀ t < 16, V (1115 + 3 * t) =
        Assumptions.bf16Pair (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t)))
          (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t + 1)))) ∧
      Rd (V 2885) (max r0 (max (w0Loc sc w) (w0FE w.pm))) ∧
      Rd (lookupD (f_mst x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
        (w.pw 5) (w.pw 6) (w.pw 7)) 1109) (w0Loc sc w)) ∧
    rmax_cond Vr ∧ mld_cond Vm ∧ vt_cond Vh ∧ pw_cond Vj := by
  intro V Vr Vm Vh Vj
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9, -⟩ := w0_block_full_has hw hx hm hl hmx
  exact ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
