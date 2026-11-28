-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumVote
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Vote
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumChain2
import Lemmas.Flow.SetpReads

@[expose] public section

/-! # The predicate the vote takes

At the vote (pc 578) the register of the predicate (`%p109`) holds `w0VoteArg`: the words of the
block's loads, as `w0_block_mst` and the peer's word give the maxima, and the carried maximum. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- The register of the predicate, from the readings of the three words it uses. -/
theorem w0_vote_of_reads (V : Nat → Value) {loc pm : EReal} {mR : ℝ} (h1 : Rd (V 1109) loc)
    (h2 : Rd (V 1110) pm) (h3 : Rd (V 2950) (mR : EReal)) :
    lookupD (mld_facts1 V) 109 =
      .pred (erealCompare .gt (max loc pm + -(mR : EReal)) ((6 : ℝ) : EReal)) := by
  have h479 : Rd (mld_v573 V) (max loc pm) := w0r_max (by decide) h1 h2
  have hl : SK.ni.Lane (max loc pm) := rd_lane h479
  have hz : addEReal (max loc pm) (-(mR : EReal)) = some (max loc pm + -(mR : EReal)) := by
    have hn : ¬ ((max loc pm = ⊤ ∧ -(mR : EReal) = ⊥) ∨ (max loc pm = ⊥ ∧ -(mR : EReal) = ⊤)) := by
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact absurd h (by simp)
    simp only [addEReal, hn, ↓reduceIte]
  have hne : max loc pm + -(mR : EReal) ≠ ⊤ := by
    rcases hl with ⟨r, hr⟩ | hr <;> rw [hr] <;> simp [← EReal.coe_neg, ← EReal.coe_add]
  have hsub : subE true (mld_v573 V) (V 2950) =
      .ok (erealValue .f32 (max loc pm + -(mR : EReal))) :=
    subE_reads (rd_read h479) (rd_read h3) hz
  have hset := setpE_reads (c := .ord .gt) (fz := true) (Or.inl rfl)
    (x := max loc pm + -(mR : EReal)) (y := ((6 : ℝ) : EReal))
    (va := erealValue .f32 (max loc pm + -(mR : EReal)))
    (vb := .bits 32 (BitVec.ofNat 64 1086324736)) (readEReal_erealValue hne)
    (readEReal_of_valFloat valFloat_six)
  have hok : ∀ v, okVal (.bits 32 0) (Except.ok v) = v := fun _ => rfl
  simp only [mld_facts1, lookupD, List.lookup, beq_self_eq_true, mld_v576, mld_v575, hsub,
    hok, hset, okPred, Option.getD_some]

/-- **The vote's register** (`%p109`, id 109) is the predicate `w0VoteArg`. -/
theorem w0_vote_pred {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {b : Blk} (hhi : b.hi = w.hi) (hmw : b.mw = w.mw)
    (hpw : ∀ j, b.pw j = w.pw j) (hpm : b.pm = w.pm) {mR lR : ℝ} (hm : Rd b.m (mR : EReal))
    (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    lookupD (f_vote x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3)
      (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 109 = .pred (w0VoteArg sc w mR) := by
  have h1 : Rd (lookupD (s_mld x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 1109) (w0Loc sc w) := by
    rw [w0c_sn_mld 1109 (by decide)]
    exact w0_block_mst hw hx hhi hmw hpw hm hl hmx
  have h2 : Rd (lookupD (s_mld x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 1110) (w0FE w.pm) := by
    rw [w0c_hd_mld, hpm]; exact w0_rd_pm hw
  have h3 : Rd (lookupD (s_mld x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 2950) (mR : EReal) := by
    rw [w0c_sc_mld 2950 (by decide), w0c_vm_car _ _ _ _ _ _ _ _ 2950 (by decide), w0c_car_2950]
    exact hm
  unfold f_vote
  rw [lk_head_mem (by simp only [mld_facts1, List.map_cons, List.map_nil]; decide)]
  exact w0_vote_of_reads _ h1 h2 h3

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
