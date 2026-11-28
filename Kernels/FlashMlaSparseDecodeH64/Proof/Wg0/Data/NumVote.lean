-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumRow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Vote
public import Lemmas.Flow.Recip

@[expose] public section

/-! # The peer maximum, the vote and the lazy maximum against the extended reals

`mld` (pcs 573-577) takes the maximum `r21` of the lane's scaled maximum and the peer's, and of the
true running maximum. The vote (pc 578) is the control's; if it voted, `vt` (pcs 582-585) moves
the maximum to `max r21 m` and the rescale factor to `2 ^ (m - m')`; otherwise the maximum stays
and the factor is `1.0` (`Gen.DataFacts.f_vh`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

/-- The maximum after the vote moved it: the real `max r21 m`. -/
def w0Moved (r21 : EReal) (m : ℝ) : ℝ := (max r21 (m : EReal)).toReal

theorem w0Moved_eq {r21 : EReal} (h : SK.ni.Lane r21) (m : ℝ) :
    max r21 (m : EReal) = (w0Moved r21 m : EReal) := by
  rcases h with ⟨r, rfl⟩ | rfl
  · rw [coe_max]; simp [w0Moved, coe_max]
  · rw [max_eq_right bot_le]; simp [w0Moved]

/-- `sub.ftz.f32` of two words that read as reals is the real difference. -/
theorem w0v_sub {va vb : Value} {a b : ℝ} (ha : readEReal .f32 va = some (.ok (a : EReal)))
    (hb : readEReal .f32 vb = some (.ok (b : EReal))) :
    subE true va vb = .ok (.float .f32 (a - b)) := by
  rw [subE_reads ha hb (z := ((a - b : ℝ) : EReal)) (by
    rw [← EReal.coe_neg, addEReal_coe, sub_eq_add_neg])]
  rw [erealValue_coe]

/-- **The peer maximum** (`mld`): `r21` reads as the maximum of the lane's and the peer's; the true
running maximum stays a lane. -/
theorem w0v_mld (V : Nat → Value) {loc pm mx : EReal} (h1 : Rd (V 1109) loc) (h2 : Rd (V 1110) pm)
    (h3 : Rd (V 2885) mx) :
    Rd (lookupD (mld_facts1 V) 479) (max loc pm) ∧
      Rd (lookupD (mld_facts1 V) 2885) (max mx (max loc pm)) := by
  have h479 : Rd (mld_v573 V) (max loc pm) := w0r_max (by decide) h1 h2
  exact ⟨h479, w0r_max (r1 := 2885) (r2 := 479) (by decide) h3 h479⟩

/-- **The lazy maximum** (`vt` and `f_join`): with the vote the maximum is `max r21 m` and the
factor `2 ^ (m - m')`, without it `m` and `1`. -/
theorem w0v_join (Vh : Nat → Value) {r21 : EReal} {m : ℝ} (vt : Bool) (h479 : Rd (Vh 479) r21)
    (h2950 : Rd (Vh 2950) (m : EReal))
    (h2951 : Vh 2951 = .bits 32 (BitVec.ofNat 64 1065353216)) :
    Rd (if vt then vt_v585 Vh else Vh 2950) ((if vt then w0Moved r21 m else m : ℝ) : EReal) ∧
      readEReal .f32 (if vt then vt_v584 Vh else Vh 2951) =
        some (.ok (((2 : ℝ) ^ (m - (if vt then w0Moved r21 m else m) : ℝ) : ℝ) : EReal)) := by
  have hl : SK.ni.Lane r21 := rd_lane h479
  have hmax : Rd (vt_v582 Vh) (max r21 (m : EReal)) := w0r_max (by decide) h479 h2950
  rw [w0Moved_eq hl] at hmax
  cases vt
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_self]
    refine ⟨h2950, ?_⟩
    rw [h2951, readEReal_of_valFloat valFloat_one]
    simp
  · simp only [↓reduceIte]
    refine ⟨hmax, ?_⟩
    have e : vt_v583 Vh = .float .f32 (m - w0Moved r21 m) :=
      okVal_ok (w0v_sub (rd_read h2950) (rd_read hmax))
    have e2 : vt_v584 Vh = .float .f32 (Real.rpow 2 (m - w0Moved r21 m)) :=
      okVal_ok (by rw [e]; exact ex2E_real (readEReal_float _))
    rw [e2, readEReal_float]
    rfl

/-- `0f40C00000` reads as `6`. -/
theorem valFloat_six : valFloat .f32 (.bits 32 (BitVec.ofNat 64 1086324736)) = .ok 6 := by
  have h : f32Value 1086324736 = some (6 : ℚ) := by decide +kernel
  have := valFloat_b32 (b := 1086324736) (by norm_num) h
  simpa [b32] using this

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
