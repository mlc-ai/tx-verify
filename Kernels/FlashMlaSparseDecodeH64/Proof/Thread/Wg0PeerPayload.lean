-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputNumeric

@[expose] public section

/-! # Reassemble the softmax peer exchange payload -/

open PTX PTX.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

noncomputable section

private theorem halfBytes {v : Value} (h : Assumptions.scoreHalf v) :
    v.toBytes = [(v, 0), (v, 1), (v, 2), (v, 3)] := by
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  cases v with
  | bits w x =>
    have hw : w = 32 := by
      unfold Assumptions.scoreHalf at h
      split at h <;> simp_all
    subst w
    simp [Value.toBytes, Value.bytes, Value.byteAt, hr]
  | float fmt x =>
    have hf : fmt = .f32 := by cases fmt <;> simp_all [Assumptions.scoreHalf]
    subst fmt
    simp [Value.toBytes, Value.bytes, Value.byteAt, FloatFmt.bytes, hr]
  | _ => simp [Assumptions.scoreHalf] at h

private theorem pair_toBytes {a b : Value} :
    (Value.pair a b).toBytes = a.toBytes ++ b.toBytes := by
  apply List.ext_getElem?
  intro k
  have ha : a.toBytes.length = a.bytes := by simp [Value.toBytes]
  have hb : b.toBytes.length = b.bytes := by simp [Value.toBytes]
  by_cases hk : k < a.bytes
  · rw [List.getElem?_append_left (by omega)]
    simp [Value.toBytes, Value.bytes, Value.byteAt, hk,
      show k < a.bytes + b.bytes by omega]
  · rw [List.getElem?_append_right (by omega), ha]
    by_cases hkb : k < a.bytes + b.bytes
    · simp [Value.toBytes, Value.bytes, Value.byteAt, hk, hkb,
        show k - a.bytes < b.bytes by omega]
    · simp [Value.toBytes, Value.bytes, Value.byteAt, hkb,
        show ¬ k - a.bytes < b.bytes by omega]

private theorem rebuildIntPair (x y : BitVec 64)
    (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    rebuild 3 (((Value.bits 32 x).toBytes ++ (Value.bits 32 y).toBytes).map some) =
      .ok (joinValue (.bits 32 x) (.bits 32 y)) := by
  rw [halfBytes (v := .bits 32 x) hx, halfBytes (v := .bits 32 y) hy]
  change rebuild 3 [some (.bits 32 x, 0), some (.bits 32 x, 1),
    some (.bits 32 x, 2), some (.bits 32 x, 3), some (.bits 32 y, 0),
    some (.bits 32 y, 1), some (.bits 32 y, 2), some (.bits 32 y, 3)] = _
  rw [rebuild.eq_2, rebuild.halves.eq_def]
  simp [rebuildBits, intByte, littleEndianBits, byteBits, Value.bytes, Value.bitPattern,
    joinValue, bind, Option.bind, pure, Except.pure]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hyShift : (y.toNat * 2 ^ 32) % 2 ^ 64 = y.toNat * 2 ^ 32 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hyShift, Nat.or_comm x.toNat, Nat.mul_comm y.toNat,
    ← Nat.two_pow_add_eq_or_of_lt hx]
  rw [BitVec.toNat_ofNat]
  omega

private theorem scalar_rebuild {v : Value} (h : Assumptions.scoreHalf v) :
    rebuild 2 (v.toBytes.map some) = .ok v := by
  rw [halfBytes h]
  simp [rebuild.eq_2, Assumptions.scoreHalf_bytes h, halfBytes h, pure, Except.pure]

private theorem scoreHalf_cases {v : Value} (h : Assumptions.scoreHalf v) :
    (∃ x, v = .float .f32 x) ∨ (∃ x : BitVec 64, v = .bits 32 x ∧ x.toNat < 2 ^ 32) := by
  unfold Assumptions.scoreHalf at h
  split at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl, h⟩
  · exact h.elim

private theorem rebuildMixedPair {lo hi : Value}
    (hlo : Assumptions.scoreHalf lo) (hhi : Assumptions.scoreHalf hi)
    (hfloat : (∃ x, lo = .float .f32 x) ∨ ∃ y, hi = .float .f32 y) :
    rebuild 3 ((lo.toBytes ++ hi.toBytes).map some) = .ok (joinValue lo hi) := by
  have hlen : ((lo.toBytes ++ hi.toBytes).map some).length = 8 := by
    simp [List.length_append, Value.toBytes, Assumptions.scoreHalf_bytes hlo,
      Assumptions.scoreHalf_bytes hhi]
  have hlenLo : (lo.toBytes.map some).length = 4 := by
    simp [Value.toBytes, Assumptions.scoreHalf_bytes hlo]
  have hTake : ((lo.toBytes ++ hi.toBytes).map some).take 4 = lo.toBytes.map some := by
    rw [List.map_append]
    exact List.take_left' hlenLo
  have hDrop : ((lo.toBytes ++ hi.toBytes).map some).drop 4 = hi.toBytes.map some := by
    rw [List.map_append, ← hlenLo, List.drop_left]
  have hAll : ((lo.toBytes ++ hi.toBytes).map some).all intByte = false := by
    rw [halfBytes hlo, halfBytes hhi]
    rcases hfloat with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;> simp [intByte]
  have hJoin : joinValue lo hi = .pair lo hi := by
    rcases hfloat with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rfl
    · rcases scoreHalf_cases hlo with ⟨x, rfl⟩ | ⟨x, rfl, _⟩ <;> rfl
  have hOuter : rebuild 3 ((lo.toBytes ++ hi.toBytes).map some) =
      rebuild.halves 2 ((lo.toBytes ++ hi.toBytes).map some) := by
    rw [halfBytes hlo]
    simp [rebuild.eq_2, Assumptions.scoreHalf_bytes hlo, halfBytes hhi]
  have hSome : none ∉ ((lo.toBytes ++ hi.toBytes).map some) := by simp
  rw [hOuter, rebuild.halves.eq_def, ite_eq_right hSome]
  rw [hAll, hlen, ite_eq_right (by decide : ¬ (false = true ∨ 2 = 0 ∨ ¬(2 ≤ 8 ∧ 8 % 2 = 0)))]
  change (do
    let l ← rebuild 2 (((lo.toBytes ++ hi.toBytes).map some).take 4)
    let r ← rebuild 2 (((lo.toBytes ++ hi.toBytes).map some).drop 4)
    pure (Value.pair l r) : Exec Value) = _
  rw [hTake, hDrop, scalar_rebuild hlo, scalar_rebuild hhi, hJoin]
  rfl

private theorem rebuildScorePair {lo hi : Value}
    (hlo : Assumptions.scoreHalf lo) (hhi : Assumptions.scoreHalf hi) :
    rebuild 3 ((lo.toBytes ++ hi.toBytes).map some) = .ok (joinValue lo hi) := by
  rcases scoreHalf_cases hlo with h | ⟨x, rfl, hx⟩
  · exact rebuildMixedPair hlo hhi (.inl h)
  rcases scoreHalf_cases hhi with h | ⟨y, rfl, hy⟩
  · exact rebuildMixedPair hlo hhi (.inr h)
  exact rebuildIntPair x y hx hy

/-- The two four-byte scores loaded by one half of the peer vector read. -/
def peerReadValue (q : D) (group sub : Nat) : Value :=
  joinValue (q.peerScores.getD (4 * group + 2 * sub) (b32 0))
    (q.peerScores.getD (4 * group + 2 * sub + 1) (b32 0))

/-- Splitting the assembled word recovers its two original score values. -/
theorem split_peerReadValue {q : D} (hq : exchangeReady q = true) (group sub : Nat) :
    splitValue 64 (peerReadValue q group sub) =
      (q.peerScores.getD (4 * group + 2 * sub) (b32 0),
        q.peerScores.getD (4 * group + 2 * sub + 1) (b32 0)) := by
  have hs := (Bool.and_eq_true_iff.mp hq).2
  exact split_join_words (scoreHalf_getD hs _) (scoreHalf_getD hs _)

/-- Rebuilding either eight-byte half of the shared exchange store preserves the two scores. -/
theorem rebuild_exchange_slice {q : D} (hq : exchangeReady q = true) (group sub : Nat)
    (hsub : sub < 2) :
    rebuild 3 ((((exchangeValue q group).toBytes.drop (8 * sub)).take 8).map some) =
      .ok (peerReadValue q group sub) := by
  let w j := q.peerScores.getD (4 * group + j) (b32 0)
  have hs (j : Nat) : Assumptions.scoreHalf (w j) :=
    scoreHalf_getD (Bool.and_eq_true_iff.mp hq).2 _
  have hlen (a b : Nat) : ((w a).toBytes ++ (w b).toBytes).length = 8 := by
    simp [List.length_append, Value.toBytes, Assumptions.scoreHalf_bytes (hs a),
      Assumptions.scoreHalf_bytes (hs b)]
  change rebuild 3 (((((.pair (.pair (w 0) (w 1)) (.pair (w 2) (w 3)) : Value).toBytes).drop
    (8 * sub)).take 8).map some) = _
  rw [pair_toBytes, pair_toBytes, pair_toBytes]
  have hs' : sub = 0 ∨ sub = 1 := by omega
  rcases hs' with rfl | rfl
  · rw [Nat.mul_zero, List.drop_zero, List.take_left' (hlen 0 1)]
    exact rebuildScorePair (hs 0) (hs 1)
  · rw [Nat.mul_one, ← hlen 0 1, List.drop_left, hlen,
      show List.take 8 ((w 2).toBytes ++ (w 3).toBytes) =
        (w 2).toBytes ++ (w 3).toBytes from List.take_of_length_le (by rw [hlen])]
    exact rebuildScorePair (hs 2) (hs 3)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
