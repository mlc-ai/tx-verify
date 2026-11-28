-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

theorem k_byteLoc {sp : TcMma.OperandSpec} (hD : sp.descriptor = qkDesc) {st : Nat}
    (hs : sp.b = ⟨st, 0, 1024, 0, false, false, .b128⟩) {r k z : Nat} (hr : r < 128)
    (hk : k < 16) (hz : z < 2) :
    sp.byteLoc .b (32 * r + 2 * k + z) =
      some ⟨.shared, sp.lowCta, TensorSwizzle.offset .b128 0 (st + 128 * r + 2 * k + z)⟩ := by
  have hdiv : (32 * r + 2 * k + z) / (16 * 2) = r := by omega
  have hkdiv : (32 * r + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * r + 2 * k + z) % 2 = z := by omega
  have hlocal : r % (128 / 1) = r := by omega
  have hv := qkDesc_valid
  have hadr : TcShared.byteAddress 2 .k ⟨st, 0, 1024, 0, false, false, .b128⟩ r k z =
      some (TensorSwizzle.offset .b128 0 (st + 128 * r + 2 * k + z)) := by
    simp only [TcShared.byteAddress, TcShared.Swizzle.offset]
    rw [TcShared.linear_k128 2 _ r k rfl]
    simp only [hz, reduceCtorEq, ne_eq, not_false_eq_true, imp_self, and_self,
      ↓reduceIte, Option.some.injEq, IsEmpty.forall_iff]
    congr 1
    omega
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkDesc, TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.extent, CtaGroup.size,
    hdiv, TcMma.Operand.major, hlocal, hkdiv, hbmod, hs] at hv ⊢
  simp [hv, hr, hadr]

/-- **The byte of a PV step's B operand**: row `n`, contraction `k < 16`, byte `z` of the
MN-major, 128-byte-swizzled operand at start `st` with leading offset 16384. -/
theorem v_byteLoc {sp : TcMma.OperandSpec} (hD : sp.descriptor = pvDesc) {st : Nat}
    (hs : sp.b = ⟨st, 16384, 1024, 0, false, false, .b128⟩) {n k z : Nat} (hn : n < 128)
    (hk : k < 16) (hz : z < 2) :
    sp.byteLoc .b (32 * n + 2 * k + z) =
      some ⟨.shared, sp.lowCta, TensorSwizzle.offset .b128 0
        (st + 16384 * (n / 64) + 2 * (n % 64) + 128 * k + z)⟩ := by
  have hdiv : (32 * n + 2 * k + z) / (16 * 2) = n := by omega
  have hkdiv : (32 * n + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * n + 2 * k + z) % 2 = z := by omega
  have hlocal : n % (128 / 1) = n := by omega
  have hv := pvDesc_valid
  have hadr : TcShared.byteAddress 2 .mn ⟨st, 16384, 1024, 0, false, false, .b128⟩ n k z =
      some (TensorSwizzle.offset .b128 0 (st + 16384 * (n / 64) + 2 * (n % 64) + 128 * k + z)) := by
    simp only [TcShared.byteAddress, TcShared.Swizzle.offset, TcShared.linear,
      TcShared.Swizzle.sectors, reduceCtorEq, ↓reduceIte, Nat.reduceDiv, Nat.reduceMul]
    split
    · congr 2
      omega
    · rename_i hc
      exact absurd (by simp [hz]) hc
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvDesc, TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.extent, CtaGroup.size,
    hdiv, TcMma.Operand.major, hlocal, hkdiv, hbmod, hs] at hv ⊢
  simp [hv, hn, hadr]

/-- **A byte of a K region** `[B, B + 32768)` is the B operand byte of a QK step `j`, whose
operand starts at `B + 16384 (j / 4) + 32 (j % 4)`. -/
theorem k_cover {B a : Nat} (hB : B % 128 = 0) (ha : a < 32768) :
    ∃ j : Fin 8, ∃ idx, ∀ sp : TcMma.OperandSpec, sp.descriptor = qkDesc →
      sp.b = ⟨B + 16384 * (j / 4) + 32 * (j % 4), 0, 1024, 0, false, false, .b128⟩ →
      sp.byteLoc .b idx = some ⟨.shared, sp.lowCta, B + a⟩ := by
  have hrow := TensorSwizzle.offset_row .b128 0 (B + a)
  have hinv := TensorSwizzle.offset_involutive .b128 0 (B + a)
  generalize TensorSwizzle.offset .b128 0 (B + a) = A' at hrow hinv
  refine ⟨⟨4 * ((A' - B) / 16384) + (A' - B) % 128 / 32, by omega⟩,
    32 * ((A' - B) % 16384 / 128) + 2 * ((A' - B) % 32 / 2) + (A' - B) % 2,
    fun sp hD hs => ?_⟩
  rw [k_byteLoc hD hs (by omega) (by omega) (by omega)]
  have he : B + 16384 * ((4 * ((A' - B) / 16384) + (A' - B) % 128 / 32) / 4) +
      32 * ((4 * ((A' - B) / 16384) + (A' - B) % 128 / 32) % 4) +
      128 * ((A' - B) % 16384 / 128) + 2 * ((A' - B) % 32 / 2) + (A' - B) % 2 = A' := by
    omega
  simp only [he, hinv]

/-- **A byte of a V region** `[B, B + 32768)` is the B operand byte of a PV step `j`, whose
operand starts at `B + 2048 j`. -/
theorem v_cover {B a : Nat} (hB : B % 128 = 0) (ha : a < 32768) :
    ∃ j : Fin 8, ∃ idx, ∀ sp : TcMma.OperandSpec, sp.descriptor = pvDesc →
      sp.b = ⟨B + 2048 * j, 16384, 1024, 0, false, false, .b128⟩ →
      sp.byteLoc .b idx = some ⟨.shared, sp.lowCta, B + a⟩ := by
  have hrow := TensorSwizzle.offset_row .b128 0 (B + a)
  have hinv := TensorSwizzle.offset_involutive .b128 0 (B + a)
  generalize TensorSwizzle.offset .b128 0 (B + a) = A' at hrow hinv
  refine ⟨⟨(A' - B) % 16384 / 2048, by omega⟩,
    32 * (64 * ((A' - B) / 16384) + (A' - B) % 128 / 2) + 2 * ((A' - B) % 2048 / 128) +
      (A' - B) % 2, fun sp hD hs => ?_⟩
  rw [v_byteLoc hD hs (by omega) (by omega) (by omega)]
  have he : B + 2048 * ((A' - B) % 16384 / 2048) +
      16384 * ((64 * ((A' - B) / 16384) + (A' - B) % 128 / 2) / 64) +
      2 * ((64 * ((A' - B) / 16384) + (A' - B) % 128 / 2) % 64) +
      128 * ((A' - B) % 2048 / 128) + (A' - B) % 2 = A' := by
    omega
  simp only [he, hinv]


/-- An MMA's operand byte at a location covers it. -/
theorem covers_of_byteLoc {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {isB : Bool} {idx : Nat} {l : Loc} (hi : X.MmaIssue i d s acc mask)
    (hl : s.byteLoc (if isB then .b else .a) idx = some l) :
    AsyncCovers X i (.mmaRead isB idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, .inl ⟨d, s, acc, mask, hi, hl⟩⟩,
    ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
