-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.MmaFoot

@[expose] public section

/-!
# Every byte of a KV ring slot is an MMA step's B operand byte

The inverse of `Ring.Foot.qk_b_foot` and `Ring.Foot.pv_b_foot`. The absolute 128-byte swizzle
(`TcShared.Swizzle.offset .b128`, the TMA swizzle with base 0) is an involution that keeps a byte's
128-byte row (`TensorSwizzle.offset_involutive`, `offset_row`), so a byte `A` of a slot is the
swizzle image of the unswizzled address `A' = offset A`, in the same row:

* `k_cover`: a byte of the K region `[B, B + 32768)` of a slot is read by QK step `j` with
  `j / 4` the 16384-byte half of `A' - B` and `j % 4` the 32-byte column chunk of its row, at
  B-operand row `(A' - B) % 16384 / 128` (`k_byteLoc`: the K-major address of row `r`,
  contraction `k`, byte `z` at start `st` is `offset (st + 128 r + 2 k + z)`);
* `v_cover`: a byte of the V region `[B, B + 32768)` is read by PV step `j` with `16 j + k` the
  128-byte row of `(A' - B) % 16384` and B-operand row `n = 64 h + col / 2` (`v_byteLoc`: the
  MN-major address of row `n`, contraction `k`, byte `z` at start `st` with leading offset 16384
  is `offset (st + 16384 (n / 64) + 2 (n % 64) + 128 k + z)` for `k < 16`).

The step starts are those of the descriptors the MMA warp builds (`mma_foot`): QK step `j` of slot
`s` starts at `sharedBase + 32768 s + 16384 (j / 4) + 32 (j % 4)`, PV step `j` at
`sharedBase + 98304 + 32768 s + 2048 j`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Cover
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc qkDesc_valid pvDesc_valid)

noncomputable section

/-- **The byte of a QK step's B operand**: row `r`, contraction `k`, byte `z` of the K-major,
128-byte-swizzled operand at start `st`. -/
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


/-! ### The operands of the steps (moved from the first tree's `Protocol/SxKRing.lean`) -/

section Steps
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape mmEnv_of_pre)

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- An MMA's operand byte at a location covers it. -/
theorem covers_of_byteLoc {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {isB : Bool} {idx : Nat} {l : Loc} (hi : X.MmaIssue i d s acc mask)
    (hl : s.byteLoc (if isB then .b else .a) idx = some l) :
    AsyncCovers X i (.mmaRead isB idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, .inl ⟨d, s, acc, mask, hi, hl⟩⟩,
    ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩⟩

/-! ### The operands of the steps -/

/-- **The event of QK step `j`** is an MMA whose B operand is the K-major operand of slot
`i % 3` at `sharedBase + 32768 (i % 3) + 16384 (j / 4) + 32 (j % 4)`. -/
theorem qk_spec (hpre : Pre Q L mem0) {d : Mma.D} {j : Fin 8} {e : Event} (hs : d.site = .qk j)
    (hsh : MmShape L g d e) :
    ∃ pc dst sp acc mask, e = ⟨pc, .tc (.mma dst sp acc mask)⟩ ∧ sp.descriptor = qkDesc ∧
      sp.lowCta = g / L.block ∧
      sp.b = ⟨L.sharedBase + 32768 * (d.i % 3) + 16384 * (j / 4) + 32 * (j % 4), 0, 1024, 0,
        false, false, .b128⟩ := by
  have hE := mmEnv_of_pre hpre
  have hal := hE.align
  unfold MmShape at hsh
  rw [hs] at hsh
  obtain ⟨da, db, dsc, hdsc, -, hdb, hev⟩ := hsh
  have hj8 : (j : Nat) < 8 := j.isLt
  have hdb' := Ring.Foot.decode_k (Ring.lo_lt_k hE (d.i % 3) j (Nat.mod_lt _ (by omega)) hj8)
  have hdbe := Option.some.inj (hdb.symm.trans hdb')
  subst hdbe hev
  have hdsc' := Ring.Foot.qkDesc_eq hdsc
  subst hdsc'
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, ?_⟩
  have hstart : (Mma.kLo L (d.i % 3) + 2 * (↑j % 4) + 1024 * (↑j / 4)) * 16 =
      L.sharedBase + 32768 * (d.i % 3) + 16384 * (↑j / 4) + 32 * (↑j % 4) := by
    unfold Mma.kLo
    omega
  simp only [hstart]

/-- **The event of PV step `j`** is an MMA whose B operand is the MN-major operand of slot
`(i - 1) % 3` at `sharedBase + 98304 + 32768 ((i - 1) % 3) + 2048 j`. -/
theorem pv_spec (hpre : Pre Q L mem0) {d : Mma.D} {j : Fin 8} {e : Event} (hs : d.site = .pv j)
    (hsh : MmShape L g d e) :
    ∃ pc dst sp acc mask, e = ⟨pc, .tc (.mma dst sp acc mask)⟩ ∧ sp.descriptor = pvDesc ∧
      sp.lowCta = g / L.block ∧
      sp.b = ⟨L.sharedBase + 98304 + 32768 * ((d.i - 1) % 3) + 2048 * j, 16384, 1024, 0,
        false, false, .b128⟩ := by
  have hE := mmEnv_of_pre hpre
  have hal := hE.align
  unfold MmShape at hsh
  rw [hs] at hsh
  obtain ⟨db, dsc, hdsc, hdb, hev⟩ := hsh
  have hj8 : (j : Nat) < 8 := j.isLt
  have hdb' := Ring.Foot.decode_v (Ring.lo_lt_v hE ((d.i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj8)
  have hdbe := Option.some.inj (hdb.symm.trans hdb')
  subst hdbe hev
  have hdsc' := Ring.Foot.pvDesc_eq hdsc
  subst hdsc'
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, ?_⟩
  have hstart : (Mma.vLo L ((d.i - 1) % 3) + 128 * ↑j) * 16 =
      L.sharedBase + 98304 + 32768 * ((d.i - 1) % 3) + 2048 * ↑j := by
    unfold Mma.vLo
    omega
  simp only [hstart]

end Steps

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Cover
