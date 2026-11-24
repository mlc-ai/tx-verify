-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxValues
public import Kernels.InklingRelDecode.Proof.Interface.SxQStore
public import Kernels.InklingRelDecode.Proof.Interface.QxQZero
public import Kernels.InklingRelDecode.Proof.Interface.LpQTile
public import Lemmas.Flow.Scalars

@[expose] public section

/-!
# The A elements of every QK MMA are reals, in every row (`Qx.ElemPrem.qkA`)

`qk_a_real`: on every consistent execution, element `(r, kk)` of the A operand of a QK MMA with
recorded operands is a real, for every row `r < 64` (padding rows and rows of tokens at or beyond
`q_len` included). The byte the MMA reads is the byte of the one store that writes it
(`Lp.bar1_of_mma`, `Lp.qtile_writer`, `Lp.qtile_other`, `Lp.stq_before_mmaRead`,
`read_byte_of_write`). The store writes the word of two query values that two loads of one group
returned: the bf16 query elements when the group's guard holds (`Lp.q_at_fnc1`), and the zero
`ProA.qZero` of a masked load when it does not (`Lp.qz_at_fnc1`). Two bf16 values read back as
themselves (`element_bf16`); the word of two zeros is the 32-bit zero, whose halves read as the bf16
number 0 (`zero_elem`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qx
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts threadCode)
open PTX.Kernels.InklingRelDecode.Proof.Lp (qThread qThread_lt qStore qStore_lt qElemIdx
  qElemIdx_lt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The word of two masked loads -/

/-- The word a store of two masked query loads writes: the 32-bit zero. -/
theorem zero_word : storeValue 32 (joinValue ProA.qZero ProA.qZero) =
    .ok (.bits 32 (BitVec.ofNat 64 0)) := by
  have h : truncBits 16 (BitVec.ofInt 64 0) = BitVec.ofNat 64 0 := by decide
  have h2 : (BitVec.ofNat 64 0 ||| BitVec.ofNat 64 0 <<< 16 : BitVec 64) = BitVec.ofNat 64 0 := by
    decide
  simp only [ProA.qZero, h, joinValue, h2]
  rfl

/-- The 16-bit zero reads as the bf16 number 0. -/
theorem valFloat_bf16_zero : valFloat .bf16 (.bits 16 (BitVec.ofNat 64 0)) = .ok 0 := by
  have h : FloatFmt.bf16.layout.decode 0 = some (.zero false) := by
    simp [FloatFmt.layout, Layout.decode, Layout.fieldVal]
  have hc : classify .bf16 (.bits 16 (BitVec.ofNat 64 0)) = .ok (.zero false) := by
    simpa [FloatFmt.bytes] using classify_bits (fmt := .bf16) (n := 0) (by norm_num) h
  rw [valFloat_of_classify (fmt := .bf16) (x := .zero false) (by intro f y hh; cases hh) hc]
  simp [FVal.finite, pure, Except.pure]

/-- **An element whose two bytes are a half of the 32-bit zero is the bf16 number 0.** -/
theorem zero_elem {o : FloatFmt} {op : Operand} {bytes : List (Option Byte)} {row k p : Nat}
    (hp : p = 0 ∨ p = 2)
    (h0 : bytes[2 * (row * 16 + k)]? = some (some (.bits 32 (BitVec.ofNat 64 0), p)))
    (h1 : bytes[2 * (row * 16 + k) + 1]? = some (some (.bits 32 (BitVec.ofNat 64 0), p + 1))) :
    Assumption.idealMmaElement (.f16 .bf16 o) op bytes row k = .ok 0 := by
  have hb : elementBytes (.f16 .bf16 o) bytes row k =
      [some (.bits 32 (BitVec.ofNat 64 0), p), some (.bits 32 (BitVec.ofNat 64 0), p + 1)] := by
    rw [← take_two h0 h1]
    simp [elementBytes, Kind.k, Kind.width, Nat.mul_comm]
  have hr : rebuild 1 [some ((Value.bits 32 (BitVec.ofNat 64 0)), p),
      some ((Value.bits 32 (BitVec.ofNat 64 0)), p + 1)] = .ok (.bits 16 (BitVec.ofNat 64 0)) := by
    rcases hp with rfl | rfl <;>
      simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
        Value.bitPattern, Value.bytes, Value.toBytes, Value.byteAt] <;> rfl
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb, hr]
  exact valFloat_bf16_zero

/-! ### The element -/

/-- **Every A element of a QK MMA with recorded operands is a real**, for every row `r < 64`. -/
theorem qk_a_real (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : Interface.RoleReads L X) (hE : Interface.Bar1Exits L X) {g k pc dst : Nat}
    {sp : OperandSpec} {acc : Bool} {mask : List Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8} (hs : d.site = .qk j)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands (g, k) = some ops) {r kk : Nat}
    (hr : r < 64) (hk : kk < 16) :
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk = .ok x := by
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', hqo, -, -, -⟩ | ⟨d', P', j', hσ', hI, hs', -⟩
  rotate_left
  · exfalso
    have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs'
    exact absurd hs' (by simp)
  have hdd : d = d' := by
    have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
    simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
    exact this.1
  subst hdd
  have hjj : j = j' := by
    have := hs.symm.trans hs'
    simpa using this
  subst hjj
  have hE' := EvW.mmEnv_of_pre hpre
  set dd := 16 * j.val + kk with hdd
  have hd : dd < 128 := by have := j.isLt; omega
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨i0, pc0, hbar, hc0⟩ := Lp.bar1_of_mma hpre hX hf hR hE (m := (g, k)) hkl hσ
    (t := g / L.block * L.block + qThread r dd) (by
      have hb := hpre.block
      have hq := qThread_lt (r := r) (d := dd)
      show (g / L.block * L.block + qThread r dd) / L.block = g / L.block
      rw [hb]; omega)
  obtain ⟨k1, j1, pc1, dt, a, v, hget1, hcz, hv, hσ1, hkj, hj1, hfence, hσk⟩ :=
    Lp.qtile_writer hpre hX hf hT hg hd hr hbar hc0
  have hb := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  set t := g / L.block * L.block + qThread r dd with ht
  have htl : t < L.threads := by
    have := qThread_lt (r := r) (d := dd)
    rw [hth, hb] at hg ⊢; rw [hb] at ht; omega
  have htc : t / L.block = g / L.block := by
    have := qThread_lt (r := r) (d := dd)
    rw [ht, hb]; omega
  -- the byte the MMA reads at offset `z` of the element
  have hbyte : ∀ z < 2, ops.a[2 * (r * 16 + kk) + z]? = some (v.toBytes[2 * (dd % 2) + z]?) := by
    intro z hz
    rw [← idx_eq]
    have hl : sp.byteLoc .a (32 * r + 2 * kk + z) =
        some ⟨.shared, g / L.block, qAddr L.sharedBase r dd z⟩ := by
      rw [qk_a_loc_eq hE' hqo.desc j.isLt hqo.a hqo.aTmem hr hk hz, hqo.low]
    obtain ⟨obs, hrd, hget⟩ := hX.mma_read_exists (isB := false) ⟨pc, he⟩ hops
      (by simpa using hl)
    simp only [Bool.false_eq_true, ↓reduceIte] at hget
    obtain ⟨hcov, hwb⟩ := hcz z hz
    have hv1 := Lp.stq_before_mmaRead hpre hX hf hR hE htl hbar hc0 hj1 hkj hfence
      (m := (g, k)) hσ (by simp only; rw [htc]) hrd rfl (by simp only; exact htc.symm)
    have hmw : X.MemWrites (.thread (t, k1)) a v.toBytes := by
      show X.Writes (t, k1) a v.toBytes ∨ ∃ old, X.Rmw (t, k1) a old (some v.toBytes)
      exact Or.inl ⟨pc1, hget1⟩
    have := read_byte_of_write hX hrd hmw hcov hv1 (fun other fp bytes hw hcv => .inl
      (Lp.qtile_other hpre hX hf hd hz hr hbar hc0 hσk hw hcv))
    rw [hget, this, hwb]
  -- the two values the store packs
  set i := 4 * qStore r dd + qElemIdx dd with hi
  have hi32 : i < 32 := by
    have := qStore_lt hr hd; have := qElemIdx_lt (d := dd); omega
  have hj1l : j1 ≤ (X.tr t).length := by
    have := (List.getElem?_eq_some_iff.mp (show X.get (t, i0) = some _ from hbar)).1
    simp only at this
    omega
  have hgd : ProA.guardVal L t dt (ProA.ldqSite (2 * i + 1)) =
      ProA.guardVal L t dt (ProA.ldqSite (2 * i)) := by
    rw [ProA.guardVal_ldq L t dt _ (by omega), ProA.guardVal_ldq L t dt _ (by omega),
      show (2 * i + 1) / 16 = 2 * i / 16 by omega]
  have hpar : 2 * (dd % 2) = 0 ∨ 2 * (dd % 2) = 2 := by omega
  cases hG : ProA.guardVal L t dt (ProA.ldqSite (2 * i)) with
  | true =>
    have hx := Lp.q_at_fnc1 hpre hX hf htl hj1l hσ1 (2 * i) (by omega) hG
    have hy := Lp.q_at_fnc1 hpre hX hf htl hj1l hσ1 (2 * i + 1) (by omega) (by rw [hgd, hG])
    unfold Lp.qVal at hx hy
    obtain ⟨x, hx⟩ : ∃ x, dt.q (2 * i) = .float .bf16 x := ⟨_, hx⟩
    obtain ⟨y, hy⟩ : ∃ y, dt.q (2 * i + 1) = .float .bf16 y := ⟨_, hy⟩
    have hb0 := qstore_value hx hy hv (z := 0) (by omega)
    have hb1 := qstore_value hx hy hv (z := 1) (by omega)
    have e0 := hbyte 0 (by omega)
    have e1 := hbyte 1 (by omega)
    simp only [Nat.add_zero] at e0
    rcases hpar with h0 | h2
    · refine ⟨x, element_bf16 ?_ ?_⟩
      · rw [e0, h0]; exact congrArg some hb0.1
      · rw [e1, h0]; exact congrArg some hb1.1
    · refine ⟨y, element_bf16 ?_ ?_⟩
      · rw [e0, h2]; exact congrArg some hb0.2
      · rw [e1, h2]; exact congrArg some hb1.2
  | false =>
    have hx := Lp.qz_at_fnc1 hX hf hj1l hσ1 (2 * i) (by omega) hG
    have hy := Lp.qz_at_fnc1 hX hf hj1l hσ1 (2 * i + 1) (by omega) (by rw [hgd, hG])
    have hvz : v = .bits 32 (BitVec.ofNat 64 0) := by
      unfold ProA.qWord at hv
      rw [hx, hy, zero_word] at hv
      exact (Except.ok.inj hv).symm
    subst hvz
    have hbz : ∀ q < 4, (Value.bits 32 (BitVec.ofNat 64 0)).toBytes[q]? =
        some (.bits 32 (BitVec.ofNat 64 0), q) := by
      intro q hq
      simp [Value.toBytes, Value.bytes, Value.byteAt, hq]
    have e0 := hbyte 0 (by omega)
    have e1 := hbyte 1 (by omega)
    simp only [Nat.add_zero] at e0
    refine ⟨0, zero_elem hpar ?_ ?_⟩
    · rw [e0, hbz _ (by omega)]
    · rw [e1, hbz _ (by omega)]

end
end PTX.Kernels.InklingRelDecode.Proof.Qx
