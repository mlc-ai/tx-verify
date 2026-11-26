-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Mma
public import Lemmas.Tcgen05.SharedRow
public import Core.Tc.TcCopy

@[expose] public section

/-! # The shared bytes the MMA warp's operations read

Pure geometry of the MMA warp's shared operands. The descriptors the code builds, from a tile's
first byte `B` (a multiple of 128):

* `keyDesc B k`: QK MMA `k`'s B (and copy `k`'s source): K-major, 128-byte swizzle, start
  `B + 16 qkDelta k`; its bytes lie in `[B, B + 65536)` (`key_foot`, `copy_foot`);
* `valueDesc B k`: PV MMA `k`'s B: MN-major (the PV word transposes B), 128-byte swizzle, leading
  offset 8192, start `B + 16 pvDelta k`; its bytes lie in `[B, B + 65536)` (`value_foot`);
* `probDesc B k`: PV MMA `k`'s A (the P tile): K-major, no swizzle, leading offset 1024, stride
  128, start `B + 2048 (k / 2)`; its bytes lie in `[B, B + 8192)` (`prob_foot`);
* a QK MMA reads no A byte from shared memory (`tmemA_none`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

/-- The descriptor offsets (in 16-byte units) of QK MMA `k`'s B and of PV MMA `k`'s B. -/
def qkDelta (k : Nat) : Nat := 1024 * (k / 4) + 2 * (k % 4)
def pvDelta (k : Nat) : Nat := 128 * (k / 2) + 2048 * (k % 2)

/-- The decoded QK and PV instruction descriptors. -/
def qkD : TcMma.Descriptor :=
  { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 128, negateA := false,
    negateB := false, transposeA := false, transposeB := false, ws := true }
def pvD : TcMma.Descriptor :=
  { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 256, negateA := false,
    negateB := false, transposeA := false, transposeB := true, ws := true }

theorem qkD_eq {d : TcMma.Descriptor} (h : TcMma.decode .one true .f16 TmemRow.qkIdesc = some d) :
    d = qkD := by
  have : TcMma.decode .one true .f16 TmemRow.qkIdesc = some qkD := by decide
  rw [this] at h
  exact (Option.some.inj h).symm

theorem pvD_eq {d : TcMma.Descriptor} (h : TcMma.decode .one true .f16 TmemRow.pvIdesc = some d) :
    d = pvD := by
  have : TcMma.decode .one true .f16 TmemRow.pvIdesc = some pvD := by decide
  rw [this] at h
  exact (Option.some.inj h).symm

theorem qkD_valid : TcMma.Valid qkD := by decide
theorem pvD_valid : TcMma.Valid pvD := by decide

/-- The shared descriptors the code builds. -/
def keyDesc (B k : Nat) : TcShared.Descriptor :=
  ⟨B + 16 * qkDelta k, 16, 1024, 0, false, false, .b128⟩
def valueDesc (B k : Nat) : TcShared.Descriptor :=
  ⟨B + 16 * pvDelta k, 8192, 1024, 0, false, false, .b128⟩
def probDesc (B k : Nat) : TcShared.Descriptor :=
  ⟨B + 2048 * (k / 2), 1024, 128, 0, false, false, .none⟩

/-- A row's bound from its 128-byte row. -/
private theorem row_bound {B a x n : Nat} (hB : B % 128 = 0) (h : a / 128 = x / 128)
    (hlo : B ≤ x) (hhi : x < B + n) (hn : n % 128 = 0) : B ≤ a ∧ a < B + n := by
  omega

/-- **QK MMA `k`'s B bytes lie in `[B, B + 65536)`** of the low CTA. -/
theorem key_foot {s : TcMma.OperandSpec} (hD : s.descriptor = qkD) {B k : Nat}
    (hB : B % 128 = 0) (hk : k < 16) (hs : s.b = keyDesc B k) {idx : Nat} {l : Loc}
    (h : s.byteLoc .b idx = some l) :
    l.space = .shared ∧ l.cta = s.lowCta ∧ B ≤ l.addr ∧ l.addr < B + 65536 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, qkD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := qkD_valid
  simp only [qkD] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  obtain ⟨a, hba, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  have h1 := TcShared.byteAddress_b128_row rfl hba
  simp only [TcShared.linear, TcShared.Swizzle.sectors, keyDesc, qkDelta, reduceCtorEq,
    ↓reduceIte] at h1
  refine ⟨rfl, by simp [hrow], ?_⟩
  exact row_bound hB h1 (by omega) (by omega) (by decide)

/-- **PV MMA `k`'s B bytes lie in `[B, B + 65536)`** of the low CTA. -/
theorem value_foot {s : TcMma.OperandSpec} (hD : s.descriptor = pvD) {B k : Nat}
    (hB : B % 128 = 0) (hk : k < 8) (hs : s.b = valueDesc B k) {idx : Nat} {l : Loc}
    (h : s.byteLoc .b idx = some l) :
    l.space = .shared ∧ l.cta = s.lowCta ∧ B ≤ l.addr ∧ l.addr < B + 65536 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, pvD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := pvD_valid
  simp only [pvD] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  obtain ⟨a, hba, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  have h1 := TcShared.byteAddress_b128_row rfl hba
  simp only [TcShared.linear, TcShared.Swizzle.sectors, valueDesc, pvDelta, reduceCtorEq,
    ↓reduceIte] at h1
  refine ⟨rfl, by simp [hrow], ?_⟩
  exact row_bound hB h1 (by omega) (by omega) (by decide)

/-- **PV MMA `k`'s A bytes (the P tile) lie in `[B, B + 8192)`** of the low or high CTA. -/
theorem prob_foot {s : TcMma.OperandSpec} (hD : s.descriptor = pvD) {B k : Nat}
    (hk : k < 8) (hs : s.a = probDesc B k) (haT : s.aTmem = none) {idx : Nat} {l : Loc}
    (h : s.byteLoc .a idx = some l) :
    l.space = .shared ∧ (l.cta = s.lowCta ∨ l.cta = s.highCta) ∧ B ≤ l.addr ∧
      l.addr < B + 8192 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, pvD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs, haT,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := pvD_valid
  simp only [pvD] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  obtain ⟨a, hba, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  have h1 := TcShared.byteAddress_none_eq rfl hba
  simp only [TcShared.linear, TcShared.Swizzle.sectors, probDesc, ↓reduceIte] at h1
  refine ⟨rfl, by split <;> simp, ?_⟩
  show B ≤ a ∧ a < B + 8192
  omega

/-- **An MMA with A in Tensor Memory reads no A byte from shared memory.** -/
theorem tmemA_none {s : TcMma.OperandSpec} {a : Nat} (haT : s.aTmem = some a) (idx : Nat) :
    s.byteLoc .a idx = none := by
  unfold TcMma.OperandSpec.byteLoc
  simp [haT]

/-- **Copy `k`'s source bytes lie in `[B, B + 65536)`** of the copying CTA. -/
theorem copy_foot {B k cta idx : Nat} (hB : B % 128 = 0) (hk : k < 16) {l : Loc}
    (h : TcCopy.byteLoc .s128x256b (keyDesc B k) cta idx = some l) :
    l.space = .shared ∧ l.cta = cta ∧ B ≤ l.addr ∧ l.addr < B + 65536 := by
  unfold TcCopy.byteLoc at h
  split at h
  · rename_i hi
    obtain ⟨a, hba, rfl⟩ := Option.map_eq_some_iff.mp h
    have h1 := TcShared.byteAddress_b128_row rfl hba
    simp only [TcShared.linear, TcShared.Swizzle.sectors, keyDesc, qkDelta, reduceCtorEq,
      ↓reduceIte, TcCpShape.sourceBytes, TcCpShape.rowBytes, TcCpShape.rows] at h1 hi
    refine ⟨rfl, rfl, ?_⟩
    exact row_bound hB h1 (by omega) (by omega) (by decide)
  · cases h

/-! ### Decoding the descriptor words -/

/-- A descriptor word's start field added to a word with start field 0. -/
theorem decode_start_add {n x : Nat} {d : TcShared.Descriptor}
    (hn : n < 2 ^ 15) (hx : x % 2 ^ 15 = 0) (hb : x + 2 ^ 15 ≤ 2 ^ 64)
    (hd : TcShared.decode x = some d) :
    TcShared.decode (n + x) = some { d with start := 16 * n } := by
  have hlo : (n + x) % 2 ^ 15 = n := by omega
  have hbase : (n + x) / 2 ^ 15 = x / 2 ^ 15 := by omega
  have hfld (s : Nat) (hs : 15 ≤ s) : (n + x) / 2 ^ s = x / 2 ^ s := by
    have he : 2 ^ s = 2 ^ 15 * 2 ^ (s - 15) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hs]
    rw [he, ← Nat.div_div_eq_div_mul, hbase, Nat.div_div_eq_div_mul]
  have hn64 : n + x < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  have he : TcShared.decode (n + x) =
      (TcShared.decode x).map (fun d => { d with start := 16 * n }) := by
    unfold TcShared.decode
    simp only [hfld 61 (by decide), hfld 15 (by decide), hfld 31 (by decide),
      hfld 46 (by decide), hfld 54 (by decide), hfld 16 (by decide), hfld 32 (by decide),
      hfld 49 (by decide), hfld 52 (by decide), hfld 53 (by decide),
      hlo, hn64, hx64, true_and]
    split
    · rfl
    · split <;> simp [Nat.mul_comm n 16]
  rw [he, hd]
  rfl

/-- The high constants of the key (and query copy), value and P descriptor words. -/
abbrev keyHi : Nat := 4611756662049538048
abbrev valueHi : Nat := 4611756662083026944
abbrev probHi : Nat := 70403108110336

theorem decode_key {n : Nat} (hn : n < 2 ^ 15) :
    TcShared.decode (n + keyHi) = some ⟨16 * n, 16, 1024, 0, false, false, .b128⟩ :=
  decode_start_add (d := ⟨0, 16, 1024, 0, false, false, .b128⟩) hn (by decide) (by decide)
    (by decide)

theorem decode_value {n : Nat} (hn : n < 2 ^ 15) :
    TcShared.decode (n + valueHi) = some ⟨16 * n, 8192, 1024, 0, false, false, .b128⟩ :=
  decode_start_add (d := ⟨0, 8192, 1024, 0, false, false, .b128⟩) hn (by decide) (by decide)
    (by decide)

theorem decode_prob {n : Nat} (hn : n < 2 ^ 15) :
    TcShared.decode (n + probHi) = some ⟨16 * n, 1024, 128, 0, false, false, .none⟩ :=
  decode_start_add (d := ⟨0, 1024, 128, 0, false, false, .none⟩) hn (by decide) (by decide)
    (by decide)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
