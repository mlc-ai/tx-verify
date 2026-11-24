-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.KvFoot
public import Kernels.InklingRelDecode.Proof.Thread.EvWMma
public import Lemmas.Tcgen05.TcSharedAddress

@[expose] public section

/-!
# The shared bytes an MMA of the kernel reads

Moved from the first tree's `Proof/Protocol/RingKvFoot.lean` (the decoded descriptors and the
operand footprints), `Proof/Protocol/RingKvMma.lean` (`lo_lt_k`, `lo_lt_q`, `lo_lt_v`) and
`Proof/Protocol/PlMma.lean` (`mma_foot`), names and namespaces unchanged, so the second tree
states the MMA operands' placement without the first tree's ring protocol.

* `qk_b_foot`: a QK MMA's B operand (the K tile, K-major) reads only bytes of the 16384-byte half
  `hh` of the slot's K region; `pv_b_foot`: a PV MMA's B operand (the V tile, MN-major) reads only
  bytes of the slot's V region; `qk_a_foot`: a QK MMA's A operand reads the query tile; a PV MMA's
  A operand is in Tensor Memory (`pv_a_none`).
* `mma_foot`: a QK or PV MMA event of the MMA warp (the shape `EvW.MmShape` of its site) reads its
  B operand in the K or V ring and, for QK, its A operand in the query tile.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Foot
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section

/-- The decoded QK instruction descriptor: `kind::f16` bf16 into f32, `64 × 128 × 16`,
`cta_group::1`, both operands K-major. -/
def qkDesc : TcMma.Descriptor :=
  ⟨.one, .f16 .bf16 .f32, 64, 128, false, false, false, false, false⟩

/-- The decoded PV instruction descriptor: the B operand transposed (MN-major). -/
def pvDesc : TcMma.Descriptor :=
  ⟨.one, .f16 .bf16 .f32, 64, 128, false, false, false, true, false⟩

theorem qkDesc_eq {d : TcMma.Descriptor} (h : TcMma.decode .one false .f16 Mma.qkIdesc = some d) :
    d = qkDesc := by
  have : TcMma.decode .one false .f16 Mma.qkIdesc = some qkDesc := by decide
  rw [this] at h
  exact (Option.some.inj h).symm

theorem pvDesc_eq {d : TcMma.Descriptor} (h : TcMma.decode .one false .f16 Mma.pvIdesc = some d) :
    d = pvDesc := by
  have : TcMma.decode .one false .f16 Mma.pvIdesc = some pvDesc := by decide
  rw [this] at h
  exact (Option.some.inj h).symm

theorem qkDesc_valid : TcMma.Valid qkDesc := by decide

theorem pvDesc_valid : TcMma.Valid pvDesc := by decide

/-- **The row of a K-major, 128-byte-swizzled address.** The swizzle keeps the 128-byte row of the
unswizzled address `start + 128 (r % 8) + stride (r / 8) + 2 k + byte`. -/
theorem byteAddress_k {start leading stride row k byte a : Nat}
    (h : TcShared.byteAddress 2 .k ⟨start, leading, stride, 0, false, false, .b128⟩ row k byte =
      some a) :
    a / 128 = (start + 128 * (row % 8) + stride * (row / 8) + 2 * k + byte) / 128 := by
  unfold TcShared.byteAddress at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [TcShared.Swizzle.offset]
    rw [TensorSwizzle.offset_row]
    simp only [TcShared.linear, TcShared.Swizzle.sectors, reduceCtorEq, ↓reduceIte]
    congr 1
    omega
  · cases h

/-- **A QK MMA's B operand reads only the half `[B, B + 16384)` of the K tile its start lies
in.** -/
theorem qk_b_foot {s : TcMma.OperandSpec} (hD : s.descriptor = qkDesc) {B c : Nat}
    (hB : B % 128 = 0) (hc : c ≤ 96) (hs : s.b = ⟨B + c, 0, 1024, 0, false, false, .b128⟩)
    {idx : Nat} {l : Loc} (h : s.byteLoc .b idx = some l) :
    l.space = .shared ∧ l.cta = s.lowCta ∧ B ≤ l.addr ∧ l.addr < B + 16384 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  cases hba : TcShared.byteAddress 2 TcShared.Major.k
      ⟨B + c, 0, 1024, 0, false, false, TcShared.Swizzle.b128⟩ (idx / 32 % 128) (idx / 2 % 16)
      (idx % 2) with
  | none => rw [hba] at h; cases h
  | some a =>
    rw [hba] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    have h1 := byteAddress_k hba
    refine ⟨rfl, by simp [hrow], ?_, ?_⟩ <;> simp only <;> omega

/-- **The row of an MN-major, 128-byte-swizzled address.** -/
theorem byteAddress_mn {start leading stride row k byte a : Nat}
    (h : TcShared.byteAddress 2 .mn ⟨start, leading, stride, 0, false, false, .b128⟩ row k byte =
      some a) :
    a / 128 = (start + 2 * (row % 8) + 16 * (row / 8 % 8) + leading * (row / 64) +
      128 * (k % 8) + stride * (k / 8) + byte) / 128 := by
  unfold TcShared.byteAddress at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [TcShared.Swizzle.offset]
    rw [TensorSwizzle.offset_row]
    simp only [TcShared.linear, TcShared.Swizzle.sectors, reduceCtorEq, ↓reduceIte, Nat.reduceDiv,
      Nat.reduceMul]
    congr 1
    omega
  · cases h

/-- **A PV MMA's B operand reads only the 32768 bytes `[B, B + 32768)` of the V tile**, the MMA
`j` of the block starting `2048 j` bytes in. -/
theorem pv_b_foot {s : TcMma.OperandSpec} (hD : s.descriptor = pvDesc) {B j : Nat}
    (hB : B % 128 = 0) (hj : j < 8)
    (hs : s.b = ⟨B + 2048 * j, 16384, 1024, 0, false, false, .b128⟩)
    {idx : Nat} {l : Loc} (h : s.byteLoc .b idx = some l) :
    l.space = .shared ∧ l.cta = s.lowCta ∧ B ≤ l.addr ∧ l.addr < B + 32768 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, pvDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := pvDesc_valid
  simp only [pvDesc] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  cases hba : TcShared.byteAddress 2 TcShared.Major.mn
      ⟨B + 2048 * j, 16384, 1024, 0, false, false, TcShared.Swizzle.b128⟩ (idx / 32 % 128)
      (idx / 2 % 16) (idx % 2) with
  | none => rw [hba] at h; cases h
  | some a =>
    rw [hba] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    have h1 := byteAddress_mn hba
    refine ⟨rfl, by simp [hrow], ?_, ?_⟩ <;> simp only <;> omega

/-! ### The descriptors the MMA warp builds -/

/-- The shared-memory descriptor that the word `lo + 0x40004040 · 2^32` decodes to. -/
def sdesc (lo : Nat) : TcShared.Descriptor :=
  ⟨lo % 32768 * 16, lo / 65536 % 32768 * 16, 1024, 0, false, false, .b128⟩

/-- A word whose swizzle, reserved and version fields are those of the 128-byte swizzle decodes
to its fields. -/
theorem decode_b128 {x : Nat} (hs : x / 2 ^ 61 % 8 = 2)
    (hc : x < 2 ^ 64 ∧ x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 ∧ x / 2 ^ 46 % 8 = 1 ∧
      x / 2 ^ 54 % 128 = 0) :
    TcShared.decode x = some ⟨x % 2 ^ 15 * 16, x / 2 ^ 16 % 2 ^ 15 * 16, x / 2 ^ 32 % 2 ^ 14 * 16,
      x / 2 ^ 49 % 8, x / 2 ^ 52 % 2 = 1, x / 2 ^ 53 % 2 = 1, .b128⟩ := by
  unfold TcShared.decode
  rw [hs]
  simp only [TcShared.decodeSwizzle, hc, and_self, ↓reduceIte]

/-- A descriptor `lo + hi · 2^32` with the high word's fields of `0x40004040`. -/
theorem sdesc_decode_of {lo hi : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0)
    (hhi : hi < 2 ^ 32) (h61 : hi / 2 ^ 29 % 8 = 2) (h46 : hi / 2 ^ 14 % 8 = 1)
    (h54 : hi / 2 ^ 22 % 128 = 0) (h49 : hi / 2 ^ 17 % 8 = 0) (h52 : hi / 2 ^ 20 % 2 = 0)
    (h53 : hi / 2 ^ 21 % 2 = 0) (h32 : hi % 2 ^ 14 = 64) :
    TcShared.decode (lo + hi * 2 ^ 32) = some (sdesc lo) := by
  rw [decode_b128 (by omega) ⟨by omega, by omega, by omega, by omega, by omega⟩]
  have e1 : (lo + hi * 2 ^ 32) % 2 ^ 15 * 16 = lo % 32768 * 16 := by omega
  have e2 : (lo + hi * 2 ^ 32) / 2 ^ 16 % 2 ^ 15 * 16 = lo / 65536 % 32768 * 16 := by omega
  have e3 : (lo + hi * 2 ^ 32) / 2 ^ 32 % 2 ^ 14 * 16 = 1024 := by omega
  have e4 : (lo + hi * 2 ^ 32) / 2 ^ 49 % 8 = 0 := by omega
  have e5 : ¬ (lo + hi * 2 ^ 32) / 2 ^ 52 % 2 = 1 := by omega
  have e6 : ¬ (lo + hi * 2 ^ 32) / 2 ^ 53 % 2 = 1 := by omega
  simp only [e1, e2, e3, e4, e5, e6, decide_false, sdesc]

theorem sdesc_decode {lo : Nat} (hlo : lo < 2 ^ 31) (h15 : lo / 2 ^ 15 % 2 = 0) :
    TcShared.decode (lo + Mma.descHi * 2 ^ 32) = some (sdesc lo) :=
  sdesc_decode_of hlo h15 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The K-major descriptor of a low word below `2 ^ 15`: start `lo * 16`, stride 1024, 128-byte
swizzle. -/
theorem decode_k {lo : Nat} (h : lo < 2 ^ 15) :
    TcShared.decode (lo + Mma.descHi * 2 ^ 32) =
      some ⟨lo * 16, 0, 1024, 0, false, false, .b128⟩ := by
  rw [sdesc_decode (by omega) (by omega)]
  have h1 : lo % 32768 * 16 = lo * 16 := by omega
  have h2 : lo / 65536 % 32768 * 16 = 0 := by omega
  simp only [sdesc, h1, h2]

/-- The V operand's descriptor, bit 26 of the low word set: leading offset 16384. -/
theorem decode_v {lo : Nat} (h : lo < 2 ^ 15) :
    TcShared.decode (lo + 2 ^ 26 + Mma.descHi * 2 ^ 32) =
      some ⟨lo * 16, 16384, 1024, 0, false, false, .b128⟩ := by
  rw [sdesc_decode (lo := lo + 2 ^ 26) (by omega) (by omega)]
  have h1 : (lo + 2 ^ 26) % 32768 * 16 = lo * 16 := by omega
  have h2 : (lo + 2 ^ 26) / 65536 % 32768 * 16 = 16384 := by omega
  simp only [sdesc, h1, h2]

/-- **A QK MMA's A operand (the Q tile) reads only `[B, B + 8192)`**: 64 rows of 128 bytes in the
128-byte-swizzled, K-major layout. -/
theorem qk_a_foot {s : TcMma.OperandSpec} (hD : s.descriptor = qkDesc) {B c : Nat}
    (hB : B % 128 = 0) (hc : c ≤ 96) (hs : s.a = ⟨B + c, 0, 1024, 0, false, false, .b128⟩)
    (haT : s.aTmem = none) {idx : Nat} {l : Loc} (h : s.byteLoc .a idx = some l) :
    l.space = .shared ∧ l.cta = s.lowCta ∧ B ≤ l.addr ∧ l.addr < B + 8192 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs, haT,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  cases hba : TcShared.byteAddress 2 TcShared.Major.k
      ⟨B + c, 0, 1024, 0, false, false, TcShared.Swizzle.b128⟩ (idx / 32 % 64) (idx / 2 % 16)
      (idx % 2) with
  | none => rw [hba] at h; cases h
  | some a =>
    rw [hba] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    have h1 := byteAddress_k hba
    refine ⟨rfl, by simp [hrow], ?_, ?_⟩ <;> simp only <;> omega

/-- **A PV MMA reads no byte of A from shared memory**: A is in Tensor Memory. -/
theorem pv_a_none {s : TcMma.OperandSpec} {a : Nat} (haT : s.aTmem = some a) {idx : Nat} :
    s.byteLoc .a idx = none := by
  unfold TcMma.OperandSpec.byteLoc
  simp [haT]

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Foot

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmEnv)

noncomputable section

/-- The shared base leaves room for the operand descriptors' start fields. -/
theorem lo_lt_k {L : Launch} (hE : MmEnv L) (s j : Nat) (hs : s < 3) (hj : j < 8) :
    Mma.kLo L s + 2 * (j % 4) + 1024 * (j / 4) < 2 ^ 15 := by
  have := hE.sb
  unfold Mma.kLo
  omega

theorem lo_lt_q {L : Launch} (hE : MmEnv L) (j : Nat) (hj : j < 8) :
    Mma.qLo L + 2 * (j % 4) + 512 * (j / 4) < 2 ^ 15 := by
  have := hE.sb
  unfold Mma.qLo
  omega

theorem lo_lt_v {L : Launch} (hE : MmEnv L) (s j : Nat) (hs : s < 3) (hj : j < 8) :
    Mma.vLo L s + 128 * j < 2 ^ 15 := by
  have := hE.sb
  unfold Mma.vLo
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape QkIssue PvIssue mmEnv_of_pre)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **The shared footprint of a QK or PV MMA** at a state `d` of the MMA warp. -/
theorem mma_foot (hpre : Pre Q L mem0) {d : Mma.D} {pc c : Nat} {spec : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hsh : MmShape L g d ⟨pc, .tc (.mma c spec acc mask)⟩) :
    (∀ idx l, spec.byteLoc .b idx = some l → l.space = .shared ∧ l.cta = g / L.block ∧
      L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 196608) ∧
    (∀ idx l, spec.byteLoc .a idx = some l → l.space = .shared ∧ l.cta = g / L.block ∧
      L.sharedBase + 196608 ≤ l.addr ∧ l.addr < L.sharedBase + 212992) := by
  have hE := mmEnv_of_pre hpre
  have hsb := hE.sb
  have hal := hE.align
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site with
  | qk j =>
    simp only [MmShape, QkIssue] at hsh
    obtain ⟨da, db, dsc, hdsc, hda, hdb, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    have hj8 : (j : Nat) < 8 := j.isLt
    have hdb' := Ring.Foot.decode_k (Ring.lo_lt_k hE (i % 3) j (Nat.mod_lt _ (by omega)) hj8)
    have hda' := Ring.Foot.decode_k (Ring.lo_lt_q hE j hj8)
    have hdbe := Option.some.inj (hdb.symm.trans hdb')
    have hdae := Option.some.inj (hda.symm.trans hda')
    subst hdbe hdae
    have hdsc' := Ring.Foot.qkDesc_eq hdsc
    subst hdsc'
    refine ⟨fun idx l hl => ?_, fun idx l hl => ?_⟩
    · have hstart : (Mma.kLo L (i % 3) + 2 * (↑j % 4) + 1024 * (↑j / 4)) * 16 =
          L.sharedBase + 32768 * (i % 3) + 16384 * (↑j / 4) + 32 * (↑j % 4) := by
        unfold Mma.kLo
        omega
      have hB : (L.sharedBase + 32768 * (i % 3) + 16384 * (↑j / 4)) % 128 = 0 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.qk_b_foot (B := L.sharedBase + 32768 * (i % 3) +
        16384 * (↑j / 4)) (c := 32 * (↑j % 4)) rfl hB (by omega) (by simp only [hstart]) hl
      refine ⟨h1, by simpa using h2, by omega, by omega⟩
    · have hstart : (Mma.qLo L + 2 * (↑j % 4) + 512 * (↑j / 4)) * 16 =
          L.sharedBase + 196608 + 8192 * (↑j / 4) + 32 * (↑j % 4) := by
        unfold Mma.qLo
        omega
      have hB : (L.sharedBase + 196608 + 8192 * (↑j / 4)) % 128 = 0 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.qk_a_foot (B := L.sharedBase + 196608 + 8192 * (↑j / 4))
        (c := 32 * (↑j % 4)) rfl hB (by omega) (by simp only [hstart]) rfl hl
      refine ⟨h1, by simpa using h2, by omega, by omega⟩
  | pv j =>
    simp only [MmShape, PvIssue] at hsh
    obtain ⟨db, dsc, hdsc, hdb, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    have hj8 : (j : Nat) < 8 := j.isLt
    have hdb' := Ring.Foot.decode_v (Ring.lo_lt_v hE ((i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj8)
    have hdbe := Option.some.inj (hdb.symm.trans hdb')
    subst hdbe
    have hdsc' := Ring.Foot.pvDesc_eq hdsc
    subst hdsc'
    refine ⟨fun idx l hl => ?_, fun idx l hl => ?_⟩
    · have hstart : (Mma.vLo L ((i - 1) % 3) + 128 * ↑j) * 16 =
          L.sharedBase + 98304 + 32768 * ((i - 1) % 3) + 2048 * ↑j := by
        unfold Mma.vLo
        omega
      have hB : (L.sharedBase + 98304 + 32768 * ((i - 1) % 3)) % 128 = 0 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.pv_b_foot
        (B := L.sharedBase + 98304 + 32768 * ((i - 1) % 3)) (j := ↑j) rfl hB hj8
        (by simp only [hstart]) hl
      refine ⟨h1, by simpa using h2, by omega, by omega⟩
    · rw [Ring.Foot.pv_a_none rfl] at hl
      cases hl
  | _ => simp [MmShape] at hsh

/-- **The slot an MMA's B operand reads**: a QK MMA of iteration `i` reads the K tile of slot
`i % 3`, a PV MMA of iteration `i` the V tile of slot `(i - 1) % 3`. -/
theorem mma_b_slot (hpre : Pre Q L mem0) {d : Mma.D} {pc c : Nat} {spec : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hsh : MmShape L g d ⟨pc, .tc (.mma c spec acc mask)⟩) :
    ((∃ j, d.site = .qk j) ∧ ∀ idx l, spec.byteLoc .b idx = some l → l.space = .shared ∧
      l.cta = g / L.block ∧ L.sharedBase + 32768 * (d.i % 3) ≤ l.addr ∧
      l.addr < L.sharedBase + 32768 * (d.i % 3) + 32768) ∨
    ((∃ j, d.site = .pv j) ∧ ∀ idx l, spec.byteLoc .b idx = some l → l.space = .shared ∧
      l.cta = g / L.block ∧ L.sharedBase + 98304 + 32768 * ((d.i - 1) % 3) ≤ l.addr ∧
      l.addr < L.sharedBase + 98304 + 32768 * ((d.i - 1) % 3) + 32768) := by
  have hE := mmEnv_of_pre hpre
  have hsb := hE.sb
  have hal := hE.align
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site with
  | qk j =>
    simp only [MmShape, QkIssue] at hsh
    obtain ⟨da, db, dsc, hdsc, hda, hdb, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    have hj8 : (j : Nat) < 8 := j.isLt
    have hdb' := Ring.Foot.decode_k (Ring.lo_lt_k hE (i % 3) j (Nat.mod_lt _ (by omega)) hj8)
    have hdbe := Option.some.inj (hdb.symm.trans hdb')
    subst hdbe
    have hdsc' := Ring.Foot.qkDesc_eq hdsc
    subst hdsc'
    refine .inl ⟨⟨j, rfl⟩, fun idx l hl => ?_⟩
    have hstart : (Mma.kLo L (i % 3) + 2 * (↑j % 4) + 1024 * (↑j / 4)) * 16 =
        L.sharedBase + 32768 * (i % 3) + 16384 * (↑j / 4) + 32 * (↑j % 4) := by
      unfold Mma.kLo
      omega
    have hB : (L.sharedBase + 32768 * (i % 3) + 16384 * (↑j / 4)) % 128 = 0 := by omega
    obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.qk_b_foot (B := L.sharedBase + 32768 * (i % 3) +
      16384 * (↑j / 4)) (c := 32 * (↑j % 4)) rfl hB (by omega) (by simp only [hstart]) hl
    exact ⟨h1, by simpa using h2, by simp only; omega, by simp only; omega⟩
  | pv j =>
    simp only [MmShape, PvIssue] at hsh
    obtain ⟨db, dsc, hdsc, hdb, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    have hj8 : (j : Nat) < 8 := j.isLt
    have hdb' := Ring.Foot.decode_v (Ring.lo_lt_v hE ((i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj8)
    have hdbe := Option.some.inj (hdb.symm.trans hdb')
    subst hdbe
    have hdsc' := Ring.Foot.pvDesc_eq hdsc
    subst hdsc'
    refine .inr ⟨⟨j, rfl⟩, fun idx l hl => ?_⟩
    have hstart : (Mma.vLo L ((i - 1) % 3) + 128 * ↑j) * 16 =
        L.sharedBase + 98304 + 32768 * ((i - 1) % 3) + 2048 * ↑j := by
      unfold Mma.vLo
      omega
    have hB : (L.sharedBase + 98304 + 32768 * ((i - 1) % 3)) % 128 = 0 := by omega
    obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.pv_b_foot
      (B := L.sharedBase + 98304 + 32768 * ((i - 1) % 3)) (j := ↑j) rfl hB hj8
      (by simp only [hstart]) hl
    exact ⟨h1, by simpa using h2, by simp only; omega, by simp only; omega⟩
  | _ => simp [MmShape] at hsh

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
