-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSmem
public import Kernels.FlashAttn4Fwd.Proof.Thread.Mma
public import Lemmas.Tcgen05.TcSharedAddress
public import Lemmas.Tensor.BoxWrite

@[expose] public section

/-! # The ring boxes and the shared bytes of an MMA operand element

The arithmetic of the input rings' boxes and of the MMA warp's shared-memory descriptors, below
the protocol layer so that the thread layer can use it. The copies of a ring slot are boxes of
64 FP16 columns by `copyBytes / 128` rows, box `j` at `Rings.boxBase b j`, `copyBytes` apart from
the region's start (`Rings.regionSize_eq`, `Rings.box_offset_lt'`). The instruction descriptors
decode to `SmemElements.qkDesc` and `SmemElements.pvDesc`; an element of a QK operand (K-major)
or of the B operand of a PV MMA (MN-major) is a byte of a 128-byte-swizzled box
(`qk_a_byteLoc`, `qk_b_byteLoc`, `pv_b_byteLoc`), the step starts are box bytes
(`qStepStart_eq`, `kStepStart_eq`, `vStepStart_eq`) and a box byte is in its ring region
(`box_inRegion`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma TensorDescriptor

noncomputable section

namespace Rings

variable {L : Launch}

/-- The shared address of box `j` of full barrier `b`'s region. -/
def boxBase (L : Launch) (b : FBar) (j : Nat) : Nat := L.sharedBase + b.regionOff + j * b.copyBytes

theorem copyBytes_cases {b : FBar} (hb : b.isFull) :
    b.copyBytes = 16384 ∨ b.copyBytes = 8192 := by
  cases b <;> simp only [FBar.isFull, Bool.false_eq_true] at hb
  · exact .inl rfl
  · simp only [FBar.copyBytes]
    split_ifs
    · exact .inr rfl
    · exact .inl rfl

theorem copyBytes_mul {b : FBar} (hb : b.isFull) :
    b.copyBytes = 128 * (b.copyBytes / 128) ∧ 0 < b.copyBytes / 128 := by
  rcases copyBytes_cases hb with h | h <;> rw [h] <;> omega

theorem regionSize_kv (s : Fin 6) :
    (FBar.kvFull s).regionSize = (FBar.kvFull s).copies * (FBar.kvFull s).copyBytes := by
  dsimp only [FBar.regionSize, FBar.copies, FBar.copyBytes]
  split_ifs <;> rfl

theorem regionSize_q (st : Fin 2) :
    (FBar.qFull st).regionSize = (FBar.qFull st).copies * (FBar.qFull st).copyBytes := by
  rw [show (FBar.qFull st).regionSize = 32768 from rfl,
    show (FBar.qFull st).copies = 2 from rfl, show (FBar.qFull st).copyBytes = 16384 from rfl]

theorem regionSize_eq {b : FBar} (hb : b.isFull) : b.regionSize = b.copies * b.copyBytes := by
  cases b <;> simp only [FBar.isFull, Bool.false_eq_true] at hb
  · exact regionSize_q _
  · exact regionSize_kv _

/-- A byte of box `j` is at most `copyBytes` past its start. -/
theorem box_offset_lt' {b : FBar} (hb : b.isFull) (base : Nat) {x y z : Nat} (hx : x < 64)
    (hy : y < b.copyBytes / 128) (hz : z < 2) :
    TensorSwizzle.offset .b128 base (128 * y + 2 * x + z) < b.copyBytes := by
  have h := TensorCopy.box_offset_lt (base := base) hx hy hz
  have := (copyBytes_mul hb).1
  omega

/-- A one-byte access covering `l` is at `l`. -/
theorem covers_one {a : Acc} {l : Loc} (h : a.Covers l) (hs : a.size = 1) : a.loc = l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hs] at h4
  have h5 : l.addr = a.loc.addr := by omega
  obtain ⟨s1, c1, a1⟩ := l
  simp only at h1 h2 h5
  rw [h1, h2, h5]

end Rings

namespace SmemElements

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The decoded QK instruction descriptor. -/
def qkDesc : Descriptor := ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, false, false⟩

/-- The decoded PV instruction descriptor (B transposed: MN-major). -/
def pvDesc : Descriptor := ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, true, false⟩

theorem qkDesc_eq {d : Descriptor} (h : decode .two false .f16 Mma.qkIdesc = some d) :
    d = qkDesc :=
  (Option.some.inj h).symm

theorem pvDesc_eq {d : Descriptor} (h : decode .two false .f16 Mma.pvIdesc = some d) :
    d = pvDesc :=
  (Option.some.inj h).symm

theorem qkDesc_valid : Valid qkDesc := by decide

theorem pvDesc_valid : Valid pvDesc := by decide

/-- The CTA of half `r` of an operand split over the pair. -/
theorem cta_half {s : OperandSpec} {r y h : Nat} (hr : r < 2) (hy : y < h) :
    (if h * r + y < h then s.lowCta else s.highCta) = if r = 0 then s.lowCta else s.highCta := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · simp [hy]
  · simp

/-- **The byte of a QK MMA's B operand** (K-major, at `base + 2 c`): row `64 r + y`, contraction
`k`, byte `z` is element `(c + k, y)` of the 128-byte-swizzled box at `base` in CTA `r`. -/
theorem qk_b_byteLoc {s : OperandSpec} (hD : s.descriptor = qkDesc) {base c : Nat}
    (hs : s.b = kMajorDesc (base + 2 * c)) (hb : base % 128 = 0) {r y k z : Nat}
    (hr : r < 2) (hy : y < 64) (hk : k < 16) (hz : z < 2) :
    s.byteLoc .b (32 * (64 * r + y) + 2 * k + z) = some ⟨.shared,
      if r = 0 then s.lowCta else s.highCta,
      base + TensorSwizzle.offset .b128 base (128 * y + 2 * (c + k) + z)⟩ := by
  have hdiv : (32 * (64 * r + y) + 2 * k + z) / (16 * 2) = 64 * r + y := by omega
  have hkdiv : (32 * (64 * r + y) + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * (64 * r + y) + 2 * k + z) % 2 = z := by omega
  have hlocal : (64 * r + y) % (128 / 2) = y := by omega
  have hext : 64 * r + y < 128 := by omega
  have hcta : (if 64 * r + y < 128 / 2 then s.lowCta else s.highCta) =
      if r = 0 then s.lowCta else s.highCta := cta_half (h := 64) hr hy
  have haddr := TcShared.k128_tma_byte 2 base c 16 y k z hb hz
  have hv := qkDesc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, qkDesc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv,
    Operand.major, hlocal, hkdiv, hbmod, hs, kMajorDesc] at hv ⊢
  simp [hv, hext, hcta, haddr]

/-- **The byte of a QK MMA's A operand** (in shared memory, K-major, at `base + 2 c`): row
`128 r + y`, contraction `k`, byte `z` is element `(c + k, y)` of the 128-byte-swizzled box at
`base` in CTA `r`. -/
theorem qk_a_byteLoc {s : OperandSpec} (hD : s.descriptor = qkDesc) (haT : s.aTmem = none)
    {base c : Nat} (hs : s.a = kMajorDesc (base + 2 * c)) (hb : base % 128 = 0)
    {r y k z : Nat} (hr : r < 2) (hy : y < 128) (hk : k < 16) (hz : z < 2) :
    s.byteLoc .a (32 * (128 * r + y) + 2 * k + z) = some ⟨.shared,
      if r = 0 then s.lowCta else s.highCta,
      base + TensorSwizzle.offset .b128 base (128 * y + 2 * (c + k) + z)⟩ := by
  have hdiv : (32 * (128 * r + y) + 2 * k + z) / (16 * 2) = 128 * r + y := by omega
  have hkdiv : (32 * (128 * r + y) + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * (128 * r + y) + 2 * k + z) % 2 = z := by omega
  have hlocal : (128 * r + y) % (256 / 2) = y := by omega
  have hext : 128 * r + y < 256 := by omega
  have hcta : (if 128 * r + y < 256 / 2 then s.lowCta else s.highCta) =
      if r = 0 then s.lowCta else s.highCta := cta_half (h := 128) hr hy
  have haddr := TcShared.k128_tma_byte 2 base c 16 y k z hb hz
  have hv := qkDesc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, qkDesc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv,
    Operand.major, hlocal, hkdiv, hbmod, hs, kMajorDesc, haT] at hv ⊢
  simp [hv, hext, hcta, haddr]

/-- The MN-major address of a 2-byte element with 64 columns per CTA: the packed 128-byte row
`k`, column `y`. -/
theorem mn128_tma_byte (base y k z : Nat) (hb : base % 128 = 0) (hy : y < 64) (hz : z < 2) :
    TcShared.byteAddress 2 .mn (mnMajorDesc base) y k z =
      some (base + TensorSwizzle.offset .b128 base (128 * k + 2 * y + z)) := by
  simp only [TcShared.byteAddress, mnMajorDesc, TcShared.linear, TcShared.Swizzle.sectors,
    TcShared.Swizzle.offset]
  simp only [reduceCtorEq, ↓reduceIte, hz, true_and, true_implies, false_implies,
    Nat.reduceEqDiff]
  rw [← TensorSwizzle.offset_add_base _ _ _ hb]
  congr 2
  omega

/-- **The byte of a PV MMA's B operand** (MN-major, at `base + 128 c`): column `64 r + y`,
contraction `k`, byte `z` is element `(y, c + k)` of the 128-byte-swizzled box at `base` in CTA
`r`. -/
theorem pv_b_byteLoc {s : OperandSpec} (hD : s.descriptor = pvDesc) {base c : Nat}
    (hs : s.b = mnMajorDesc (base + 128 * c)) (hb : base % 128 = 0) {r y k z : Nat}
    (hr : r < 2) (hy : y < 64) (hk : k < 16) (hz : z < 2) :
    s.byteLoc .b (32 * (64 * r + y) + 2 * k + z) = some ⟨.shared,
      if r = 0 then s.lowCta else s.highCta,
      base + TensorSwizzle.offset .b128 base (128 * (c + k) + 2 * y + z)⟩ := by
  have hdiv : (32 * (64 * r + y) + 2 * k + z) / (16 * 2) = 64 * r + y := by omega
  have hkdiv : (32 * (64 * r + y) + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * (64 * r + y) + 2 * k + z) % 2 = z := by omega
  have hlocal : (64 * r + y) % (128 / 2) = y := by omega
  have hext : 64 * r + y < 128 := by omega
  have hcta : (if 64 * r + y < 128 / 2 then s.lowCta else s.highCta) =
      if r = 0 then s.lowCta else s.highCta := cta_half (h := 64) hr hy
  have hb' : (base + 128 * c) % 128 = 0 := by omega
  have haddr := mn128_tma_byte (base + 128 * c) y k z hb' hy hz
  have e1 := TensorSwizzle.offset_add_base .b128 (base + 128 * c) (128 * k + 2 * y + z) hb'
  have e2 := TensorSwizzle.offset_add_base .b128 base (128 * (c + k) + 2 * y + z) hb
  have e3 : base + 128 * c + (128 * k + 2 * y + z) = base + (128 * (c + k) + 2 * y + z) := by
    ring
  rw [← e1, e3, e2] at haddr
  have hv := pvDesc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, pvDesc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv,
    Operand.major, hlocal, hkdiv, hbmod, hs] at hv ⊢
  simp [hv, hext, hcta, haddr]

/-! ### The step starts are box bytes -/

theorem boxBase_mod (hpre : Pre P L mem0) {b : FBar} (hb : b.isFull) (j : Nat) :
    Rings.boxBase L b j % 128 = 0 := by
  have := hpre.sharedAlignment
  cases b with
  | qFull st => simp only [Rings.boxBase, FBar.regionOff, FBar.copyBytes]; omega
  | kvFull s =>
    simp only [Rings.boxBase, FBar.regionOff, FBar.copyBytes]
    split_ifs <;> omega
  | _ => cases hb

theorem qStepStart_eq (st : Fin 2) (j : Nat) :
    qStepStart L st j = Rings.boxBase L (.qFull st) (j / 4) + 2 * (16 * (j % 4)) := by
  simp only [qStepStart, Rings.boxBase, FBar.copyBytes]
  ring

theorem kStepStart_eq {sl : Fin 6} (hs : sl.val % 2 = 0) (j : Nat) :
    kStepStart L sl j = Rings.boxBase L (.kvFull sl) (j / 4) + 2 * (16 * (j % 4)) := by
  simp only [kStepStart, Rings.boxBase, FBar.copyBytes, hs, ↓reduceIte]
  ring

theorem vStepStart_eq (sl : Fin 6) (j : Nat) :
    vStepStart L sl j = Rings.boxBase L (.kvFull sl) 0 + 128 * (16 * j) := by
  simp only [vStepStart, Rings.boxBase]
  ring

/-- **A box byte is in its ring region.** -/
theorem box_inRegion {b : FBar} (hb : b.isFull) {cta jb x y z : Nat} (hj : jb < b.copies)
    (hx : x < 64) (hy : y < b.copyBytes / 128) (hz : z < 2) :
    InRegion L cta b ⟨.shared, cta, Rings.boxBase L b jb + TensorSwizzle.offset .b128
      (Rings.boxBase L b jb) (128 * y + 2 * x + z)⟩ := by
  have ho := Rings.box_offset_lt' hb (Rings.boxBase L b jb) hx hy hz
  have hr := Rings.regionSize_eq hb
  have hm : (jb + 1) * b.copyBytes ≤ b.copies * b.copyBytes := Nat.mul_le_mul_right _ hj
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [Rings.boxBase] at ho ⊢
  · omega
  · rw [hr]
    have : (jb + 1) * b.copyBytes = jb * b.copyBytes + b.copyBytes := by ring
    omega

end SmemElements

end
end PTX.Kernels.FlashAttn4Fwd.Proof
