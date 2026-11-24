-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ProtocolLayer
public import Kernels.InklingRelDecode.Proof.Interface.ResultThreads
public import Lemmas.Tcgen05.TcSharedAddress

@[expose] public section

/-!
# Where the MMA operands are in shared memory, and where the copies put them

One address function for each tile:

* `kvAddr sb s isV n d z`: byte `z` of the element of key `n` (`< 128`) and head-dimension index
  `d` (`< 128`) of the K (`isV = 0`) or V (`isV = 1`) tile of ring slot `s`: the 128-byte
  swizzle of the unswizzled byte `sb + 32768 s + 98304 isV + 16384 (d / 64) + 128 n + 2 (d % 64)
  + z`. A K row is 128 bytes of one 64-column half; the half is `16384` bytes (two slabs of 64
  keys), the V tile has the same layout.
* `qAddr sb r d z`: the same for the Q tile at `sb + 196608`, 64 rows of two 8192-byte halves.

`copy_loc` is where a K/V copy writes (`TensorCopy.writeLoc` of `kvCopySpec`: the box element
`(x, y)` of the copy at `dst` is `dst + offset .b128 dst (128 y + 2 x + z)`), and `qk_a_loc`,
`qk_b_loc`, `pv_b_loc` where the operands of the MMA warp's QK and PV MMAs read (`byteLoc` of
the decoded descriptors `Foot.sdesc`): the arithmetic of the layouts, shown to give the same bytes.
So the byte an MMA reads at element `(n, d)` is the one a copy of the box holding that element
writes at `(x, y) = (d % 64, n % 64)`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section

/-! ### The tiles' addresses -/

/-- Byte `z` of element `(n, d)` of the K (`isV = 0`) or V (`isV = 1`) tile of slot `s`. -/
def kvAddr (sb s isV n d z : Nat) : Nat :=
  TensorSwizzle.offset .b128 0
    (sb + 32768 * s + 98304 * isV + 16384 * (d / 64) + 128 * n + 2 * (d % 64) + z)

/-- Byte `z` of element `(r, d)` of the Q tile. -/
def qAddr (sb r d z : Nat) : Nat :=
  TensorSwizzle.offset .b128 0 (sb + 196608 + 8192 * (d / 64) + 128 * r + 2 * (d % 64) + z)

/-! ### The swizzle -/

/-- A swizzled tile at a 128-byte aligned base is the base plus the base-relative swizzle. -/
theorem copy_addr (dst u : Nat) (h : dst % 128 = 0) :
    dst + TensorSwizzle.offset .b128 dst u = TensorSwizzle.offset .b128 0 (dst + u) :=
  (TensorSwizzle.offset_add_base .b128 dst u h).symm

/-- **A KV copy writes the swizzled tile address.** Box element `(x, y)`, byte `z` of the copy of
`kvCopySpec` at `dst` is written at the swizzle of the unswizzled byte `dst + 128 y + 2 x + z`. -/
theorem copy_loc (Q : Params) (cta col row dst : Nat) (bar : Loc) {x y z : Nat}
    (hd : dst % 128 = 0) (hx : x < 64) (hy : y < 64) (hz : z < 2) :
    TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x y z =
      some ⟨.shared, cta, TensorSwizzle.offset .b128 0 (dst + (128 * y + 2 * x + z))⟩ := by
  have h0 : TensorTile.count (kvCopySpec Q cta col row dst bar).descriptor.box 0 = 64 := by
    simp [kvCopySpec, mapKv, TensorTile.count, TensorTile.step]
  have hR : TensorTile.rows (kvCopySpec Q cta col row dst bar).descriptor.box = 64 := by
    simp [kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step]
  have hfb : (kvCopySpec Q cta col row dst bar).descriptor.format.bytes = 2 := by
    simp [kvCopySpec, mapKv, TensorDescriptor.Format.bytes]
  have hsw : (kvCopySpec Q cta col row dst bar).descriptor.swizzle = .b128 := rfl
  rw [box_writeLoc2 h0 hR hfb hsw hx hy hz]
  simp only [kvCopySpec, Option.some.injEq, Loc.mk.injEq, true_and]
  exact copy_addr dst _ hd

/-! ### The K-major and MN-major addresses of the 128-byte swizzle -/

/-- The unswizzled byte of element `(row, k)`, byte `byte` of a K-major operand of 2-byte
elements with the 128-byte swizzle. -/
theorem byteAddress_k_exact {start leading row k byte : Nat} (hb : byte < 2) :
    TcShared.byteAddress 2 .k ⟨start, leading, 1024, 0, false, false, .b128⟩ row k byte =
      some (TensorSwizzle.offset .b128 0 (start + (128 * row + 2 * k + byte))) := by
  simp [TcShared.byteAddress, TcShared.Swizzle.offset, hb, TcShared.linear,
    TcShared.Swizzle.sectors]
  congr 1
  omega

/-- The same for an MN-major operand with leading offset `16384` and stride `1024`: element
`(row, k)`, `k` below 16, is at the unswizzled byte `start + 2 (row % 64) + 16384 (row / 64) +
128 k + byte`. -/
theorem byteAddress_mn_exact {start row k byte : Nat} (hb : byte < 2) :
    TcShared.byteAddress 2 .mn ⟨start, 16384, 1024, 0, false, false, .b128⟩ row k byte =
      some (TensorSwizzle.offset .b128 0
        (start + (2 * (row % 64) + 16384 * (row / 64) + 128 * k + byte))) := by
  simp [TcShared.byteAddress, TcShared.Swizzle.offset, hb, TcShared.linear,
    TcShared.Swizzle.sectors]
  congr 1
  omega

/-! ### The operands' addresses -/

/-- **The A operand of a QK MMA** (the Q tile): element `(r, kk)` of row `r < 64`, byte `z`, is at
the swizzle of the unswizzled byte `start + 128 r + 2 kk + z`. -/
theorem qk_a_loc {s : TcMma.OperandSpec} (hD : s.descriptor = qkDesc) {st : Nat}
    (hs : s.a = ⟨st, 0, 1024, 0, false, false, .b128⟩) (haT : s.aTmem = none) {r kk z : Nat}
    (hr : r < 64) (hk : kk < 16) (hz : z < 2) :
    s.byteLoc .a (32 * r + 2 * kk + z) = some ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (st + (128 * r + 2 * kk + z))⟩ := by
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs, haT,
    TcMma.Kind.k, TcMma.Kind.width]
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  simp [hv]
  have e1 : (32 * r + 2 * kk + z) / 32 = r := by omega
  have e2 : (32 * r + 2 * kk + z) / 2 % 16 = kk := by omega
  have e3 : (32 * r + 2 * kk + z) % 2 = z := by omega
  rw [e1, e2, e3, Nat.mod_eq_of_lt (by omega : r < 64), byteAddress_k_exact hz]
  simp [hr]

/-- **The B operand of a QK MMA** (the K tile): element `(n, kk)` of key row `n < 128`, byte `z`,
is at the swizzle of the unswizzled byte `start + 128 n + 2 kk + z`. -/
theorem qk_b_loc {s : TcMma.OperandSpec} (hD : s.descriptor = qkDesc) {st : Nat}
    (hs : s.b = ⟨st, 0, 1024, 0, false, false, .b128⟩) {n kk z : Nat} (hn : n < 128)
    (hk : kk < 16) (hz : z < 2) :
    s.byteLoc .b (32 * n + 2 * kk + z) = some ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (st + (128 * n + 2 * kk + z))⟩ := by
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width]
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  simp [hv]
  have e1 : (32 * n + 2 * kk + z) / 32 = n := by omega
  have e2 : (32 * n + 2 * kk + z) / 2 % 16 = kk := by omega
  have e3 : (32 * n + 2 * kk + z) % 2 = z := by omega
  rw [e1, e2, e3, Nat.mod_eq_of_lt hn, byteAddress_k_exact hz]
  simp [hn]

/-- **The B operand of a PV MMA** (the V tile, MN-major): element `(n, kk)` of head-dimension
column `n < 128` and key `kk < 16` of the MMA, byte `z`, is at the swizzle of the unswizzled byte
`start + 2 (n % 64) + 16384 (n / 64) + 128 kk + z`. -/
theorem pv_b_loc {s : TcMma.OperandSpec} (hD : s.descriptor = pvDesc) {st : Nat}
    (hs : s.b = ⟨st, 16384, 1024, 0, false, false, .b128⟩) {n kk z : Nat} (hn : n < 128)
    (hk : kk < 16) (hz : z < 2) :
    s.byteLoc .b (32 * n + 2 * kk + z) = some ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (st + (2 * (n % 64) + 16384 * (n / 64) + 128 * kk + z))⟩ := by
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width]
  have hv := pvDesc_valid
  simp only [pvDesc] at hv
  simp [hv]
  have e1 : (32 * n + 2 * kk + z) / 32 = n := by omega
  have e2 : (32 * n + 2 * kk + z) / 2 % 16 = kk := by omega
  have e3 : (32 * n + 2 * kk + z) % 2 = z := by omega
  rw [e1, e2, e3, Nat.mod_eq_of_lt hn, byteAddress_mn_exact hz]
  simp [hn]

/-! ### The copy and the operands agree -/

/-- **A KV copy of the box holding element `(n, d)` writes the tile address of `(n, d)`.** The
box is slab `n / 64`, half `d / 64` of the K or V tile of slot `s`; its element `(d % 64, n % 64)`
is the element `(n, d)`. -/
theorem copy_loc_kv (Q : Params) (sb s isV cta col row : Nat) (bar : Loc) {n d z : Nat}
    (hsb : sb % 128 = 0) (_hn : n < 128) (_hd : d < 128) (hz : z < 2) :
    TensorCopy.writeLoc (kvCopySpec Q cta col row
        (sb + 32768 * s + 98304 * isV + 8192 * (n / 64) + 16384 * (d / 64)) bar) (d % 64) (n % 64)
        z = some ⟨.shared, cta, kvAddr sb s isV n d z⟩ := by
  rw [copy_loc Q cta col row _ bar (by omega) (by omega) (by omega) hz]
  simp only [kvAddr]
  congr 3
  omega

/-- The decoded shared descriptor of the Q operand of QK MMA `j`: start `sb + 196608 + 8192 (j / 4)
+ 32 (j % 4)`, K-major, 128-byte swizzle. -/
theorem decode_qkA {L : Launch} (hE : EvW.MmEnv L) {j : Nat} (hj : j < 8) {da : TcShared.Descriptor}
    (h : TcShared.decode (EvW.mmQkALo L j + Mma.descHi * 2 ^ 32) = some da) :
    da = ⟨L.sharedBase + 196608 + 8192 * (j / 4) + 32 * (j % 4), 0, 1024, 0, false, false,
      .b128⟩ := by
  have hb := hE.sb
  have ha := hE.align
  have hlt : EvW.mmQkALo L j < 2 ^ 15 := by
    unfold EvW.mmQkALo Mma.qLo
    omega
  rw [decode_k hlt] at h
  have := Option.some.inj h
  rw [← this]
  have e : EvW.mmQkALo L j * 16 = L.sharedBase + 196608 + 8192 * (j / 4) + 32 * (j % 4) := by
    unfold EvW.mmQkALo Mma.qLo
    omega
  rw [e]

/-- The decoded descriptor of the K operand of QK MMA `j` in slot `s`: start `sb + 32768 s +
16384 (j / 4) + 32 (j % 4)`. -/
theorem decode_qkB {L : Launch} (hE : EvW.MmEnv L) {s j : Nat} (hs : s < 3) (hj : j < 8)
    {db : TcShared.Descriptor}
    (h : TcShared.decode (EvW.mmQkBLo L s j + Mma.descHi * 2 ^ 32) = some db) :
    db = ⟨L.sharedBase + 32768 * s + 16384 * (j / 4) + 32 * (j % 4), 0, 1024, 0, false, false,
      .b128⟩ := by
  have hb := hE.sb
  have ha := hE.align
  have hlt : EvW.mmQkBLo L s j < 2 ^ 15 := by
    unfold EvW.mmQkBLo Mma.kLo
    omega
  rw [decode_k hlt] at h
  have := Option.some.inj h
  rw [← this]
  have e : EvW.mmQkBLo L s j * 16 = L.sharedBase + 32768 * s + 16384 * (j / 4) + 32 * (j % 4) := by
    unfold EvW.mmQkBLo Mma.kLo
    omega
  rw [e]

/-- The decoded descriptor of the V operand of PV MMA `j` in slot `s`: start `sb + 98304 + 32768 s
+ 2048 j`, MN-major (leading offset 16384). -/
theorem decode_pvB {L : Launch} (hE : EvW.MmEnv L) {s j : Nat} (hs : s < 3) (hj : j < 8)
    {db : TcShared.Descriptor}
    (h : TcShared.decode (EvW.mmPvBLo L s j + 2 ^ 26 + Mma.descHi * 2 ^ 32) = some db) :
    db = ⟨L.sharedBase + 98304 + 32768 * s + 2048 * j, 16384, 1024, 0, false, false,
      .b128⟩ := by
  have hb := hE.sb
  have ha := hE.align
  have hlt : EvW.mmPvBLo L s j < 2 ^ 15 := by
    unfold EvW.mmPvBLo Mma.vLo
    omega
  rw [decode_v hlt] at h
  have := Option.some.inj h
  rw [← this]
  have e : EvW.mmPvBLo L s j * 16 = L.sharedBase + 98304 + 32768 * s + 2048 * j := by
    unfold EvW.mmPvBLo Mma.vLo
    omega
  rw [e]

/-- **The QK MMA `j`'s A element `(r, kk)` is the Q tile's element `(r, 16 j + kk)`.** -/
theorem qk_a_loc_eq {L : Launch} (hE : EvW.MmEnv L) {s : TcMma.OperandSpec}
    (hD : s.descriptor = qkDesc) {j : Nat} (hj : j < 8)
    (hdec : TcShared.decode (EvW.mmQkALo L j + Mma.descHi * 2 ^ 32) = some s.a)
    (haT : s.aTmem = none) {r kk z : Nat} (hr : r < 64) (hk : kk < 16) (hz : z < 2) :
    s.byteLoc .a (32 * r + 2 * kk + z) =
      some ⟨.shared, s.lowCta, qAddr L.sharedBase r (16 * j + kk) z⟩ := by
  have hs := decode_qkA hE hj hdec
  rw [qk_a_loc hD hs haT hr hk hz]
  simp only [qAddr]
  congr 3
  omega

/-- **The QK MMA `j`'s B element `(n, kk)` is the K tile's element `(n, 16 j + kk)` of slot
`s`.** -/
theorem qk_b_loc_eq {L : Launch} (hE : EvW.MmEnv L) {s : TcMma.OperandSpec}
    (hD : s.descriptor = qkDesc) {slot j : Nat} (hslot : slot < 3) (hj : j < 8)
    (hdec : TcShared.decode (EvW.mmQkBLo L slot j + Mma.descHi * 2 ^ 32) = some s.b)
    {n kk z : Nat} (hn : n < 128) (hk : kk < 16) (hz : z < 2) :
    s.byteLoc .b (32 * n + 2 * kk + z) =
      some ⟨.shared, s.lowCta, kvAddr L.sharedBase slot 0 n (16 * j + kk) z⟩ := by
  have hs := decode_qkB hE hslot hj hdec
  rw [qk_b_loc hD hs hn hk hz]
  simp only [kvAddr]
  congr 3
  omega

/-- **The PV MMA `j`'s B element `(n, kk)` is the V tile's element of key `16 j + kk` and
head-dimension column `n`.** -/
theorem pv_b_loc_eq {L : Launch} (hE : EvW.MmEnv L) {s : TcMma.OperandSpec}
    (hD : s.descriptor = pvDesc) {slot j : Nat} (hslot : slot < 3) (hj : j < 8)
    (hdec : TcShared.decode (EvW.mmPvBLo L slot j + 2 ^ 26 + Mma.descHi * 2 ^ 32) = some s.b)
    {n kk z : Nat} (hn : n < 128) (hk : kk < 16) (hz : z < 2) :
    s.byteLoc .b (32 * n + 2 * kk + z) =
      some ⟨.shared, s.lowCta, kvAddr L.sharedBase slot 1 (16 * j + kk) n z⟩ := by
  have hs := decode_pvB hE hslot hj hdec
  rw [pv_b_loc hD hs hn hk hz]
  simp only [kvAddr]
  congr 3
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
