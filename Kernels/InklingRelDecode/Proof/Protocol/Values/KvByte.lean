-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.KvBox
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Tensor.LoadBoxOnto
public import Lemmas.Tensor.LoadWritten
import Lemmas.Tcgen05.MmaBytePair

@[expose] public section

/-! # The bytes of a K or V tensor copy

A copy of a box of a slab of a block that exists writes every byte of its destination
(`copy_onto`), and the byte at slot `(x, y, z)` of a notified copy is the byte `z` of the bf16
element of the cache that the box covers there (`copy_write_byte`): the cache is read only, so
the byte a copy read is the launch's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A K/V copy writes every byte of its destination box.** -/
theorem copy_onto (Q : Params) (cta col row dst : Nat) (bar : Loc) {l : Loc}
    (hs : l.space = .shared) (hc : l.cta = cta) (lo : dst ≤ l.addr) (hi : l.addr < dst + 8192) :
    ∃ x y z, TensorCopy.writeLoc (Lib.kvCopySpec Q cta col row dst bar) x y z = some l :=
  TensorCopy.writeLoc_b128_64_onto
    (by simp [Lib.kvCopySpec, mapKv, TensorTile.count, TensorTile.step])
    (by simp [Lib.kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step])
    (by simp [Lib.kvCopySpec, mapKv, TensorDescriptor.Format.bytes]) rfl hs hc lo hi

/-- **The two bytes of an element are written at adjacent locations**: an even byte of an aligned
copy is the first byte of its slot's element, and the second byte follows it. -/
theorem copy_pair (Q : Params) (cta col row dst : Nat) (bar : Loc) {x y z : Nat} {l : Loc}
    (hal : dst % 2 = 0) (h : TensorCopy.writeLoc (Lib.kvCopySpec Q cta col row dst bar) x y z =
      some l) (even : l.addr % 2 = 0) :
    z = 0 ∧ TensorCopy.writeLoc (Lib.kvCopySpec Q cta col row dst bar) x y 1 =
      some ⟨l.space, l.cta, l.addr + 1⟩ := by
  have h0 : TensorTile.count (Lib.kvCopySpec Q cta col row dst bar).descriptor.box 0 = 64 := by
    simp [Lib.kvCopySpec, mapKv, TensorTile.count, TensorTile.step]
  have hR : TensorTile.rows (Lib.kvCopySpec Q cta col row dst bar).descriptor.box = 64 := by
    simp [Lib.kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step]
  have hfb : (Lib.kvCopySpec Q cta col row dst bar).descriptor.format.bytes = 2 := by
    simp [Lib.kvCopySpec, mapKv, TensorDescriptor.Format.bytes]
  obtain ⟨hx, hy, hz⟩ := TensorCopy.writeLoc_bounds h
  rw [h0] at hx
  rw [hR] at hy
  rw [hfb] at hz
  have hsw : (Lib.kvCopySpec Q cta col row dst bar).descriptor.swizzle = .b128 := rfl
  have e0 := Lib.box_writeLoc2 h0 hR hfb hsw hx hy hz
  rw [e0] at h
  cases Option.some.inj h
  have hb := TensorSwizzle.offset_byte .b128 dst (128 * y + 2 * x + z)
  have hz0 : z = 0 := by
    simp only [Lib.kvCopySpec] at even
    omega
  subst hz0
  refine ⟨rfl, ?_⟩
  rw [Lib.box_writeLoc2 h0 hR hfb hsw hx hy (by omega : 1 < 2)]
  have hs := TensorSwizzle.offset_succ .b128 dst (128 * y + 2 * x + 0) (by omega)
  simp only [Nat.add_zero] at hs ⊢
  simp only [Lib.kvCopySpec, hs]
  rw [Nat.add_assoc]

/-- **A K/V copy writes its first slot.** -/
theorem copy_first (Q : Params) (cta col row dst : Nat) (bar : Loc) :
    ∃ l, TensorCopy.writeLoc (Lib.kvCopySpec Q cta col row dst bar) 0 0 0 = some l :=
  ⟨_, Lib.box_writeLoc2 (R := 64)
    (by simp [Lib.kvCopySpec, mapKv, TensorTile.count, TensorTile.step])
    (by simp [Lib.kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step])
    (by simp [Lib.kvCopySpec, mapKv, TensorDescriptor.Format.bytes]) rfl (by omega) (by omega)
    (by omega)⟩

/-- **The byte a notified K/V copy writes** at slot `(x, y, z)` is byte `z` of the bf16 element of
the cache at the box's origin plus `(x, y)`. -/
theorem copy_write_byte (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) {i : EvId} {addr : Nat}
    {o : TensorCopy.Observation} {r sl kvh isV hh cta dst : Nat} {bar : Loc} (hr : r < Q.b)
    (hs : sl < 2 * Q.blocks r) (hkvh : kvh < kvHeads) (hV : isV ≤ 1) (hH : hh ≤ 1)
    (ho : X.tensor i = some o) (hi : X.TensorIssue i addr o.spec)
    (hspec : o.spec = Lib.kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar)
    (hn : o.effects.notified = true) {x y z : Nat} (hx : x < 64) (hy : y < 64) (hz : z < 2) :
    TensorCopy.writeByte o x y z = some ((Value.float .bf16 (Q.kv
      (Q.page r sl * Q.pageRows + kvh * Q.headRows + y)
      (kvh * Q.headCols + (128 * isV + 64 * hh + x)))).byteAt z) := by
  have hno := Lib.kvbox_noOob hp hr hs hkvh hV hH cta dst bar
  obtain ⟨rr, cc, -, -, hl⟩ := Lib.kv_readLoc Q cta _ _ dst bar hno hx hy hz
  obtain ⟨-, -, hit⟩ := Lib.kvCopy_readLoc_input hp hr hs hkvh hV hH hl
  obtain ⟨-, -, -, hloc⟩ := Lib.kvCopy_readLoc_eq hp hr hs hkvh hV hH hl
  rw [hloc, ← hspec] at hl
  rw [hloc] at hit
  obtain ⟨w, hw⟩ := writeByte_of_notified hX ho hn hl
  have hc : 128 * isV + 64 * hh + x < 2 * headDim := by unfold headDim; omega
  have hm := hp.kvInput r hr sl hs kvh hkvh y hy _ hc z hz
  rw [show Q.kvBase + 2 * ((Q.page r sl * Q.pageRows + kvh * Q.headRows + y) * Q.slotStride +
    kvh * Q.headCols + (128 * isV + 64 * hh + x)) + z = Q.kvBase + 2 * (Q.slotStride *
      (Q.page r sl * Q.pageRows + kvh * Q.headRows + y) +
      (kvh * Q.headCols + 128 * isV + 64 * hh + x)) + z by ring] at hm
  have := tensor_writeByte_of_initial hX ho hi hl hw hm
    (fun w' dst' bytes hw' hc' => nub ⟨Q, w', dst', _, hp, hw'.intent, hc', rfl, rfl, hit⟩)
  rw [hw, this]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
