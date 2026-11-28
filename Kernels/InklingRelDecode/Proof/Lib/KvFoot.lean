-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Tensor.BoxWrite

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

noncomputable section
def i32 (x : Nat) : Int := (BitVec.ofNat 32 x).toInt

/-- The copy a K/V tensor load into the CTA's window issues: the `kv_rows` map, the box origin
`(col, row)`, the destination and the barrier. -/
def kvCopySpec (Q : Params) (cta : Nat) (col row dst : Nat) (bar : Loc) : TensorCopy.Spec :=
  ⟨⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass, ![i32 col, i32 row], ⟨.shared, cta, dst⟩,
    none⟩, bar, false, .one⟩

/-- **Where a 64-column bf16 box with 128-byte swizzle writes** (as `TensorCopy.box_writeLoc`,
for any 2-byte format). -/
theorem box_writeLoc2 {s : TensorCopy.Spec} {R x y byte : Nat}
    (h0 : TensorTile.count s.descriptor.box 0 = 64) (hR : TensorTile.rows s.descriptor.box = R)
    (hfb : s.descriptor.format.bytes = 2) (hsw : s.descriptor.swizzle = .b128)
    (hx : x < 64) (hy : y < R) (hb : byte < 2) :
    TensorCopy.writeLoc s x y byte = some { s.sharedBase with
      addr := s.sharedBase.addr +
        TensorSwizzle.offset .b128 s.sharedBase.addr (128 * y + 2 * x + byte) } := by
  unfold TensorCopy.writeLoc TensorTransfer.slotAt
  rw [dite_eq_left (show x < TensorTile.count s.descriptor.box 0 by omega),
    dite_eq_left (show y < TensorTile.rows s.descriptor.box by omega),
    dite_eq_left (show byte < s.descriptor.format.bytes by omega), Option.map_some]
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, h0, hfb, hsw, TensorTile.swizzleWidth]
  rw [show y * max (64 * 2) 128 + x * 2 + byte = 128 * y + 2 * x + byte by
    simp only [Nat.reduceMul, max_self]; ring]

/-- The destination interval uses only the descriptor. In particular it applies
before the source coordinates or their register values have been established. -/
theorem map_foot {spec : TensorCopy.Spec} {Q : Params}
    (desc : (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩)
    {x y z : Nat} {l : Loc} (h : TensorCopy.writeLoc spec x y z = some l) :
    l.space = spec.sharedBase.space ∧ l.cta = spec.sharedBase.cta ∧
    spec.sharedBase.addr ≤ l.addr ∧ l.addr < spec.sharedBase.addr + 8192 := by
  rcases spec with ⟨⟨n,d,origin,dst,rows⟩,bar,cluster,group⟩
  cases desc
  obtain ⟨hx,hy,hz⟩ := TensorCopy.writeLoc_bounds h
  simp [TensorTile.count, TensorTile.rows, TensorTile.rowsOf,
    TensorTile.step, TensorDescriptor.Format.bytes] at hx hy hz
  have byte : z < 2 := by omega
  rw [box_writeLoc2 (R := 64) (by simp [TensorTile.count, TensorTile.step])
    (by simp [TensorTile.rows,TensorTile.rowsOf,TensorTile.count,TensorTile.step])
    rfl rfl hx hy byte] at h
  cases Option.some.inj h
  have bound := TensorCopy.box_offset_lt (base := dst.addr) (R := 64) hx hy byte
  exact ⟨rfl,rfl,Nat.le_add_right ..,Nat.add_lt_add_left bound _⟩

/-- A K/V copy writes only its destination box. -/
theorem copy_foot (Q : Params) (cta col row dst : Nat) (bar : Loc) {x y z : Nat} {l : Loc}
    (h : TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x y z = some l) :
    l.space = .shared ∧ l.cta = cta ∧ dst ≤ l.addr ∧ l.addr < dst + 8192 :=
  map_foot (Q := Q) rfl h

/-- **A KV copy writes each byte from one element** (moved from the first tree's
`Proof/Protocol/SxUCopy.lean`). -/
theorem kv_elem {Q : Params} {cta col row dst : Nat} {bar : Loc} {x y z x' y' z' : Nat} {l : Loc}
    (h1 : TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x y z = some l)
    (h2 : TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x' y' z' = some l) :
    x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨hx, hy, hz⟩ := TensorCopy.writeLoc_bounds h1
  obtain ⟨hx', hy', hz'⟩ := TensorCopy.writeLoc_bounds h2
  have h0 : TensorTile.count (kvCopySpec Q cta col row dst bar).descriptor.box 0 = 64 := by
    simp [kvCopySpec, mapKv, TensorTile.count, TensorTile.step]
  have hR : TensorTile.rows (kvCopySpec Q cta col row dst bar).descriptor.box = 64 := by
    simp [kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step]
  have hfb : (kvCopySpec Q cta col row dst bar).descriptor.format.bytes = 2 := by
    simp [kvCopySpec, mapKv, TensorDescriptor.Format.bytes]
  have hsw : (kvCopySpec Q cta col row dst bar).descriptor.swizzle = .b128 := rfl
  rw [h0] at hx hx'
  rw [hR] at hy hy'
  rw [hfb] at hz hz'
  rw [box_writeLoc2 h0 hR hfb hsw hx hy hz] at h1
  rw [box_writeLoc2 h0 hR hfb hsw hx' hy' hz', ← h1] at h2
  have ha := congrArg Loc.addr (Option.some.inj h2)
  simp only [Nat.add_left_cancel_iff] at ha
  have := TensorCopy.box_offset_inj hx hz hx' hz' ha.symm
  omega

end

end PTX.Kernels.InklingRelDecode.Proof.Lib
