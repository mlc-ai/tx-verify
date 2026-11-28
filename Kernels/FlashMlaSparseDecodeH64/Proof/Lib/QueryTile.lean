-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn
import Lemmas.Tensor.TensorSwizzle
import Lemmas.Tensor.BoxWrite

@[expose] public section

/-! # The geometry of the query tile

The eight query loads of the MMA lane (load `a` has box origin `(64 a, 0, q, e)`) write the 128-byte
swizzled box of 64 heads by 64 features at `S + 8192 a` (`q_writeLoc`), and read the bytes
`2 · element + z` of the contiguous `(b, s_q, 64, 512)` bf16 view (`q_readLoc`). Copy `k` of the
query to Tensor Memory reads source byte `2 (16 r + t) + z` from the `keyDesc` tile at the swizzled
address of the linear byte of head `r % 64`, feature `128 (k / 4) + 64 (r / 64) + 16 (k % 4) + t`
(`qcopy_byteLoc`), and this is the box byte of that head and feature (`q_linear`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
open PTX TensorDescriptor MmaFoot

/-- The linear (unswizzled) byte of feature `f` of head `h` of the tile at `B`. -/
def linear (B h f z : Nat) : Nat := B + 128 * h + 8192 * (f / 64) + 2 * (f % 64) + z

/-- The query feature of contraction element `t` of the A row `r` of QK MMA `k`. -/
def feature (k r t : Nat) : Nat := 128 * (k / 4) + 64 * (r / 64) + 16 * (k % 4) + t

/-- **The shared byte a query copy reads**: source byte `2 t + z` of row `r` of copy `k`. -/
theorem qcopy_byteLoc {B k cta r t z : Nat} (hr : r < 128) (ht : t < 16) (hz : z < 2) :
    TcCopy.byteLoc .s128x256b (keyDesc B k) cta (32 * r + 2 * t + z) =
      some ⟨.shared, cta, TensorSwizzle.offset .b128 0 (linear B (r % 64) (feature k r t) z)⟩ := by
  have h1 : (32 * r + 2 * t + z) / 32 = r := by omega
  have h2 : (32 * r + 2 * t + z) % 32 = 2 * t + z := by omega
  have hlim : 32 * r + 2 * t + z < 4096 := by omega
  simp [TcCopy.byteLoc, TcCpShape.sourceBytes, TcCpShape.rowBytes, TcCpShape.rows, hlim, h1, h2,
    keyDesc, TcShared.byteAddress, TcShared.linear, TcShared.Swizzle.sectors, linear, feature,
    qkDelta, TcShared.Swizzle.offset]
  congr 1
  omega

/-- The query map. -/
abbrev qMap (P : Params) : Σ n, Descriptor n :=
  ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩

/-- A load through the query map has a 64-column, 64-row, two-byte, 128-byte swizzled box. -/
theorem q_shape (P : Params) :
    TensorTile.count (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass).box 0 =
        64 ∧
      TensorTile.rows (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass).box =
        64 ∧
      (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass).format.bytes = 2 ∧
      (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass).swizzle = .b128 := by
  norm_num [mapQ, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, Fin.cases, Format.bytes]

/-- A slot a query load writes is in the 64 by 64 two-byte box. -/
theorem q_bounds {P : Params} {s : TensorCopy.Spec} {x y z : Nat} {l : Loc}
    (hmap : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) = qMap P)
    (h : TensorCopy.writeLoc s x y z = some l) : x < 64 ∧ y < 64 ∧ z < 2 := by
  obtain ⟨hx, hy, hz⟩ := TensorCopy.writeLoc_bounds h
  rcases s with ⟨⟨o, d, org, sb, rw⟩, mb, f1, f2⟩
  simp only [qMap] at hmap hx hy hz
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hmap
  cases hd
  obtain ⟨hc0, hr0, hb0, -⟩ := q_shape P
  rw [hc0] at hx
  rw [hr0] at hy
  rw [hb0] at hz
  exact ⟨hx, hy, hz⟩

/-- **The shared byte of a query load's slot**: the swizzled linear byte of head `y`, feature
`64 a + x` of the tile at `S` (`S` a multiple of 128). -/
theorem q_writeLoc {P : Params} {s : TensorCopy.Spec} {a cta S x y z : Nat}
    (hmap : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) = qMap P)
    (hsb : s.sharedBase = ⟨.shared, cta, S + 8192 * a⟩) (hS : S % 128 = 0)
    (hx : x < 64) (hy : y < 64) (hz : z < 2) :
    TensorCopy.writeLoc s x y z =
      some ⟨.shared, cta, TensorSwizzle.offset .b128 0 (linear S y (64 * a + x) z)⟩ := by
  rcases s with ⟨⟨o, d, org, sb, rw⟩, mb, f1, f2⟩
  simp only [qMap] at hmap hsb
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hmap
  cases hd
  obtain ⟨hc0, hr0, hb0, hsw⟩ := q_shape P
  have hbase : (S + 8192 * a) % 128 = 0 := by omega
  unfold TensorCopy.writeLoc TensorTransfer.slotAt
  rw [dite_eq_left (by rw [hc0]; exact hx), dite_eq_left (by rw [hr0]; exact hy),
    dite_eq_left (by rw [hb0]; exact hz)]
  simp only [Option.map_some, TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, hc0, hb0, hsw, TensorTile.swizzleWidth, hsb]
  rw [← TensorSwizzle.offset_add_base .b128 (S + 8192 * a) _ hbase]
  congr 3
  simp only [linear, Nat.reduceMul, max_self]
  omega

/-- **The global byte of a query load's slot**: byte `z` of element `(e, q, y, 64 a + x)` of the
`(b, s_q, 64, 512)` bf16 view, for a box at origin `(64 a, 0, q, e)`. -/
theorem q_readLoc {P : Params} {s : TensorCopy.Spec} {a cx cy : Nat} (hcx : cx < P.s_q)
    (hcy : cy < P.b) (ha : a < 8)
    (hmap : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) = qMap P)
    (horg : BoxOrigin s.origin [64 * a, 0, cx, cy]) (hr : s.rows = none)
    {x y z : Nat} (hx : x < 64) (hy : y < 64) (hz : z < 2) :
    TensorCopy.readLoc s x y z = some ⟨.global, 0,
      P.qBase + 2 * (((cy * P.s_q + cx) * 64 + y) * 512 + (64 * a + x)) + z⟩ := by
  rcases s with ⟨⟨o, d, org, sb, rw⟩, mb, f1, f2⟩
  simp only [qMap] at hmap horg hr
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hmap
  cases hd
  subst hr
  obtain ⟨hc0, hr0, hb0, hsw⟩ := q_shape P
  have h0 : org 0 = ((64 * a : Nat) : Int) := by simpa using horg 0
  have h1 : org 1 = 0 := by simpa using horg 1
  have h2 : org 2 = cx := by simpa using horg 2
  have h3 : org 3 = cy := by simpa using horg 3
  obtain ⟨slot, hsl, hs1, hs2, hs3⟩ : ∃ slot : TensorTransfer.Slot
      (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass),
      TensorTransfer.slotAt (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass)
        x y z = some slot ∧ slot.1.val = x ∧ slot.2.1.val = y ∧ slot.2.2.val = z := by
    unfold TensorTransfer.slotAt
    rw [dite_eq_left (by rw [hc0]; exact hx), dite_eq_left (by rw [hr0]; exact hy),
      dite_eq_left (by rw [hb0]; exact hz)]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  have hco : TensorTransfer.coord
      (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass) org none slot =
      ![((64 * a + x : Nat) : Int), (y : Int), (cx : Int), (cy : Int)] := by
    have hmod : y % 64 = y := Nat.mod_eq_of_lt hy
    have hdiv : y / 64 = 0 := Nat.div_eq_of_lt hy
    funext i
    fin_cases i <;>
      simp [TensorTransfer.coord, TensorTransfer.index, TensorTile.coord, TensorTile.indexOf,
        TensorTile.unflatten, TensorTile.count, TensorTile.step, mapQ, encodeTiled, Fin.cases,
        h0, h1, h2, h3, hs1, hs2, hmod, hdiv]
    all_goals rfl
  have hga : TensorTransfer.globalAddress
      (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass) org none slot =
      some (P.qBase + 2 * (((cy * P.s_q + cx) * 64 + y) * 512 + (64 * a + x)) + z) := by
    unfold TensorTransfer.globalAddress
    rw [hco, hs3]
    have hin : TensorAddress.InBounds (geometry
        (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass))
        ![((64 * a + x : Nat) : Int), (y : Int), (cx : Int), (cy : Int)] := by
      intro i
      fin_cases i <;> simp [geometry, mapQ, encodeTiled] <;> omega
    unfold TensorAddress.lookup
    rw [ite_eq_left ⟨hin, by simp [geometry, mapQ, encodeTiled, Format.bytes]; omega⟩]
    congr 1
    simp [TensorAddress.byteAddress, geometry, mapQ, encodeTiled, Fin.sum_univ_succ, Fin.cases,
      Format.bytes]
    rw [show (64 * (a : Int) + x).toNat = 64 * a + x by omega]
    ring
  unfold TensorCopy.readLoc TensorTransfer.sourceLoc
  rw [hsl]
  simp only [bind, Option.bind, hga]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
