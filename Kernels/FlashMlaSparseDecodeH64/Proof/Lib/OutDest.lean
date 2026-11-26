-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The global byte of an output store's slot

A tensor store through the output map (`mapO`) whose box has the origin `(x₀, 0, q, e)` writes
its slot at column `x`, row `y`, byte `z` to byte `z` of the element `(e, q, y, x₀ + x)` of the
`(b, s_q, 64, 512)` view at the map's base (`out_dest`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- A byte of the query or output view, past the map's origin, is one of its `2 b s_q 64 512`. -/
theorem view_lt {b sq e q hh t y : Nat} (he : e < b) (hq : q < sq) (hh' : hh < 64)
    (ht : t < 512) (hy : y < 2) :
    2 * (((e * sq + q) * 64 + hh) * 512 + t) + y < 2 * b * sq * 64 * 512 := by
  have h1 : e * sq + q + 1 ≤ b * sq := by
    calc e * sq + q + 1 ≤ e * sq + sq := by omega
      _ = (e + 1) * sq := by ring
      _ ≤ b * sq := Nat.mul_le_mul_right _ he
  have h2 : 2 * b * sq * 64 * 512 = 65536 * (b * sq) := by ring
  generalize e * sq + q = x at h1
  rw [h2]
  omega

/-- The issuer of a memory access: a thread's event or one stage of an asynchronous event. -/
abbrev Accessor : Type := AsyncCopy.Ref

/-- **A cache row's byte is inside the cache**. -/
theorem kv_lt {nb bs r y : Nat} (hr : r < nb * (bs / 528)) (hy : y < 528) :
    r * 528 + y < nb * bs := by
  have h1 : (r + 1) * 528 ≤ nb * (bs / 528) * 528 := Nat.mul_le_mul_right _ hr
  have h2 : nb * (bs / 528) * 528 ≤ nb * bs := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self bs 528)
  omega

/-- **The destination of an output store's slot**. -/
theorem out_dest {s : TensorStore.Spec} {base sq b : Nat} {fill : Fill} {cls : AllocationClass}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) =
      ⟨3, mapO base 512 32768 (sq * 32768) sq b fill cls⟩)
    {x₀ q e : Nat} (ho : BoxOrigin s.origin [x₀, 0, q, e]) (hr : s.rows = none)
    {x y z : Nat} {l : Loc} (h : TensorStore.writeLoc s x y z = some l) :
    x < 64 ∧ y < 64 ∧ z < 2 ∧ x₀ + x < 512 ∧ q < sq ∧ e < b ∧
      l = ⟨.global, 0, base + 2 * (((e * sq + q) * 64 + y) * 512 + (x₀ + x)) + z⟩ := by
  obtain ⟨⟨outer, desc, org, sb, rows⟩, red⟩ := s
  simp only at hd ho hr
  subst hr
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hd
  cases hd
  simp only [TensorStore.writeLoc, TensorStore.destination, TensorBox.globalAddress,
    TensorTransfer.globalAddress, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨slot, hsl, addr, hlk, rfl⟩ := h
  have hv : slot.1.val = x ∧ slot.2.1.val = y ∧ slot.2.2.val = z := by
    unfold TensorTransfer.slotAt at hsl
    split_ifs at hsl
    cases hsl
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hx, hy, hz, hco⟩ := tile_coord (d := mapO base 512 32768 (sq * 32768) sq b fill cls)
    (base := base) (sq := sq) (b := b) (fill := fill) (cls := cls) (sH := 512) (sS := 32768)
    (sB := sq * 32768) rfl ho slot
  obtain ⟨e', he, q', hq, y', hy', t, ht, z', hz', c0, c1, c2, c3, c4, ha⟩ :=
    tiled_coord (d := mapO base 512 32768 (sq * 32768) sq b fill cls) rfl hlk
  rw [hco] at c0 c1 c2 c3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] at c0 c1 c2 c3
  obtain ⟨hx', hy'', hz''⟩ := hv
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  have et : t = x₀ + x := by omega
  have ey : y' = y := by omega
  have eq : q' = q := by omega
  have ee : e' = e := by omega
  have ez : z' = z := by omega
  simp only [Loc.mk.injEq, true_and]
  rw [ha, et, ey, eq, ee, ez]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
