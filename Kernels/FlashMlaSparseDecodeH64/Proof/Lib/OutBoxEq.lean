-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutBox

@[expose] public section

/-! # The source byte of an output slot, as an equation

`outBox_sharedLoc` (`Lib/OutBox.lean`) only names the parts of the source address; here the slot
at column `x`, row `h` and byte `z` of an output box at a 1024-byte aligned base reads exactly
`base + 128 h + 16 ((x / 8) ^^^ h % 8) + 2 (x % 8) + z` (`outBox_sharedLoc_eq`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- The O map's box has 64 columns. -/
theorem mapO_count (base sH sS sB sq bt : Nat) (fill : Fill) (cls : AllocationClass) :
    TensorTile.count (mapO base sH sS sB sq bt fill cls).box 0 = 64 := by
  simp [mapO, encodeTiled, TensorTile.count, TensorTile.step]

/-- The O map's box has 64 rows. -/
theorem mapO_rows (base sH sS sB sq bt : Nat) (fill : Fill) (cls : AllocationClass) :
    TensorTile.rows (mapO base sH sS sB sq bt fill cls).box = 64 := by
  simp [mapO, encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]

/-- The O map's elements have two bytes. -/
theorem mapO_bytes (base sH sS sB sq bt : Nat) (fill : Fill) (cls : AllocationClass) :
    (mapO base sH sS sB sq bt fill cls).format.bytes = 2 := by
  simp [mapO, encodeTiled, Format.bytes]

/-- **The source byte of an output store's slot**, explicitly. -/
theorem outBox_sharedLoc_eq {b : TensorBox} {base sH sS sB sq bt : Nat} {fill : Fill}
    {cls : AllocationClass}
    (hd : (⟨b.outer, b.descriptor⟩ : Σ n, Descriptor n) =
      ⟨3, mapO base sH sS sB sq bt fill cls⟩)
    (hal : b.sharedBase.addr % 1024 = 0) (slot : TensorTransfer.Slot b.descriptor) :
    b.sharedLoc slot = { b.sharedBase with addr := b.sharedBase.addr +
      (128 * slot.2.1.val + 16 * ((slot.1.val / 8) ^^^ (slot.2.1.val % 8)) +
        2 * (slot.1.val % 8) + slot.2.2.val) } := by
  obtain ⟨outer, desc, origin, sb, rows⟩ := b
  simp only [Sigma.mk.injEq] at hd
  obtain ⟨rfl, hd⟩ := hd
  cases hd
  have hc := mapO_count base sH sS sB sq bt fill cls
  have hr := mapO_rows base sH sS sB sq bt fill cls
  obtain ⟨⟨x, hx⟩, ⟨h, hh⟩, ⟨y, hy⟩⟩ := slot
  rw [hc] at hx
  rw [hr] at hh
  have hy2 : y < 2 := by simpa [mapO, encodeTiled, Format.bytes] using hy
  have hp : TensorTile.count (mapO base sH sS sB sq bt fill cls).box 0 *
      (mapO base sH sS sB sq bt fill cls).format.bytes ⊔
        TensorTile.swizzleWidth (mapO base sH sS sB sq bt fill cls).swizzle = 128 := by
    simp [mapO, encodeTiled, TensorTile.count, TensorTile.step, Format.bytes,
      TensorTile.swizzleWidth]
  have hsw : (mapO base sH sS sB sq bt fill cls).swizzle = .b128 := by
    simp [mapO, encodeTiled]
  have hby : (mapO base sH sS sB sq bt fill cls).format.bytes = 2 := by
    simp [mapO, encodeTiled, Format.bytes]
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes]
  rw [hp, hsw, hby, swizzle128_row hal hx hy2]

/-- **A slot of an output map's descriptor**: column `x < 64`, row `y < 64`, byte `z < 2` is
in range. -/
theorem outDesc_slot {o : Nat} {d : Descriptor o} {base sH sS sB sq bt : Nat} {fill : Fill}
    {cls : AllocationClass}
    (hd : (⟨o, d⟩ : Σ n, Descriptor n) = ⟨3, mapO base sH sS sB sq bt fill cls⟩)
    {x y z : Nat} (hx : x < 64) (hy : y < 64) (hz : z < 2) :
    ∃ slot : TensorTransfer.Slot d, slot.1.val = x ∧ slot.2.1.val = y ∧ slot.2.2.val = z ∧
      TensorTransfer.slotAt d x y z = some slot := by
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hd
  cases hd
  have hc := mapO_count base sH sS sB sq bt fill cls
  have hr := mapO_rows base sH sS sB sq bt fill cls
  have hb := mapO_bytes base sH sS sB sq bt fill cls
  have h1 : x < TensorTile.count (mapO base sH sS sB sq bt fill cls).box 0 := by omega
  have h2 : y < TensorTile.rows (mapO base sH sS sB sq bt fill cls).box := by omega
  have h3 : z < (mapO base sH sS sB sq bt fill cls).format.bytes := by omega
  exact ⟨⟨⟨x, h1⟩, ⟨y, h2⟩, ⟨z, h3⟩⟩, rfl, rfl, rfl, by
    simp only [TensorTransfer.slotAt, h1, h2, h3, dite_true]⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
