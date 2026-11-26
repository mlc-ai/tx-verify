-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutBoxEq
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutDest
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin

@[expose] public section

/-! # An in-range slot of an output store has a destination

A tile store through the output map with the origin `(x₀, 0, q, e)`, `x₀ + 64 ≤ 512`, `q < s_q`,
`e < b` (`tile_inBounds`) writes each slot `(x, y, z)` of its box (`x, y < 64`, `z < 2`):
`writeLoc` is a location (`out_writeLoc_some`), and `out_dest` names it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- **Every in-range slot of an in-bounds output store has a destination.** -/
theorem out_writeLoc_some {s : TensorStore.Spec} {base sq b : Nat} {fill : Fill}
    {cls : AllocationClass}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) =
      ⟨3, mapO base 512 32768 (sq * 32768) sq b fill cls⟩)
    {x₀ q e : Nat} (ho : BoxOrigin s.origin [x₀, 0, q, e]) (hr : s.rows = none)
    (hx₀ : x₀ + 64 ≤ 512) (hq : q < sq) (he : e < b) {x y z : Nat} (hx : x < 64) (hy : y < 64)
    (hz : z < 2) : ∃ l, TensorStore.writeLoc s x y z = some l := by
  obtain ⟨⟨outer, desc, org, sb, rows⟩, red⟩ := s
  simp only at hd ho hr
  subst hr
  obtain ⟨slot, -, -, -, hsl⟩ := outDesc_slot hd hx hy hz
  have hob := tile_inBounds hd hx₀ hq he ho
  have hin : TensorAddress.InBounds (geometry desc) (TensorTransfer.coord desc org none slot) := by
    by_contra hn
    exact hob ⟨slot, hn⟩
  obtain ⟨rfl, hd'⟩ := Sigma.mk.inj_iff.mp hd
  cases hd'
  have hby : slot.2.2.val <
      (geometry (mapO base 512 32768 (sq * 32768) sq b fill cls)).elementBytes := by
    simp only [geometry, mapO, encodeTiled, Format.bytes]
    have := slot.2.2.isLt
    simpa [mapO, encodeTiled, Format.bytes] using this
  simp only [TensorStore.writeLoc, hsl, Option.bind_some, TensorStore.destination,
    TensorBox.globalAddress, TensorTransfer.globalAddress, TensorAddress.lookup, hby,
    and_true]
  split_ifs with hc
  · exact ⟨_, rfl⟩
  · exact absurd hin hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
