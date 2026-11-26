-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Origin
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Origin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out

@[expose] public section

/-! # The box origin of the query loads and the output stores

A tensor load through the query map is a query load of the MMA warp (a gather of the TMA warp has
a cache map, of rank one): its box starts at column `64 c` of the query row and batch of its CTA
(`tensor_load_origin`). A tensor store is an output store of warp 0 or 1 of warpgroup 0: its box
starts at column `128 w + col` of the query row and batch of its CTA (`tensor_store_origin`,
without undefined behaviour; the store's pc is its chunk's). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The origin of a query load**: a tensor load through the query map is a tile load of the
origin `(64 c, 0, %ctaid.x, %ctaid.y)` for a `c < 8`, of the lane's CTA. -/
theorem tensor_load_origin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k a : Nat} {s : TensorCopy.Spec} (h : X.TensorIssue (g, k) a s)
    (hq : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩) :
    s.rows = none ∧ ∃ c < 8, BoxOrigin s.origin [64 * c, 0, ctaidX L g, ctaidY L g] := by
  obtain ⟨pc, he⟩ := h
  have hpc : 1850 ≤ pc ∧ pc < 2332 := load_pc hX he rfl
  rcases tensor_place hp hX hFw he (.inl ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  · simp only [StartupAt] at h; omega
  · simp only [Wg0At] at h; omega
  · simp only [Wg1At] at h; omega
  · exact mma_loadOrigin hp hX hFw he h rfl
  · obtain ⟨d0, -, hK⟩ := tma_gather_map hp hX hFw he h rfl
    have h3 : s.outer = 3 := congrArg Sigma.fst hq
    rcases hK with hK | ⟨-, hK⟩ <;> have h1 : s.outer = 1 := congrArg Sigma.fst hK <;> omega
  · simp only [IndexAt] at h; omega
  · simp only [DequantAt] at h; omega

/-- **The origin of an output store**: a tensor store is a tile store of the origin
`(128 w + col, 0, %ctaid.x, %ctaid.y)` of a lane of warp `w < 2` of warpgroup 0, with `col` of its
chunk (`0, 64, 256, 320`). -/
theorem tensor_store_origin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {g k a : Nat} {s : TensorStore.Spec}
    (h : X.TensorStoreIssue (g, k) a s) :
    MbarRow.warp L g < 2 ∧ s.rows = none ∧ ∃ c < 4,
      X.get (g, k) = some ⟨[1358, 1516, 1673, 1831].getD c 0, .tensorStore a s⟩ ∧ BoxOrigin s.origin
        [128 * MbarRow.warp L g + [0, 64, 256, 320].getD c 0, 0, ctaidX L g, ctaidY L g] := by
  obtain ⟨pc, he⟩ := h
  have hpc : 103 ≤ pc ∧ pc < 1842 := store_pc hX he rfl
  have hw2 := (wg0_outIssue hp hX hFw hnu ⟨pc, he⟩).1
  rcases tensor_place hp hX hFw he (.inr ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  · simp only [StartupAt] at h; omega
  · obtain ⟨hr, c, hc, hpcc, ho⟩ := wg0_storeOrigin hp hX hFw he h rfl hw2
    have hpcc' : pc = [1358, 1516, 1673, 1831].getD c 0 := hpcc
    subst hpcc'
    exact ⟨hw2, hr, c, hc, he, ho⟩
  all_goals
    simp only [Wg1At, MmaAt, TmaAt, IndexAt, DequantAt] at h
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
