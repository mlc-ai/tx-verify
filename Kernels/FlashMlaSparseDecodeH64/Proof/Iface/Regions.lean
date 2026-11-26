-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The kernel's shared-memory regions: vocabulary

The byte layout of `SharedMemoryPlan` (`config.h:141-172`, `Data/Barriers.lean`), as offsets from
the dynamic shared base. The `u` union (bytes 0 to 204800) has two members: the `kv` member, two
dequantized `bf16` tiles of 64 × 512 (`dequant b` at `65536 b`) and two raw gather4 blocks of
64 rows of 576 bytes (`raw b` at `131072 + 36864 b`), and the `qo` member, the query tile and the
output staging buffer, which the kernel reuses inside the dequantized tiles' bytes (the query copy
source, then the output staging; the protocol layer orders the uses). The map below names the
`kv` member; the regions after the union are used for one purpose each.

| region | offset | bytes |
| - | - | - |
| `dequant b` | `65536 b` | 65536 |
| `raw b` | `131072 + 36864 b` | 36864 |
| `pExchange` | 204800 | 16384 |
| `rowMax` | 221184 | 512 |
| `tokenValid` | 221696 | 32 |
| `tmaCoord` | 221728 | 1024 |
| `tmemWord` | 222752 | 16 |
| `mbars` | 222768 | 184 |

`regionOf` names the region of a byte offset below 222952; `regionOf_cover` proves that the
region it names contains the offset (the regions cover `[0, 222952)` without gaps), and
`regionOf_lo` that a region's own bytes are named by it (no overlap). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **The named regions of the shared workspace.** -/
inductive Region where
  | dequant (b : Fin 2)
  | raw (b : Fin 2)
  | pExchange
  | rowMax
  | tokenValid
  | tmaCoord
  | tmemWord
  | mbars
  deriving DecidableEq, Repr

namespace Region

/-- The first byte, from the dynamic shared base. -/
def lo : Region → Nat
  | dequant b => 65536 * b.val
  | raw b => 131072 + 36864 * b.val
  | pExchange => 204800
  | rowMax => 221184
  | tokenValid => 221696
  | tmaCoord => 221728
  | tmemWord => 222752
  | mbars => 222768

/-- The number of bytes. -/
def size : Region → Nat
  | dequant _ => 65536
  | raw _ => 36864
  | pExchange => 16384
  | rowMax => 512
  | tokenValid => 32
  | tmaCoord => 1024
  | tmemWord => 16
  | mbars => 184

/-- The byte offset `off` lies in the region. -/
def Mem (r : Region) (off : Nat) : Prop := r.lo ≤ off ∧ off < r.lo + r.size

/-- The end of the mapped workspace: the last mbarrier's word ends here. -/
def top : Nat := 222952

/-- All regions, in the order of their offsets. -/
def all : List Region :=
  [dequant 0, dequant 1, raw 0, raw 1, pExchange, rowMax, tokenValid, tmaCoord, tmemWord, mbars]

theorem mem_all (r : Region) : r ∈ all := by
  cases r
  all_goals first
    | decide
    | (rename_i b; revert b; decide)

/-- Every region fits the dynamic shared size. -/
theorem fits (r : Region) : r.lo + r.size ≤ sharedBytes := by
  have h : ∀ r ∈ all, r.lo + r.size ≤ sharedBytes := by decide
  exact h r (mem_all r)

end Region

/-- **The region of a byte offset** of the mapped workspace. -/
def regionOf (off : Nat) : Region :=
  if off < 65536 then .dequant 0
  else if off < 131072 then .dequant 1
  else if off < 167936 then .raw 0
  else if off < 204800 then .raw 1
  else if off < 221184 then .pExchange
  else if off < 221696 then .rowMax
  else if off < 221728 then .tokenValid
  else if off < 222752 then .tmaCoord
  else if off < 222768 then .tmemWord
  else .mbars

/-- **Cover**: every byte offset below `top` lies in the region `regionOf` names. -/
theorem regionOf_cover {off : Nat} (h : off < Region.top) : (regionOf off).Mem off := by
  unfold regionOf Region.Mem Region.top at *
  repeat' split
  all_goals simp only [Region.lo, Region.size, Fin.val_zero, Fin.val_one]
  all_goals omega

namespace Region

/-- **The regions are pairwise disjoint.** -/
theorem disjoint {r r' : Region} {off : Nat} (h : r.Mem off) (h' : r'.Mem off) : r = r' := by
  have hall : ∀ r ∈ all, ∀ r' ∈ all, r ≠ r' →
      r.lo + r.size ≤ r'.lo ∨ r'.lo + r'.size ≤ r.lo := by decide
  by_contra hne
  rcases hall r (mem_all r) r' (mem_all r') hne with hl | hl
  · exact absurd (Nat.lt_of_lt_of_le h.2 hl) (Nat.not_lt.mpr h'.1)
  · exact absurd (Nat.lt_of_lt_of_le h'.2 hl) (Nat.not_lt.mpr h.1)

/-- Every region ends by `top`. -/
theorem le_top (r : Region) : r.lo + r.size ≤ top := by
  have h : ∀ r ∈ all, r.lo + r.size ≤ top := by decide
  exact h r (mem_all r)

end Region

/-- **The LSE output's bytes**: a global access inside `[lseBase, lseBase + lseBytes P)`. -/
def LseIn (P : Params) (a : Acc) : Prop :=
  a.loc.space = .global ∧ P.lseBase ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ P.lseBase + lseBytes P

/-- The shared location of byte `off` of the workspace in CTA `cta`. -/
def wsLoc (L : Launch) (cta off : Nat) : Loc := ⟨.shared, cta, L.sharedBase + off⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
