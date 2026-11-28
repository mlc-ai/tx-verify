-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- The twelve preload copy sites: four per ring slot, in issue order. -/
abbrev preloadSites : List Nat := [211,217,226,231,253,259,268,273,295,301,310,315]

/-- The byte offset of each preload copy's 8192-byte box from `sharedBase + 16384 * half`: slot
`32768 * b`, the V tile (`98304`) for odd sites, and `8192` for the second pair. -/
def preloadOff (pc : Nat) : Nat :=
  [0,98304,8192,106496,32768,131072,40960,139264,65536,163840,73728,172032][preloadSites.idxOf pc]!

/-- Two preload boxes, each of a site and a half tile, that overlap are those of one site and
one half. -/
theorem preloadOff_apart {pc pc' : Nat} {h h' : Nat} (hp : pc ∈ preloadSites)
    (hp' : pc' ∈ preloadSites) (hh : h < 2) (hh' : h' < 2)
    (lo : 16384*h + preloadOff pc < 16384*h' + preloadOff pc' + 8192)
    (hi : 16384*h' + preloadOff pc' < 16384*h + preloadOff pc + 8192) : pc = pc' ∧ h = h' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hp'
  have hh2 : h = 0 ∨ h = 1 := by omega
  have hh2' : h' = 0 ∨ h' = 1 := by omega
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases hp' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases hh2 with rfl|rfl <;> rcases hh2' with rfl|rfl <;>
  first | exact ⟨rfl,rfl⟩ | (exfalso; revert lo hi; decide)

end PTX.Kernels.InklingRelDecode.Proof.Iface
