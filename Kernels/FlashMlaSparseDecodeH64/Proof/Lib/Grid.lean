-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The CTA indices of the kernel's grid

The launch is the kernel's `(s_q, b, 1)` grid of single-CTA clusters (`Pre.clusterSize`,
`Pre.clusterPlaces`), so CTA `c` has block index `(c % s_q, c / s_q % b, 0)` (`ctaidOf_eq`, the
old tree's `Interface/LaunchTest.lean` proof) and every thread's `%ctaid.x` and `%ctaid.y` are below
`s_q` and `b`: the CTA-side premises of the index warp's invariant and sources. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

theorem ctaidOf_eq (hpre : Pre P L mem0) (c : Nat) :
    L.ctaidOf c = ⟨c % P.s_q, c / P.s_q % P.b, 0⟩ := by
  have hsz : L.clusterSize.val = 1 := hpre.clusterSize
  have hloc : ∀ (n k cc : Nat), L.locate n k cc = (k + cc, 0) := by
    intro n k cc
    rw [Launch.locate_regular (fun k => by rw [hpre.clusterPlaces, hsz]; rfl), hsz,
      Nat.div_one, Nat.mod_one]
  have hco : L.clusterOfCta c = c := by
    simp only [Launch.clusterOfCta, hloc, Nat.zero_add]
  have hrk : L.rankOfCta c = 0 := by
    simp only [Launch.rankOfCta, hloc]
  have hplace : L.clusterPlaces c = ⟨⟨c % P.s_q, c / P.s_q % P.b, 0⟩, ⟨1, 1, 1⟩,
      ⟨c % P.s_q, c / P.s_q % P.b, 0⟩, ⟨P.s_q, P.b, 1⟩⟩ := by
    rw [hpre.clusterPlaces]
    rfl
  simp only [Launch.ctaidOf, Launch.placeOf, hco, hplace, Launch.clusterCtaidOf, hrk,
    Dim3.coord]
  simp only [Nat.mod_one, Nat.div_one, Nat.zero_add, Nat.add_zero]

/-- **Every thread's CTA is a query row of the batch.** -/
theorem ctaid_lt (hpre : Pre P L mem0) (g : Nat) : ctaidX L g < P.s_q ∧ ctaidY L g < P.b := by
  have h1 := hpre.sqPos; have h2 := hpre.bPos; have h3 := hpre.sqLt; have h4 := hpre.bLt
  simp only [ctaidX, ctaidY, ctaidOf_eq hpre]
  constructor
  · rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt (ctaOf L g) h1; omega)]; exact Nat.mod_lt _ h1
  · rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt (ctaOf L g / P.s_q) h2; omega)]
    exact Nat.mod_lt _ h2

/-- **A launched thread's CTA is its query row of its batch**:
`ctaOf = %ctaid.y * s_q + %ctaid.x`. -/
theorem ctaOf_row (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    ctaOf L g = ctaidY L g * P.s_q + ctaidX L g := by
  have h1 := hpre.sqPos; have h2 := hpre.bPos; have h3 := hpre.sqLt; have h4 := hpre.bLt
  have hblk : 0 < L.block := by rw [hpre.block]; decide
  have hc : ctaOf L g < P.s_q * P.b := by
    rw [← hpre.grid]
    exact (Nat.div_lt_iff_lt_mul hblk).mpr hg
  have hb : ctaOf L g / P.s_q < P.b := (Nat.div_lt_iff_lt_mul h1).mpr (by rwa [Nat.mul_comm])
  have hx : ctaOf L g % P.s_q % 2 ^ 32 = ctaOf L g % P.s_q :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ h1) (by omega))
  have hy : ctaOf L g / P.s_q % P.b % 2 ^ 32 = ctaOf L g / P.s_q := by
    rw [Nat.mod_eq_of_lt hb]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [ctaidX, ctaidY, ctaidOf_eq hpre]
  rw [hx, hy]
  exact (Nat.div_add_mod' _ _).symm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
