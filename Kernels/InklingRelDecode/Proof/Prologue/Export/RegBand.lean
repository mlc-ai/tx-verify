-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Time
public import Kernels.InklingRelDecode.Proof.Prologue.Requests

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX

public theorem regBand (d) :
    Prologue.time d ≤ 283 ∧ (Prologue.requestPhase d.site = 0 → Prologue.time d = 100) ∧
      (Prologue.requestPhase d.site = 1 → 100 < Prologue.time d) := by
  have card : Prologue.allSites.length = 183 := by decide +kernel
  have head : Prologue.allSites = Prologue.Site.sMax :: Prologue.allSites.tail := by
    decide +kernel
  have le := List.idxOf_le_length (a := d.site) (l := Prologue.allSites)
  refine ⟨?_,fun h => ?_,fun h => ?_⟩
  · unfold Prologue.time Lib.Slots.prologue; omega
  · have : d.site = .sMax := by
      by_contra ne
      simp [Prologue.requestPhase, ne] at h
    unfold Prologue.time Lib.Slots.prologue
    rw [this, head]; simp
  · have ne : d.site ≠ .sMax := by
      intro e; simp [Prologue.requestPhase, e] at h
    unfold Prologue.time Lib.Slots.prologue
    have : 0 < Prologue.allSites.idxOf d.site := by
      rw [head]; simp [Ne.symm ne]
    omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
