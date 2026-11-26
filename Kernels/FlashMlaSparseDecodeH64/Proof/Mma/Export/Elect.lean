-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Lemmas.Kernel.ElectSource
import Lemmas.Flow.ElectActor

@[expose] public section

/-! # One MMA lane per CTA

`mmaOne`: two lanes of one CTA with events at MMA pcs after the election are lanes of warp 4
that each won the election at pc 1853 with the full mask (`mma_won`, `Common/MmaWon.lean`), so
they have one lane index (`elect_winner`) and are one lane. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **`MmaOne`**: one MMA lane per CTA. -/
theorem mmaOne (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MmaOne L X := by
  intro g g' k k' e e' he he' hu hu' hon hon' hc
  obtain ⟨⟨hw, -, hr⟩, hlo⟩ := hon
  obtain ⟨⟨hw', -, hr'⟩, hlo'⟩ := hon'
  obtain ⟨j, -, inst, hj⟩ := mma_won hp hX hFw he hu ⟨hlo, hr⟩
  obtain ⟨j', -, inst', hj'⟩ := mma_won hp hX hFw he' hu' ⟨hlo', hr'⟩
  have hb := hp.block
  have hx := tidOf_x_eq hp g
  have hx' := tidOf_x_eq hp g'
  simp only [MbarRow.warp] at hw hw'
  have hs : SameWarp L g g' :=
    ⟨⟨Frame.lt_of_get hX he, Frame.lt_of_get hX he', hc⟩, by rw [hb]; omega⟩
  exact sameWarp_eq_of_lane_eq hs (elect_winner hX (e := (g, j)) (f := (g', j')) hj hj' hs)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
