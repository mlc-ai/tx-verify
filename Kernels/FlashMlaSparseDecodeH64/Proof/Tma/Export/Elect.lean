-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Tma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Lemmas.Kernel.ElectSource
import Lemmas.Flow.ElectActor

@[expose] public section

/-! # One TMA lane per CTA

`tmaOne`: two lanes of one CTA with events at TMA pcs after the election are lanes of warp 5
that each won the election at pc 2165 with the full mask (`tma_won`, `Common/TmaWon.lean`), so
they have one lane index (`elect_winner`) and are one lane. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **`TmaOne`**: one TMA lane per CTA. -/
theorem tmaOne (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmaOne L X := by
  intro g g' k k' e e' he he' hu hu' hon hon' hc
  obtain ⟨⟨hw, -, hr⟩, hlo⟩ := hon
  obtain ⟨⟨hw', -, hr'⟩, hlo'⟩ := hon'
  obtain ⟨j, -, inst, hj⟩ := tma_won hp hX hFw he hu ⟨hlo, hr⟩
  obtain ⟨j', -, inst', hj'⟩ := tma_won hp hX hFw he' hu' ⟨hlo', hr'⟩
  have hx := tidOf_x_eq hp g
  have hx' := tidOf_x_eq hp g'
  simp only [MbarRow.warp] at hw hw'
  have hs : SameWarp L g g' :=
    ⟨⟨Frame.lt_of_get hX he, Frame.lt_of_get hX he', hc⟩, by rw [hp.block]; omega⟩
  exact sameWarp_eq_of_lane_eq hs (elect_winner hX (e := (g, j)) (f := (g', j')) hj hj' hs)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
