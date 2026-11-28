-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs

@[expose] public section

/-! # ERR-BARRIER-MISMATCH: the lanes of a warp agree at each barrier

The safety class of Core's `Unsafe` this file owns (`BarMismatch`), proved from the named-barrier
rows and the barrier ordinals (inputs `bar`, `barOrd` of `Top.Inputs`): two lanes of one warp at
their `k`-th barrier event name one barrier with one count (`bar_same`), and no barrier event is a
`bar.arrive` (`bar_sync`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-BARRIER-MISMATCH**: the lanes of a warp agree on the barrier, count and form. -/
theorem Safe.noBarMismatch (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ BarMismatch L X := by
  have hR := hIn.bar hp X hX hFw
  rintro (⟨g, h, i, j, id, id', cnt, cnt', pc, pc', hw, hi, hj, hk, hne⟩ |
    ⟨g, h, i, j, id, id', cnt, cnt', md', pc, pc', hw, hi, hj, -, -⟩)
  · have hs := bar_same hp hR (hIn.barOrd hp X hX hFw) hw hi hj rfl rfl hk
    simp only [Kind.bar.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    simp at hne
  · obtain ⟨⟨hg, -⟩, -⟩ := hw
    cases bar_sync hR hg hi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
