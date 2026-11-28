-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-! # ERR-CTA-BARRIER: no CTA barrier arrival faults

The safety class of Core's `Unsafe` this file owns (`CtaBarFault`), by the library's
`NamedBar.no_duplicate_arrival`: the arrivals of one CTA on one barrier pass one count (`bar_cnt`:
the count is the barrier's, `barCnt`), and no arrival is a `bar.arrive` (`bar_sync`), so no
generation is left open by one; both from the named-barrier rows (input `bar` of `Top.Inputs`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-CTA-BARRIER**: no CTA barrier arrival faults. -/
theorem Safe.noCtaBar (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ CtaBarFault L X := by
  have hR := hIn.bar hp X hX hFw
  refine NamedBar.no_duplicate_arrival hX
    (fun ⟨g, k⟩ ⟨h, j⟩ id cnt cnt' pc pc' m m' _ he hf => ?_)
    (fun ⟨g, k⟩ key pc cnt j ev _ he _ _ _ => ?_)
  · rw [bar_cnt hR (Frame.lt_of_get hX he) he, bar_cnt hR (Frame.lt_of_get hX hf) hf]
  · cases bar_sync hR (Frame.lt_of_get hX he) he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
