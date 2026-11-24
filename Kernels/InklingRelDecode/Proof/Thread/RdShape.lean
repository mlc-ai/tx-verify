-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSSync

@[expose] public section

/-!
# Event shapes of the softmax region: the wait after the rescale's load

`waitLdO`: `tcgen05.wait::ld` (the same instruction as the S tile's `waitLd`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **The wait for the O rescale's load**: `tcgen05.wait::ld`. -/
theorem shape_waitLdO (hb : L.block % 32 = 0) (hF : Fired L g d e (some u))
    (hs : d.site = .waitLdO) : e = ⟨evPc d.site, .tc .waitLd⟩ := by
  have hpc : d.site.pc = Flow.tmemWait_2 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_tmemWait_2) hF
  rw [hpc] at hf
  rw [fires_tcWaitLd hb hf, evPc, hpc]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
