-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasVal

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof

/-- **A bias load returns a bf16 number**: the element of the relative logits it reads. -/
public theorem bias_half {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.rd a bs⟩)
    (site : (∃ j : Fin 64, pc = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc = 1124 + 2 * j.val) :
    ∃ x, rebuild 3 bs = .ok (Value.float .bf16 x) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hv⟩ := bias_val hp hX hf he site
  exact ⟨_, hv⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
