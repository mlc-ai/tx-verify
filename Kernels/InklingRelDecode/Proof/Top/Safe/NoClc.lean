-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noClc {X : Execution} (hX : Consistent L kernel Assumptions.all m X) :
    ¬ ClcUnsafe L X := by
  rintro ⟨_, _, _, _, _, _, ⟨pc, he⟩, _⟩
  exact Lib.no_clc hX he

end PTX.Kernels.InklingRelDecode.Proof.Top
