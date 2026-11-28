-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTensorStore {X : Execution} (hX : Consistent L kernel Assumptions.all m X) :
    ¬ TensorStoreUnsafe Assumptions.all X := by
  rintro (⟨i, o, -, -, -, hio, -⟩ | ⟨i, s, -, -, ⟨pc, hi⟩, -⟩)
  · obtain ⟨⟨addr, pc, hi⟩, -⟩ := hX.store i o hio
    exact Lib.no_tensorStore hX hi
  · exact Lib.no_copy hX hi

end PTX.Kernels.InklingRelDecode.Proof.Top
