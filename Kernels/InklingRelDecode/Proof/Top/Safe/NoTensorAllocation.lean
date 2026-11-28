-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.KvBox
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- The box origin of the 20 tensor loads (12 preloads and 8 worker copies, all through the one
map) is inside it: each is the copy of a box of a slab that exists. The kernel has no tensor store
and no prefetch. -/
theorem Safe.noTensorAllocation (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ¬ TensorAllocationUnsafe L m X := by
  rintro ⟨i,⟨a,s,⟨pc,hi⟩,-,oob,-⟩|⟨a,s,⟨pc,hi⟩,-⟩|⟨a,s,⟨pc,hi⟩,-⟩⟩
  · obtain ⟨r, sl, kvh, isV, hh, dst, bar, hr, hs, hk, hV, hH, -, rfl⟩ :=
      Protocol.Shared.kv_copy_form hp hX hf hi
    exact Lib.kvbox_noOob hp hr hs (by unfold kvHeads at hk; omega) hV hH _ _ _ oob
  · exact Lib.no_tensorStore hX hi
  · exact Lib.no_tensorPrefetch hX hi

end PTX.Kernels.InklingRelDecode.Proof.Top
