-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.IpTmZero
public import Kernels.InklingRelDecode.Proof.Result.SwStore

@[expose] public section

/-!
# `Rs.SmBaseZero`

Every softmax state's Tensor Memory base word `Sm.D.e.tm` is 0: the common start's load of the base
word returns the zero word (`Interface.BaseWordRead`, the premise `SO.BaseWordZero`, which
`Interface.baseWordRead_of` proves from the allocation's store, `allocWordZero_w`, on the tracking
up to the base-word stops), and the machine carries the word unchanged to the softmax region
(`Interface.tmz_inv`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Rs.SmBaseZero Q L X`**, from the base word's read. -/
theorem smBaseZero (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) : SmBaseZero Q L X :=
  fun hg hσ => smBaseZero_of hpre hX hf hb hg hσ

end
end PTX.Kernels.InklingRelDecode.Proof.Rs
