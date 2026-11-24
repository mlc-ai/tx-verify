-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5WBfly
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5MBar

@[expose] public section

/-! # `StoreWord`: the scratch word of each warp, without the lockstep

`storeWord_all`: in every iteration of every CTA the lanes of each default warp store at `store10`
the value of one number that is not `+inf` (`Interface.Lk.storeWordB`, the butterfly minimum of
`alpha` over the warp, with the partners' `alpha` equal by iteration). Premises: `Pre`,
`Consistent`, `ThreadFacts` and `Rs.SmBaseZero` only. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`StoreWord` in every CTA and iteration.** -/
theorem storeWord_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) :
    ∀ c i, StoreWord Q L X c i :=
  fun c i => storeWordB hpre hX hf hz c i

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
