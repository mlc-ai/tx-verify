-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.BaseRace
public import Kernels.InklingRelDecode.Proof.Protocol.SxTScratch
public import Kernels.InklingRelDecode.Proof.Protocol.SxTCount
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmSmBase

@[expose] public section

/-!
# `Safety.SharedOrder` for every consistent execution

The six regions' orders: `Proof2.base_ordered`, `Proof2.kv_ordered`, `Proof2.q_ordered` and
`Proof2.role_ordered` (the second tree's role table, `Proof2/Safety/BaseRace.lean`,
`Proof2/Safety/KvSame.lean`, `Proof2/Safety/Race.lean`), `count_ordered`, `scratch_ordered`
(`SxT*.lean`). The premises are the thread layer's facts, the role-byte reads, `Bar1Exits`, the
base-word read and the scratch words of every iteration.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Safety.SharedOrder`.** -/
theorem order_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) (hb : BaseWordRead L X)
    (hI : ∀ i, Lk.ScratchIt Q L X i) : SharedOrder L X where
  base := Proof2.base_ordered hpre hX
  kv := Proof2.kv_ordered hpre hX
  q := Proof2.q_ordered hpre hX
  count := count_ordered hpre hX hf hT hR hE hI (Rs.smBaseZero hpre hX hf hb)
  scratch := scratch_ordered hpre hX hf hT hI (Rs.smBaseZero hpre hX hf hb)
  role := Proof2.role_ordered hpre hX

end
end PTX.Kernels.InklingRelDecode.Proof.Sx
