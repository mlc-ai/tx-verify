-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteSpace

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- Thread writes in shared space can only allocate TMEM, fill the query tile,
publish the worker inputs, or reuse the published words. -/
def sharedStores : List Nat :=
  [11,526,532,538,544,550,556,562,568,570,571,2250,2848]

private def sharedWrite (op : Op) : Bool :=
  storeSpace op == some .shared || (dynamicAccess op && writeOp op)

private theorem checked : OpPcsFast kernel.code sharedWrite sharedStores = true := by
  decide +kernel

theorem shared_write_site {L m X i pc a bs} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get i = some ⟨pc,.wr a bs⟩) (hsp : a.loc.space=.shared) : pc ∈ sharedStores := by
  obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX he
  · cases bad
  apply OpPcsFast.mem checked code
  rcases fires_write_space fire rfl with h | h
  · simp [sharedWrite,h,hsp]
  · simp [sharedWrite,h,fires_write_op fire rfl]

end PTX.Kernels.InklingRelDecode.Proof.Lib
