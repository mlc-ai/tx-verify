-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Tmem.AccessCp
import Kernels.InklingRelDecode.Proof.Common.Export.AllocBefore
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

/-! # Every Tensor Memory access follows lane 0 of warp 0's allocation

An MMA, load or store is past its thread's first `bar.sync 0` (`Export.tc_after_start`), which
lane 0 of warp 0 reached after its allocation (`Export.alloc_before`). The kernel has no copy. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **`LifeCp.alloc_before`.** -/
public theorem alloc_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {e : EvId} (hop : Tmem.AccessCp.Op X e) :
    ∃ j pc grp dst n, X.get ((e.1 / L.block) * L.block + 0 * 32, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block + 0 * 32)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block + 0 * 32, j) e := by
  obtain ⟨h,f⟩ := e
  have get : ∃ pc k, X.get (h,f) = some ⟨pc,.tc k⟩ ∧
      ((∃ d s a mk, k = .mma d s a mk) ∨ (∃ a v s, k = .ld a v s) ∨ ∃ a v s, k = .st a v s) := by
    rcases hop with ⟨d,s,a,mk,pc,he⟩ | ⟨c,hc⟩ | ⟨a,v,s,pc,he⟩ | ⟨a,v,s,pc,he⟩
    · exact ⟨pc,_,he,.inl ⟨d,s,a,mk,rfl⟩⟩
    · exact (Lib.no_cp hX _ c hc).elim
    · exact ⟨pc,_,he,.inr (.inl ⟨a,v,s,rfl⟩)⟩
    · exact ⟨pc,_,he,.inr (.inr ⟨a,v,s,rfl⟩)⟩
  obtain ⟨pc,k,he,hk⟩ := get
  obtain ⟨j,pc,grp,dst,n,get,len,order,-⟩ :=
    Export.alloc_before hp hX hf he (Export.tc_after_start hp hX he hk)
  exact ⟨j,pc,grp,dst,n,get,len,order⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
