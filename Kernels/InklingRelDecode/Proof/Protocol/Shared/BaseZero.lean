-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseOrder
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Common.Export.BaseStored
import Kernels.InklingRelDecode.Proof.Common.Export.BaseWord
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite

@[expose] public section

/-! # The word read at pc 13 is zero

The CTA's thread 0 stores the allocation's column, which is 0, before the first barrier 0, and
every thread reads it after. No byte of the word is read from the initial memory (`Hidden`, the
store precedes the read), nor from an asynchronous copy (which follows the read, `NoFuture`), so
each byte is read from a store of the word, the allocation's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- **`Iface.BaseRead`**: the shared word read at pc 13 holds 32 zero bits. -/
theorem base_read {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : Iface.BaseRead L X := by
  intro g k a bs he hloc hsize
  have hg := Frame.lt_of_get hX he
  have hb : L.block = 256 := hp.block
  obtain ⟨one,one'⟩ := Export.base_load hp hX he
  obtain ⟨a0,bs0,store⟩ := Export.base_stored hp hX hf he (by omega)
  obtain ⟨-,-,zero⟩ := Export.base_store hp hX store
  obtain ⟨loc0,size0,val0⟩ := Export.base_value hp hX store
  have cta : ((g/L.block)*L.block + 0*32)/L.block = g/L.block := by
    rw [hb]; omega
  have hrd : X.MemReads (.thread (g,k)) a bs := Or.inl ⟨13,he⟩
  have hlen : bs.length = a.size := (hX.rf _ a bs hrd).1
  apply List.ext_getElem?
  intro j
  by_cases hj : j < a.size
  swap
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by
      rw [List.length_map]; have : (b32 0).toBytes.length = 4 := rfl; omega)]
  have cov := Acc.covers_at hj
  have hl : (a.loc.at j).space = .shared ∧ L.sharedBase ≤ (a.loc.at j).addr ∧
      (a.loc.at j).addr < L.sharedBase + 4 ∧ (a.loc.at j).cta = g/L.block := by
    simp only [Loc.at, hloc]
    exact ⟨trivial,by omega,by omega,trivial⟩
  obtain ⟨sp,lo,hi,own⟩ := hl
  have cov0 : a0.Covers (a.loc.at j) := by
    unfold Acc.Covers at cov ⊢
    simp only [loc0,size0,cta,hloc,Loc.at] at cov ⊢
    rw [hsize] at cov
    exact cov
  have bc := Export.startup_before hp hX ⟨Frame.lt_of_get hX store,hg,by rw [cta]⟩
    (List.getElem?_eq_some_iff.mp he).1 (by rw [zero,one]; decide) (by rw [zero]; omega)
  have hH := hX.hidden _ a bs j (.thread ((g/L.block)*L.block + 0*32,1)) a0 bs0 hrd hj
    (Or.inl ⟨11,store⟩) cov0 (.direct (.inl bc))
  have hrf := (hX.rf _ a bs hrd).2 j hj
  rcases hsrc : X.rf (.thread (g,k)) j with _|w
  · rw [hsrc] at hH
    exact hH.elim
  rw [hsrc] at hrf
  obtain ⟨a',bs',hmw,hcv,hval⟩ := hrf
  rcases base_writer hp hX hmw.intent hcv sp lo hi with ⟨g',k',bs'',rfl,store'⟩|async
  · obtain ⟨loc',-,val'⟩ := Export.base_value hp hX store'
    obtain rfl : bs'' = bs' := by
      rcases hmw with ⟨pc0,h0⟩|⟨old,pc0,h0⟩ <;> rw [store'] at h0 <;> cases h0
      rfl
    rw [hval,val',List.getElem?_map]
    simp only [wbyte,loc',hloc,Loc.at]
    rw [Nat.add_sub_cancel_left]
    have h4 : (b32 0).toBytes.length = 4 := rfl
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  · exact (hX.noFuture _ a bs j w hrd hj hsrc
      (thread_copy hp hX hf hg (by omega) own hmw.intent hcv async sp)).elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
