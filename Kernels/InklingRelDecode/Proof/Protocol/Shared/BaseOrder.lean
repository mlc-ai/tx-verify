-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Ordered
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.Regions
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseFence
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Common.Export.BaseWord
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Lemmas.Kernel.Frame
import Lemmas.Order.Order

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- An early thread access of a CTA precedes a copy's issue in that CTA through its fence. -/
private theorem early_copy {Q L m X g k h j pc a sp l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads)
    (early : ((X.tr g).take (k+1)).countP (Execution.isBarId 0) ≤ 1)
    (he : X.get (h,j)=some ⟨pc,.tensorIssue a sp⟩) (cta : g/L.block=h/L.block)
    (space : l.space=.shared) (own : l.cta=g/L.block) : ProxyBefore L X (g,k) (h,j) l := by
  obtain ⟨f,jf,fcta,flt,⟨pcf,fence⟩,two,order⟩ := copy_fence hp hX he
  exact early_proxy hp hX hg (Frame.lt_of_get hX he) cta early fcta flt ⟨pcf,fence⟩ two order
    space own (List.getElem?_eq_some_iff.mp fence).1

/-- An early thread access of a CTA precedes an MMA issue in that CTA through its fence. -/
private theorem early_mma {Q L m X g k h j pc dst s acc mask l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (early : ((X.tr g).take (k+1)).countP (Execution.isBarId 0) ≤ 1)
    (he : X.get (h,j)=some ⟨pc,.tc (.mma dst s acc mask)⟩) (cta : g/L.block=h/L.block)
    (space : l.space=.shared) (own : l.cta=g/L.block) : ProxyBefore L X (g,k) (h,j) l := by
  obtain ⟨_,range,_⟩ := Mma.Export.operands_all hp hX hf he
  have hh := Frame.lt_of_get hX he
  have late : 2 ≤ ((X.tr h).take j).countP (Execution.isBarId 1) :=
    Export.after_initialization hp hX he (fun _ => nofun) (by
      simp only [Export.afterInit]
      simp
      omega)
  obtain ⟨g0,uf,fcta,flt,fence,two,order⟩ := fence_after_release hp hX hh
    (List.getElem?_eq_some_iff.mp he).1 (Nat.le_trans (by decide) late)
  exact early_proxy hp hX hg hh cta early fcta flt ⟨_,fence⟩ two order space own
    (List.getElem?_eq_some_iff.mp fence).1

/-- An early thread access of the base word is before a copy's write of the byte. -/
theorem thread_copy {Q L m X g k ref' b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (early : ((X.tr g).take (k+1)).countP (Execution.isBarId 0) ≤ 1)
    (own : l.cta=g/L.block) (hw : X.Intent ref' b true) (hb : b.Covers l)
    (async : ∀ g k, ref' ≠ .thread (g,k)) (space : l.space=.shared) :
    ByteCausality L X l (.thread (g,k)) ref' := by
  obtain ⟨h,j,pc,addr,sp,x,y,z,σ,rfl,e,-,cta,-⟩ := copy_write_facts hp hX hf hw hb async
  exact .direct ⟨⟨b,true,hw,hb⟩,.inl (early_copy hp hX hg early e (own.symm.trans cta) space
    own)⟩

/-- An early thread access of the base word is before an MMA's read of the byte. -/
private theorem thread_mma {Q L m X g k ref' b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hg : g<L.threads) (early : ((X.tr g).take (k+1)).countP (Execution.isBarId 0) ≤ 1)
    (own : l.cta=g/L.block) (hr : X.Intent ref' b false) (hb : b.Covers l) (reg : InRing L l)
    (mma : ∃ i b j, ref' = .async i (.mmaRead b j)) :
    ByteCausality L X l (.thread (g,k)) ref' := by
  obtain ⟨h,j,isB,idx,pc,dst,s,acc,mask,σ,rfl,e,-,-,cta,-⟩ :=
    ring_read_facts hp hX hf words hr hb reg mma
  exact .direct ⟨⟨b,false,hr,hb⟩,.inl (early_mma hp hX hf hg early e (own.symm.trans cta) reg.1
    own)⟩

private theorem store_cta {Q L m X g k a bs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨11,.wr a bs⟩)
    (cov : a.Covers l) : l.cta=g/L.block := by
  obtain ⟨loc,_⟩ := Startup.Export.alloc_write hp hX he
  have := cov.2.1
  rw [loc] at this
  exact this

private theorem load_cta {Q L m X g k a bs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨13,.rd a bs⟩)
    (cov : a.Covers l) : l.cta=g/L.block := by
  obtain ⟨loc,_⟩ := Startup.Export.base_address hp hX he
  have := cov.2.1
  rw [loc] at this
  exact this

/-- A write and a read of a base word byte are ordered. -/
private theorem write_read {Q L m X ref ref' a b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hw : X.Intent ref a true) (hr : X.Intent ref' b false) (ha : a.Covers l)
    (hb : b.Covers l) (base : Iface.InBase L l) :
    ByteCausality L X l ref ref' ∨ ByteCausality L X l ref' ref := by
  have reg := InRing.of_base base
  rcases base_writer hp hX hw ha base.1 base.2.1 base.2.2 with ⟨g,k,bs,rfl,store⟩|async
  · obtain ⟨-,-,zero⟩ := Export.base_store hp hX store
    have hg := Frame.lt_of_get hX store
    have own := store_cta hp hX store ha
    rcases base_reader hp hX hr hb base.1 base.2.2 with ⟨g',k',bs',rfl,load⟩|mma
    · have hg' := Frame.lt_of_get hX load
      obtain ⟨one,-⟩ := Export.base_load hp hX load
      exact .inl (.direct (.inl (Export.startup_before hp hX
        ⟨hg,hg',own.symm.trans (load_cta hp hX load hb)⟩
        (List.getElem?_eq_some_iff.mp load).1 (by omega) (by omega))))
    · exact .inl (thread_mma hp hX hf words hg (by omega) own hr hb reg mma)
  · rcases base_reader hp hX hr hb base.1 base.2.2 with ⟨g',k',bs',rfl,load⟩|mma
    · have hg' := Frame.lt_of_get hX load
      obtain ⟨-,one⟩ := Export.base_load hp hX load
      exact .inr (thread_copy hp hX hf hg' (by omega) (load_cta hp hX load hb) hw ha async
        base.1)
    · exact copy_read_ordered hp hX hf rows init words hw hr ha hb reg async mma

/-- **The allocation's store of the base word is before every copy's write of a byte of it.** -/
theorem alloc_before_copy {Q L m X g k a bs ref' b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (store : X.get (g,k)=some ⟨11,.wr a bs⟩) (ha : a.Covers l) (hw : X.Intent ref' b true)
    (hb : b.Covers l) (async : ∀ g k, ref' ≠ .thread (g,k)) (base : Iface.InBase L l) :
    ByteCausality L X l (.thread (g,k)) ref' := by
  obtain ⟨hk,h0,zero⟩ := Export.base_store hp hX store
  exact thread_copy hp hX hf (Frame.lt_of_get hX store) (by omega) (store_cta hp hX store ha)
    hw hb async base.1

/-- Two writes of a base word byte are ordered. -/
private theorem write_write {Q L m X ref ref' a b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (ne : ref ≠ ref') (hw : X.Intent ref a true) (hw' : X.Intent ref' b true)
    (ha : a.Covers l) (hb : b.Covers l) (base : Iface.InBase L l) :
    ByteCausality L X l ref ref' ∨ ByteCausality L X l ref' ref := by
  have reg := InRing.of_base base
  rcases base_writer hp hX hw ha base.1 base.2.1 base.2.2 with ⟨g,k,bs,rfl,store⟩|async
  · obtain ⟨hk,h0,zero⟩ := Export.base_store hp hX store
    have hg := Frame.lt_of_get hX store
    have own := store_cta hp hX store ha
    rcases base_writer hp hX hw' hb base.1 base.2.1 base.2.2 with ⟨g',k',bs',rfl,store'⟩|async'
    · exfalso
      obtain ⟨hk',h0',-⟩ := Export.base_store hp hX store'
      have own' := store_cta hp hX store' hb
      have e1 := Nat.div_add_mod g L.block
      have e2 := Nat.div_add_mod g' L.block
      have same : g=g' := by rw [← e1,← e2,h0,h0',own.symm.trans own']
      exact ne (by rw [same,hk,hk'])
    · exact .inl (thread_copy hp hX hf hg (by omega) own hw' hb async' base.1)
  · rcases base_writer hp hX hw' hb base.1 base.2.1 base.2.2 with ⟨g',k',bs',rfl,store'⟩|async'
    · obtain ⟨-,-,zero⟩ := Export.base_store hp hX store'
      exact .inr (thread_copy hp hX hf (Frame.lt_of_get hX store') (by omega)
        (store_cta hp hX store' hb) hw ha async base.1)
    · exact copies_ordered hp hX hf rows init words hu ne hw hw' ha hb reg async async'

/-- **The base word's conflicting accesses are ordered**: the allocation's store is the first
thread's second event, before every load by barrier zero's first instance and before every
copy's issue and MMA's issue through a proxy fence of the CTA; copies and MMA reads of the
bytes in K slot zero are ordered as the ring's. -/
theorem base_ordered {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) : ByteOrdered L X (Iface.InBase L) := by
  rintro e f a b l ⟨ne,we,wf,he,hfe,hw,-⟩ ha hb base -
  cases we <;> cases wf
  · simp at hw
  · exact (write_read hp hX hf rows init words hfe he hb ha base).symm
  · exact write_read hp hX hf rows init words he hfe ha hb base
  · exact write_write hp hX hf rows init words hu ne he hfe ha hb base

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
