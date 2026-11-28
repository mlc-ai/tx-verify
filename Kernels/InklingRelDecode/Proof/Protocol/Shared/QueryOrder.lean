-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

import Kernels.InklingRelDecode.Proof.Protocol.Shared.QueryFence
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Lemmas.Protocol.RegionByte
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryStore
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryLane
public import Kernels.InklingRelDecode.Proof.Lib.QTile
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Lemmas.Order.Order

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- Every write intent at a byte of the query tile is a query store of a default-partition lane
at the address its lane and store number fix. -/
theorem query_store_facts {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (intent : X.Intent ref a true) (cov : a.Covers l) (inq : Iface.InQ L l) :
    ∃ g k bs, ∃ i : Fin 8, ∃ j : Fin 4, ref=.thread (g,k) ∧
      X.get (g,k)=some ⟨526+6*i.val,.wr a bs⟩ ∧ g%L.block<128 ∧
      a.loc=⟨.shared,g/L.block,L.sharedBase+Lib.qSwz (g%L.block)+(196608+2048*Lib.qGroup i)+
        4*j.val⟩ ∧ a.size=4 := by
  obtain ⟨sp,ct,lo,hi⟩ := cov
  obtain ⟨space,qlo,qhi⟩ := inq
  rcases Lib.write_intents hX intent with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|⟨i,x,y,z,addr,s,_,issue,atByte,size⟩
  · obtain ⟨i,rfl⟩ := query_writers hp hX get (b := l.addr-L.sharedBase) (sp.symm.trans space)
      (by omega) (by omega) (by omega) (by omega)
    obtain ⟨⟨j,loc⟩,size,_⟩ := Prologue.Export.query_store hp hX i get
    exact ⟨g,k,bs,i,j,rfl,get,Prologue.Export.query_lane hp hX hf get,loc,size⟩
  · have miss := outside_tiles (l := a.loc) hp hX (by omega) (by omega)
    exact (miss ⟨i,addr,s,issue,x,y,z,atByte⟩).elim

/-- Every read intent at a byte of the query tile is an operand read of an MMA issued in the
byte's CTA. -/
private theorem read_facts {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (intent : X.Intent ref a false) (cov : a.Covers l) (inq : Iface.InQ L l) :
    ∃ h f pc dst s acc mask side j, ref=.async (h,f) (.mmaRead side j) ∧
      X.get (h,f)=some ⟨pc,.tc (.mma dst s acc mask)⟩ ∧ (2462≤pc ∧ pc≤2553) ∧
      l.cta=h/L.block := by
  obtain ⟨space,qlo,qhi⟩ := inq
  obtain ⟨i,side,j,rfl⟩ := query_reader hp hX intent cov space qlo qhi
  obtain ⟨h,f⟩ := i
  obtain ⟨_,size,foot⟩ := intent
  rcases foot with ⟨dst,s,acc,mask,⟨pc,get⟩,byte⟩|⟨c,_,_,cp,_⟩
  · obtain ⟨_,range,tile⟩ := Mma.Export.operands_all hp hX hf get
    obtain ⟨_,own,_⟩ := tile _ _ _ byte
    exact ⟨h,f,pc,dst,s,acc,mask,side,j,rfl,get,range,cov.2.1.trans own⟩
  · exact (Lib.no_cp hX (h,f) c cp).elim

/-- A query store is ordered before the operand read of an MMA at the same byte. -/
theorem query_write_read {Q L m X sref rref a b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : X.Intent sref a true) (hr : X.Intent rref b false) (ha : a.Covers l)
    (hb : b.Covers l) (inq : Iface.InQ L l) : ByteCausality L X l sref rref := by
  obtain ⟨g,k,bs,i,j,rfl,get,lane,loc,_⟩ := query_store_facts hp hX hf hw ha inq
  obtain ⟨h,f,pc,dst,s,acc,mask,side,idx,rfl,mma,range,own⟩ := read_facts hp hX hf hr hb inq
  have cta : l.cta=g/L.block := by
    have := ha.2.1
    rw [loc] at this
    exact this
  have space : l.space=.shared := inq.1
  refine .direct ⟨⟨b,false,hr,hb⟩,.inl ?_⟩
  exact query_proxy hp hX get lane mma range (cta.symm.trans own) space cta

/-- **The conflicting accesses of the query tile are ordered**: two stores of one byte are one
lane's, in program order; a store precedes every MMA operand read of the byte through its lane's
proxy fence and barrier one. -/
theorem query_ordered {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ByteOrdered L X (Iface.InQ L) := by
  rintro e f a b l ⟨ne,we,wf,he,hf',w,ov⟩ ha hb inq _
  cases we <;> cases wf
  · simp only [Bool.false_eq_true,or_self] at w
  · exact .inr (query_write_read hp hX hf hf' he hb ha inq)
  · exact .inl (query_write_read hp hX hf he hf' ha hb inq)
  · have ha' := ha
    have hb' := hb
    obtain ⟨g,k,bs,i,j,rfl,get,lane,loc,sz⟩ := query_store_facts hp hX hf he ha inq
    obtain ⟨g',k',bs',i',j',rfl,get',lane',loc',sz'⟩ := query_store_facts hp hX hf hf' hb inq
    obtain ⟨_,cta,lo,hi⟩ := ha
    obtain ⟨_,cta',lo',hi'⟩ := hb
    rw [loc] at cta lo hi
    rw [loc'] at cta' lo' hi'
    rw [sz] at hi
    rw [sz'] at hi'
    simp only at cta cta' lo hi lo' hi'
    have key := Lib.qOff_inj (m := i.val) (m' := i'.val) (t := g%L.block) (t' := g'%L.block)
      (w := j.val) (w' := j'.val)
      (b := l.addr-(L.sharedBase+Lib.qSwz (g%L.block)+(196608+2048*Lib.qGroup i)+4*j.val))
      (b' := l.addr-(L.sharedBase+Lib.qSwz (g'%L.block)+(196608+2048*Lib.qGroup i')+
        4*j'.val)) i.isLt i'.isLt (by omega) (by omega) j.isLt j'.isLt (by omega) (by omega)
      (by omega)
    obtain ⟨rfl,-,-⟩ : g=g' ∧ True ∧ True := by
      refine ⟨?_,trivial,trivial⟩
      have h1 := Nat.div_add_mod g L.block
      have h2 := Nat.div_add_mod g' L.block
      have h3 : g/L.block=g'/L.block := cta.symm.trans cta'
      rw [←h1,←h2,h3,key.1]
    have distinct : k≠k' := by
      rintro rfl
      exact ne rfl
    have access : X.Access (g,k) a true := he
    have access' : X.Access (g,k') b true := hf'
    rcases Nat.lt_or_gt_of_ne distinct with lt|gt
    · exact .inl (.direct (.inl (.single (.inl (po_of_overlap access access' rfl lt
        ⟨l,ha',hb'⟩)))))
    · exact .inr (.direct (.inl (.single (.inl (po_of_overlap access' access rfl gt
        ⟨l,hb',ha'⟩)))))

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
