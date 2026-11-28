-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.OperandRead
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Kernels.InklingRelDecode.Proof.Common.Export.PairAddress
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Protocol.Region

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX

/-- **The accesses of a scratch or count byte** are thread accesses: the stores of the count pair
(pc 571) and of the softmax words (pc 2250), the loads of the softmax words (pc 2252) and of the
workers' count pair (pcs 2345, 2423), each of one aligned word. -/
theorem scratch_access {Q L m X ref a w l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hi : X.Intent ref a w)
    (hc : a.Covers l) (sp : l.space=.shared)
    (lo : L.sharedBase+212992≤l.addr) (end' : l.addr<L.sharedBase+213008) :
    ∃ g k j, ref=.thread (g,k) ∧ a.loc.addr=L.sharedBase+212992+4*j ∧ a.size=4 ∧
      a.loc.cta=g/L.block ∧
      ((w=true ∧ ∃ pc bs, X.get (g,k)=some ⟨pc,.wr a bs⟩ ∧ (pc=571 ∨ pc=2250)) ∨
       (w=false ∧ ∃ pc bs, X.get (g,k)=some ⟨pc,.rd a bs⟩ ∧ (pc=2252 ∨ pc=2345 ∨ pc=2423))) := by
  obtain ⟨space,ct,start,stop⟩ := hc
  cases w with
  | true =>
    rcases Lib.write_intents hX hi with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|⟨i,x,y,z,addr,s,_,issue,byte,size⟩
    · have sites := (publication_writers (b := l.addr-L.sharedBase) hp hX get (space ▸ sp)
        (by omega) (by omega)).1 (by omega) (by omega)
      have place : ∃ j, a.loc.addr=L.sharedBase+212992+4*j ∧ a.size=4 ∧ a.loc.cta=g/L.block := by
        rcases sites with rfl|rfl
        · obtain ⟨j,_,sz,loc,_⟩ := Prologue.Export.pair_bytes hp hX get
          exact ⟨j.val,loc ▸ rfl,sz,by rw [loc]⟩
        · obtain ⟨loc,sz⟩ := Softmax.Export.scratch_store hp hX get
          exact ⟨_,by rw [loc,Nat.mul_comm (g%L.block/32%4)],sz,by rw [loc]⟩
      obtain ⟨j,al,sz,own⟩ := place
      exact ⟨g,k,j,rfl,al,sz,own,.inl ⟨rfl,pc,bs,get,sites⟩⟩
    · exact (outside_tiles (l := a.loc) hp hX (by omega) (by omega)
        ⟨i,addr,s,issue,x,y,z,byte⟩).elim
  | false =>
    rcases Execution.shared_intent hi ⟨space,ct,start,stop⟩ sp with
      ⟨⟨g,k⟩,rfl,acc⟩|⟨i,b,j,rfl⟩|⟨i,x,y,z,rfl⟩|⟨i,x,y,z,rfl⟩|⟨_,_,_,_,_,⟨_,get⟩,_⟩|
        ⟨_,_,_,_,⟨_,get⟩⟩|⟨_,_,⟨_,get⟩⟩
    · rcases acc with ⟨bs,⟨pc,get⟩,_⟩|⟨_,_,bad⟩|⟨old,new,pc,get⟩
      · have site := shared_read_site hX get (space ▸ sp)
        simp only [List.mem_cons,List.not_mem_nil,or_false] at site
        rcases site with rfl|rfl|rfl|pair
        · obtain ⟨loc,sz⟩ := Startup.Export.base_address hp hX get
          rw [loc,sz] at stop
          change l.addr<L.sharedBase+4 at stop
          omega
        · obtain ⟨loc,sz⟩ := Softmax.Export.scratch_read hp hX get
          exact ⟨g,k,_,rfl,by rw [loc,Nat.mul_comm (g%L.block%4)],sz,by rw [loc],
            .inr ⟨rfl,_,bs,get,.inl rfl⟩⟩
        · obtain ⟨_,_,_,loc⟩ := Dispatch.Export.role_address hp hX get
          rw [loc] at start
          dsimp only at start
          omega
        · obtain ⟨j,_,loc,sz⟩ := Export.pair_address hp hX get pair
          exact ⟨g,k,j.val,rfl,loc ▸ rfl,sz,by rw [loc],.inr ⟨rfl,_,bs,get,.inr pair⟩⟩
      · cases bad
      · have wr : X.Intent (.thread (g,k)) a true := .inr (.inr ⟨old,new,pc,get⟩)
        rcases Lib.write_intents hX wr with ⟨i,q,bs,eq,h⟩|⟨_,_,_,_,_,_,eq,_⟩
        · cases eq
          rw [get] at h
          cases h
        · cases eq
    · obtain ⟨_,size,foot⟩ := hi
      have := operand_byte hp hX hf foot
      omega
    · obtain ⟨_,_,_,⟨_,get⟩,_⟩ := hi
      exact (Lib.no_tensorStore hX get).elim
    · cases hi.1
    · exact (Lib.no_clc hX get).elim
    · exact (Lib.no_copy hX get).elim
    · exact (Lib.no_bulkPrefetch hX get).elim

/-- Reusing the two published counts as scratch can change their contents. Every
access still covers one aligned word; two intents covering a common byte have
the same footprint, even before outstanding asynchronous reads complete. -/
theorem scratch_footprint {Q L m X e f a b w v l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (ha : X.Intent e a w) (hb : X.Intent f b v) (ca : a.Covers l) (cb : b.Covers l)
    (reg : Iface.InCount L l ∨ Iface.InScratch L l) : a.SameFootprint b := by
  have ⟨sp,lo,hi⟩ : l.space=.shared ∧ L.sharedBase+212992≤l.addr ∧ l.addr<L.sharedBase+213008 := by
    rcases reg with ⟨sp,lo,hi⟩|⟨sp,lo,hi⟩ <;> exact ⟨sp,by omega,by omega⟩
  obtain ⟨_,_,i,_,ia,sa,_,_⟩ := scratch_access hp hX hf ha ca sp lo hi
  obtain ⟨_,_,j,_,jb,sb,_,_⟩ := scratch_access hp hX hf hb cb sp lo hi
  obtain ⟨as',ac,la,ua⟩ := ca
  obtain ⟨bs,bc,lb,ub⟩ := cb
  have eq : a.loc.addr=b.loc.addr := by omega
  exact ⟨Loc.mk.injEq .. |>.mpr ⟨as'.symm.trans bs,ac.symm.trans bc,eq⟩,sa.trans sb.symm⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
