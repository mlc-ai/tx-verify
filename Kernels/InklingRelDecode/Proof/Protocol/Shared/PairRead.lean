-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Visible
import Kernels.InklingRelDecode.Proof.Common.Export.PairAddress
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Lemmas.Order.ReadSame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof PTX.Frame

/-- A destination byte computed by an actual tensor load in this execution. -/
def TensorByte (X : Execution) (l : Loc) : Prop :=
  ∃ i addr sp, X.TensorIssue i addr sp ∧ ∃ x y z, TensorCopy.writeLoc sp x y z=some l

/-- Outside the tensor destinations, every covering write comes from a
thread store. The result includes read-modify-write and asynchronous references. -/
theorem thread_writer {L m X ref written bytes l}
    (hX : Consistent L kernel Assumptions.all m X)
    (write : X.MemWrites ref written bytes) (cover : written.Covers l) (miss : ¬TensorByte X l) :
    ∃ i pc, ref=.thread i ∧ X.get i=some ⟨pc,.wr written bytes⟩ := by
  rcases Lib.write_kinds hX write with ok|⟨_,x,y,z,_,_,_,issue,atByte,one⟩
  · exact ok
  · exfalso
    apply miss
    obtain ⟨sp,ct,lo,hi⟩ := cover
    have same : written.loc=l := by
      cases loc : written.loc with | mk ws wc wa =>
        cases l with | mk rs rc ra =>
          rw [loc] at sp ct lo hi
          dsimp only at sp ct lo hi
          rw [sp,ct,show wa=ra by omega]
    exact ⟨_,_,_,issue,x,y,z,same ▸ atByte⟩

/-- For the first-round count read the only remaining address obligation is the
destination of a tensor load. Every thread writer, its payload and its ordering
are discharged here. The byte obligation is independent of which thread read it. -/
theorem pair_read {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2345 ∨ p=2423) (j : Fin 2)
    (loc : a.loc=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩) (size : a.size=4)
    (first : ((X.tr g).take k).countP (Execution.isBarId 1)=1)
    (tile : ∀ b<a.size, ¬TensorByte X (a.loc.at b)) :
    bs=(b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
      else Lib.blocksOf Q L (g/L.block))).toBytes.map some := by
  let val := (b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
    else Lib.blocksOf Q L (g/L.block))).toBytes
  let dst := Lib.wordAcc ⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ j.val
  have valLen : val.length=4 := by rfl
  obtain ⟨u,get,ord⟩ := visible_pair hp hX he (.inr site) j
  let W (w : AsyncCopy.Ref) := ∃ i acc, w=.thread i ∧
    X.get i=some ⟨571,.wr acc val⟩ ∧ acc.loc=dst.loc
  have addr (b) : a.loc.at b=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val+b⟩ := by rw [loc]; rfl
  have mem : X.MemReads (.thread (g,k)) a bs := .inl ⟨p,he⟩
  refine read_of_writers hX mem W val (valLen.trans size.symm) ?_ ?_ ?_
  · intro b hb
    refine ⟨_,dst,val,⟨_,dst,rfl,get,rfl⟩,.inl ⟨_,get⟩,?_,.direct (.inl ord)⟩
    rw [addr]
    exact ⟨rfl,rfl,Nat.le_add_right ..,Nat.add_lt_add_left (show b<4 by omega) _⟩
  · rintro b _ _ written bytes ⟨i,acc,rfl,pub,wl⟩ write _
    rcases write with ⟨_,h⟩|⟨_,_,h⟩ <;> rw [pub] at h
    · obtain ⟨_,eq⟩ := Event.mk.inj (Option.some.inj h)
      obtain ⟨rfl,rfl⟩ := Kind.wr.inj eq
      rw [wbyte,addr,wl]
      simp [dst,Lib.wordAcc]
    · cases h
  · intro b hb ref written bytes write cover
    obtain ⟨⟨h,v⟩,q,rfl,store⟩ := thread_writer hX write cover (tile b hb)
    rw [addr] at cover
    obtain ⟨space,cta,lo,hi⟩ := cover
    dsimp only at space cta lo hi
    have off := j.isLt
    rw [size] at hb
    have sites := (publication_writers (b := 212992+4*j.val+b) hp hX store space.symm
      (by omega) (by omega)).1 (by omega) (by omega)
    rcases sites with rfl|rfl
    · obtain ⟨jj,tag,sz,wl,word⟩ := Prologue.Export.pair_bytes hp hX store
      rw [wl] at cta lo hi
      rw [sz] at hi
      dsimp only at cta lo hi
      have : jj=j := Fin.ext (by omega)
      subst jj
      left
      refine ⟨_,written,rfl,?_,?_⟩
      · rw [word,←cta] at store
        exact store
      · rw [wl,←cta]; rfl
    · right
      have wl := (Softmax.Export.scratch_store hp hX store).1
      rw [wl] at cta
      exact .direct (.inl (first_read_before_reuse hp hX he first store (.inl rfl) cta))

/-- The first-round count read obtains its launch word when tensor destinations
miss the eight published bytes. The MMA read always returns the block count. -/
theorem worker_pair {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2345 ∨ p=2423) (first : ((X.tr g).take k).countP (Execution.isBarId 1)=1)
    (tiles : ∀ o<8, ¬TensorByte X ⟨.shared,g/L.block,L.sharedBase+212992+o⟩) :
    ∃ j : Fin 2, (p=2423 → j=1) ∧ a.loc=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ ∧
      bs=(b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
        else Lib.blocksOf Q L (g/L.block))).toBytes.map some := by
  obtain ⟨j,second,loc,size⟩ := Export.pair_address hp hX he site
  refine ⟨j,second,loc,pair_read hp hX he site j loc size first ?_⟩
  intro b hb
  have small : 4*j.val+b<8 := by have := j.isLt; omega
  simpa only [loc,Loc.at,Nat.add_assoc] using tiles _ small

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
