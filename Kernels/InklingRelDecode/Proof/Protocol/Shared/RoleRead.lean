-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.PairRead
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Lemmas.Order.ReadSame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- The first dispatch reads its warp's byte from the initial role word.
All same-value publishers are allowed as reads-from sources. -/
theorem first_role_byte {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2340,.rd a bs⟩)
    (first : ((X.tr g).take k).countP (Execution.isBarId 1)=1)
    (tile : ¬TensorByte X a.loc) :
    bs.length=1 ∧ bs[0]?=some ((b32 16777730).toBytes[g%L.block/32-4]?) := by
  obtain ⟨low,high,size,loc⟩ := Dispatch.Export.role_address hp hX he
  let j := g%L.block/32-4
  let l : Loc := ⟨.shared,g/L.block,L.sharedBase+213336+j⟩
  have at0 : a.loc.at 0=l := by rw [loc]; rfl
  have miss : ¬TensorByte X (a.loc.at 0) := by simpa [Loc.at] using tile
  have mem : X.MemReads (.thread (g,k)) a bs := .inl ⟨_,he⟩
  refine ⟨((hX.rf _ _ _ mem).1.trans size),?_⟩
  let W (w : AsyncCopy.Ref) := ∃ h v dst bytes, w=.thread (h,v) ∧
    X.get (h,v)=some ⟨570,.wr dst bytes⟩
  apply read_byte_of_writers hX mem (by omega : 0<a.size) W
  · obtain ⟨v,pub,ord⟩ := visible_role hp hX he (.inl rfl)
    refine ⟨_,_,_,⟨_,_,_,_,rfl,pub⟩,.inl ⟨_,pub⟩,?_,.direct (.inl ord)⟩
    rw [at0]
    exact ⟨rfl,rfl,Nat.le_add_right ..,Nat.add_lt_add_left (show j<4 by dsimp [j]; omega) _⟩
  · rintro _ dst bytes ⟨h,v,a',b',rfl,pub⟩ write cover
    rcases write with ⟨_,act⟩|⟨_,_,act⟩ <;> rw [pub] at act
    · obtain ⟨_,knd⟩ := Event.mk.inj (Option.some.inj act)
      obtain ⟨rfl,rfl⟩ := Kind.wr.inj knd
      obtain ⟨addr,data⟩ := Lib.role_word hp hX pub (.inl ⟨rfl,rfl⟩)
      rw [wbyte,addr,data,at0]
      simp [Lib.wordAcc,l,j]
    · cases act
  · intro w dst bytes write cover
    obtain ⟨⟨h,v⟩,pc,rfl,store⟩ := thread_writer hX write cover miss
    rw [at0] at cover
    obtain ⟨space,cta,lo,hi⟩ := cover
    change Space.shared=dst.loc.space at space
    change g/L.block=dst.loc.cta at cta
    dsimp only [l] at lo hi
    have sites := (publication_writers hp hX store space.symm (by omega :
      dst.loc.addr≤L.sharedBase+(213336+j)) (by omega)).2 (by omega) (by dsimp [j]; omega)
    rcases sites with rfl|rfl
    · exact .inl ⟨_,_,_,_,rfl,store⟩
    · obtain ⟨dstEq,_⟩ := Lib.role_word hp hX store (.inr ⟨rfl,rfl⟩)
      rw [dstEq] at cta
      exact .inr (.direct (.inl (first_read_before_reuse hp hX he first store (.inr rfl) cta)))

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
