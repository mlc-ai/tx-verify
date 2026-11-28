-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadRound
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RoleRead
import Lemmas.Kernel.FrameU
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Epilogue.Export.Published
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Lemmas.Order.ReadSame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

private theorem store_before {Q L m X g u p a bs h k ev n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (store : X.get (g,u)=some ⟨p,.wr a bs⟩)
    (get : X.get (h,k)=some ev) (stage : Export.publishedAt p=some n)
    (later : n<((X.tr h).take k).countP (Execution.isBarId 1)) (cta : g/L.block=h/L.block) :
    baseCausality L X (g,u) (h,k) := by
  apply publication_handoff hp hX g h u k
    ⟨Frame.lt_of_get hX store,Frame.lt_of_get hX get,cta⟩ (List.getElem?_eq_some_iff.mp get).1
  change ((X.tr g).take (u+1)).countP _ < _
  rw [List.take_add_one,show (X.tr g)[u]?=_ from store,List.countP_append,
    Export.publication_store hp hX store stage]
  exact later

/-- In the second dispatch all four warp bytes contain three. A candidate
source at 570 is hidden by the same-CTA exit store from lane zero. -/
theorem exit_role_byte {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2340,.rd a bs⟩)
    (second : ((X.tr g).take k).countP (Execution.isBarId 1)=4) (tile : ¬TensorByte X a.loc) :
    bs.length=1 ∧ bs[0]?=some ((b32 50529027).toBytes[g%L.block/32-4]?) := by
  obtain ⟨low,high,size,loc⟩ := Dispatch.Export.role_address hp hX he
  obtain first|⟨_,v,sync⟩ := read_round hp hX he (.inl rfl)
  · omega
  obtain ⟨u,_,exitStore⟩ := Epilogue.Export.published_exit hp hX sync
  let lane := g/L.block*L.block
  have same : lane/L.block=g/L.block := Nat.mul_div_cancel _ (by rw [hp.block]; decide)
  have edge := store_before hp hX exitStore he (n := 3) rfl (by omega) same
  have mem : X.MemReads (.thread (g,k)) a bs := .inl ⟨_,he⟩
  let j := g%L.block/32-4
  have base : a.loc.at 0=⟨.shared,g/L.block,L.sharedBase+213336+j⟩ := by rw [loc]; rfl
  let W (w : AsyncCopy.Ref) := ∃ h v, w=.thread (h,v) ∧
    X.get (h,v)=some ⟨2848,.wr (Lib.wordAcc ⟨.shared,h/L.block,L.sharedBase+213336⟩)
      (b32 50529027).toBytes⟩
  refine ⟨(hX.rf _ _ _ mem).1.trans size,read_byte_of_writers_hidden hX mem (by omega)
    W _ (w0 := .thread (lane,u)) (.inl ⟨_,exitStore⟩) ?_ (.direct (.inl edge)) ?_ ?_⟩
  · rw [base]
    exact ⟨rfl,same.symm,Nat.le_add_right ..,Nat.add_lt_add_left (show j<4 by dsimp [j]; omega) _⟩
  · rintro _ dst bytes ⟨h,v,rfl,pub⟩ write _
    rcases write with ⟨_,act⟩|⟨_,_,act⟩ <;> rw [pub] at act
    · obtain ⟨_,kind⟩ := Event.mk.inj (Option.some.inj act)
      obtain ⟨rfl,rfl⟩ := Kind.wr.inj kind
      simp [wbyte,base,Lib.wordAcc,j]
    · cases act
  · intro w dst bytes write cover
    obtain ⟨⟨h,v⟩,pc,rfl,store⟩ := thread_writer hX write cover (by simpa [Loc.at] using tile)
    rw [base] at cover
    obtain ⟨space,cta,lo,hi⟩ := cover
    dsimp only at space cta lo hi
    have range : j<4 := by dsimp [j]; omega
    have sites := (publication_writers (b := 213336+j) hp hX store space.symm
      (by omega) (by omega)).2 (by omega) (by omega)
    rcases sites with rfl|rfl
    · obtain ⟨addr,_⟩ := Lib.role_word hp hX store (.inl ⟨rfl,rfl⟩)
      rw [addr] at cta
      have ord := Export.publication_store hp hX exitStore (phase := 3) rfl
      exact .inr (.inl (.direct (.inl (store_before hp hX store exitStore (n := 0) rfl
        (ord.symm ▸ (by decide : 0<3)) (cta.symm.trans same.symm)))))
    · obtain ⟨addr,data⟩ := Lib.role_word hp hX store (.inr ⟨rfl,rfl⟩)
      exact .inl ⟨h,v,rfl,addr ▸ data ▸ store⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
