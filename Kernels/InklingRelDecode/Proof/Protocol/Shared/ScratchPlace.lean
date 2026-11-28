-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvAccess
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TensorSource
public import Kernels.InklingRelDecode.Proof.Iface.Regions
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.RoleWord
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteSpace

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof

private def oddWrite (op : Op) : Bool :=
  storeSpace op == some .local || storeSpace op == some .const || (dynamicAccess op && writeOp op)

private theorem odd_sites : OpPcsFast kernel.code oddWrite [570,571,2848]=true := by
  decide +kernel

/-- No thread writes local or constant memory: the three dynamic stores write the shared window
and every static one names shared or global memory. -/
theorem write_space {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ⟨pc,.wr a bs⟩) :
    a.loc.space=.shared ∨ a.loc.space=.global := by
  by_contra bad
  push Not at bad
  obtain ⟨_,none⟩|⟨_,_,_,_,code,fire⟩ := get_source hX get
  · cases none
  have hit := OpPcsFast.mem odd_sites code (by
    rcases fires_write_space fire rfl with static|dynamic
    · cases hs : a.loc.space <;> simp_all [oddWrite]
    · simp [oddWrite,dynamic,fires_write_op fire rfl])
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with rfl|rfl|rfl
  · obtain ⟨loc,_⟩ := Lib.role_word hp hX get (.inl ⟨rfl,rfl⟩)
    rw [loc] at bad
    exact bad.1 rfl
  · obtain ⟨_,_,_,loc,_⟩ := Prologue.Export.pair_bytes hp hX get
    rw [loc] at bad
    exact bad.1 rfl
  · obtain ⟨loc,_⟩ := Lib.role_word hp hX get (.inr ⟨rfl,rfl⟩)
    rw [loc] at bad
    exact bad.1 rfl

/-- **A write of a byte outside the global space, the role word, the mbarriers, the query tile and
the rings is a write of the count pair or the scratch words.** -/
theorem write_place {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (w : X.Intent ref a true) (cov : a.Covers l) (ng : l.space≠.global)
    (off : ¬(Iface.InRole L l ∨ Iface.InQ L l ∨ Iface.InKv L l ∨ Iface.InBase L l)) :
    Iface.InCount L l ∨ Iface.InScratch L l := by
  simp only [Iface.InRole,Iface.InQ,Iface.InKv,Iface.InBase,Iface.InCount,Iface.InScratch,
    not_or] at off ⊢
  rcases Lib.write_intents hX w with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|
      ⟨⟨g,k⟩,x,y,z,addr,sp,eq,⟨pc,issue⟩,byte,_⟩
  · have shared : l.space=.shared := by
      rcases write_space hp hX get with h|h
      · exact cov.1.trans h
      · exact (ng (cov.1.trans h)).elim
    have own : a.loc.space=.shared := cov.1.symm.trans shared
    obtain ⟨_,_,lo,hi⟩ := cov
    obtain ⟨base,h⟩ := writer_at hp hX get own lo hi
    simp only [shared,true_and] at off ⊢
    rcases h with ⟨h1,-⟩|⟨h1,h2,-⟩|⟨h1,h2,-⟩|⟨h1,h2,-⟩ <;> omega
  · have async : ∀ g' k', ref≠.thread (g',k') := by
      rintro g' k' h
      rw [eq] at h
      cases h
    obtain ⟨_,_,_,_,_,_,_,_,σ,_,_,_,_,slot,_⟩ := copy_write_facts hp hX hf w cov async
    have ⟨_,shared,_⟩ := (tensor_box hp hX issue).1
    simp only [TensorCopy.writeLoc,Option.map_eq_some_iff] at byte
    obtain ⟨_,_,loc⟩ := byte
    have own : l.space=.shared := cov.1.trans (by rw [← loc]; exact shared)
    have := Iface.inSlot_kv σ.isLt slot
    simp only [own,true_and] at off
    exfalso
    omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
