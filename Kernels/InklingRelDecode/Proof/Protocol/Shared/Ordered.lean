-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Lemmas.Protocol.RegionByte
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.RoleWord
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- The padding and barrier arena are clear of ordinary and asynchronous write intents. -/
theorem no_arena_write {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (write : X.Intent ref a true)
    (cover : a.Covers l) (space : l.space=.shared)
    (lo : L.sharedBase+213008≤l.addr) (hi : l.addr<L.sharedBase+213336) : False := by
  obtain ⟨sp,ct,left,right⟩ := cover
  rcases Lib.write_intents hX write with ⟨⟨g,k⟩,pc,bs,_,get⟩|⟨i,x,y,z,addr,s,_,issue,atByte,size⟩
  · have sites := (publication_writers (b := l.addr-L.sharedBase) hp hX get (sp ▸ space)
      (by omega) (by omega)).2 (by omega) (by omega)
    rcases sites with rfl|rfl
    · have loc := (Lib.role_word hp hX get (.inl ⟨rfl,rfl⟩)).1
      rw [loc] at left
      change L.sharedBase+213336≤l.addr at left
      omega
    · have loc := (Lib.role_word hp hX get (.inr ⟨rfl,rfl⟩)).1
      rw [loc] at left
      change L.sharedBase+213336≤l.addr at left
      omega
  · have miss := outside_tiles (l := a.loc) hp hX (by omega) (by omega)
    exact miss ⟨i,addr,s,issue,x,y,z,atByte⟩

/-- Since each conflict includes a writer, every byte in the mbarrier region
satisfies the common ordering criterion for race and mixed-size safety. -/
theorem mbar_ordered {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) : ByteOrdered L X (Iface.InMbar L) := by
  rintro e f a b l ⟨_,we,wf,he,hf,w,_⟩ ha hb ⟨sp,lo,hi⟩ _
  rcases w with rfl|rfl
  · exact (no_arena_write hp hX he ha sp (by omega) hi).elim
  · exact (no_arena_write hp hX hf hb sp (by omega) hi).elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
