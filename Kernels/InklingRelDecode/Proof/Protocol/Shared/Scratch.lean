-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof

/-- Every writer covering a byte of the scratch load belongs to the reader's CTA.
Words zero and one can also come from the prologue. Every other candidate writes
the same word from the warp selected by the reader's lane number. -/
theorem scratch_source {Q L m X g k a bs ref ac bytes b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.get (g,k)=some ⟨2252,.rd a bs⟩)
    (byte : b<a.size) (write : X.MemWrites ref ac bytes) (cover : ac.Covers (a.loc.at b)) :
    ∃ h v, ref=.thread (h,v) ∧ h/L.block=g/L.block ∧ ac.loc=a.loc ∧ ac.size=4 ∧
      ((g%L.block%4<2 ∧ X.get (h,v)=some ⟨571,.wr ac bytes⟩) ∨
       (h%L.block/32%4=g%L.block%4 ∧ X.get (h,v)=some ⟨2250,.wr ac bytes⟩)) := by
  obtain ⟨rl,rs⟩ := Softmax.Export.scratch_read hp hX read
  rw [rs] at byte
  have dest := outside_tiles hp hX (l := a.loc.at b)
    (by rw [rl]; dsimp [Loc.at]; omega) (by rw [rl]; dsimp [Loc.at]; omega)
  obtain ⟨⟨h,v⟩,pc,rfl,store⟩ := thread_writer hX write cover dest
  rw [rl] at cover
  obtain ⟨space,cta,lo,hi⟩ := cover
  dsimp [Loc.at] at space cta lo hi
  have sites := (publication_writers (b := 212992+g%L.block%4*4+b) hp hX store space.symm
    (by omega) (by omega)).1 (by omega) (by omega)
  rcases sites with rfl|rfl
  · obtain ⟨j,_,sz,wl,_⟩ := Prologue.Export.pair_bytes hp hX store
    rw [wl] at cta lo hi
    rw [sz] at hi
    dsimp only at cta lo hi
    have := j.isLt
    have eq : j.val=g%L.block%4 := by omega
    exact ⟨h,v,rfl,cta.symm,by rw [wl,rl,eq,cta]; congr 1; omega,sz,.inl ⟨by omega,store⟩⟩
  · obtain ⟨wl,sz⟩ := Softmax.Export.scratch_store hp hX store
    rw [wl] at cta lo hi
    rw [sz] at hi
    dsimp only at cta lo hi
    have eq : h%L.block/32%4=g%L.block%4 := by omega
    exact ⟨h,v,rfl,cta.symm,by rw [wl,rl,eq,cta],sz,.inr ⟨eq,store⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
