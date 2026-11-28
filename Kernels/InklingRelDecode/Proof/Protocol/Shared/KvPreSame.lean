-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.PreloadBox
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar
import Kernels.InklingRelDecode.Proof.Prologue.Export.CopyFoot
import Kernels.InklingRelDecode.Proof.Prologue.Export.BroadcastAt
import Kernels.InklingRelDecode.Proof.Common.Export.PshRecv
import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof

private theorem half_of_warp {w : Nat} (small : w<2) :
    (Lib.word (b32 w)).toNat%2=w%2 := by
  have : w=0 ∨ w=1 := by omega
  rcases this with rfl|rfl <;> decide

/-- **Two prologue preload copies of one CTA that write one byte are one event.** The box of a
copy is fixed by its site and the parity of its warp (the broadcast of the warp index), the
elected lane of a warp is unique, and a site is visited once. -/
theorem preload_same_use {Q L m X g1 k1 pc1 a1 sp1 g2 k2 pc2 a2 sp2 x1 y1 z1 x2 y2 z2 l}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X)
    (e1 : X.get (g1,k1)=some ⟨pc1,.tensorIssue a1 sp1⟩)
    (e2 : X.get (g2,k2)=some ⟨pc2,.tensorIssue a2 sp2⟩)
    (s1 : pc1∈Iface.preloadSites) (s2 : pc2∈Iface.preloadSites)
    (cta : g1/L.block=g2/L.block)
    (w1 : TensorCopy.writeLoc sp1 x1 y1 z1=some l)
    (w2 : TensorCopy.writeLoc sp2 x2 y2 z2=some l) : g1=g2 ∧ k1=k2 := by
  have range (pc : Nat) (s : pc∈Iface.preloadSites) : 27≤pc ∧ pc<574 := by
    simp only [Iface.preloadSites,List.mem_cons,List.not_mem_nil,or_false] at s
    omega
  obtain ⟨σ1,bar1,-⟩ := Prologue.Export.preload_dest hp hX e1 s1
  obtain ⟨σ2,bar2,-⟩ := Prologue.Export.preload_dest hp hX e2 s2
  obtain ⟨-,-,warp1,elected1,-⟩ := rows.prologue.1.copy (range pc1 s1).1 (range pc1 s1).2 e1 bar1
  obtain ⟨-,-,warp2,elected2,-⟩ := rows.prologue.1.copy (range pc2 s2).1 (range pc2 s2).2 e2 bar2
  obtain ⟨p1,a1',ok1,i1,r1,m1,get1,box1⟩ := Prologue.Export.preload_box hp hX e1 s1
  obtain ⟨p2,a2',ok2,i2,r2,m2,get2,box2⟩ := Prologue.Export.preload_box hp hX e2 s2
  have rv1 := Export.psh_recv hp hX hf get1 m1
  have rv2 := Export.psh_recv hp hX hf get2 m2
  rw [rv1,half_of_warp warp1] at box1
  rw [rv2,half_of_warp warp2] at box2
  obtain ⟨lo1,hi1⟩ := box1 w1
  obtain ⟨lo2,hi2⟩ := box2 w2
  have same := Iface.preloadOff_apart s1 s2 (by omega : (g1%L.block/32)%2<2)
    (by omega : (g2%L.block/32)%2<2) (by omega) (by omega)
  obtain ⟨hpc,hhalf⟩ := same
  have warp : g1%L.block/32=g2%L.block/32 := by omega
  have hg1 := Frame.lt_of_get hX e1
  have hg2 := Frame.lt_of_get hX e2
  obtain ⟨ev1,hev1,rest1⟩ := elected1
  obtain ⟨ev2,hev2,rest2⟩ := elected2
  have lead1 := Protocol.KV.leader_eq hX hg1 ⟨ev1,(List.take_sublist _ _).subset hev1,rest1⟩
  have lead2 := Protocol.KV.leader_eq hX hg2 ⟨ev2,(List.take_sublist _ _).subset hev2,rest2⟩
  rw [cta,warp] at lead1
  obtain rfl : g1=g2 := lead1.symm.trans lead2
  subst hpc
  refine ⟨rfl,?_⟩
  by_contra ne
  have fresh (k) (pc a sp) (e : X.get (g1,k)=some ⟨pc,.tensorIssue a sp⟩)
      (s : pc∈Iface.preloadSites) := Prologue.Export.preload_fresh hp hX hf e s
  rcases Nat.lt_or_gt_of_ne ne with lt|lt
  · have get : ((X.tr g1).take k2)[k1]?=some ⟨pc1,.tensorIssue a1 sp1⟩ := by
      rw [List.getElem?_take_of_lt lt]; exact e1
    have := fresh k2 pc1 a2 sp2 e2 s1
    have pos := (List.countP_pos_iff (p := fun e : Event => e.pc==pc1)).mpr
      ⟨_,List.mem_of_getElem? get,
      (by show (pc1==pc1)=true; exact beq_self_eq_true _)⟩
    omega
  · have get : ((X.tr g1).take k1)[k2]?=some ⟨pc1,.tensorIssue a2 sp2⟩ := by
      rw [List.getElem?_take_of_lt lt]; exact e2
    have := fresh k1 pc1 a1 sp1 e1 s1
    have pos := (List.countP_pos_iff (p := fun e : Event => e.pc==pc1)).mpr
      ⟨_,List.mem_of_getElem? get,
      (by show (pc1==pc1)=true; exact beq_self_eq_true _)⟩
    omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
