-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Iface.CopyIndex
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
public import Lemmas.Flow.NotTensor
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyCount
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Loader.Export.PacketIndex

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k1 k2 pc1 pc2 : Nat}

/-- **Two loader copies of one use that write one byte are one event.** The use of a copy is
its count of earlier issues to the slot's barrier over eight; within a use the copies are at
distinct sites with disjoint boxes, and one site is visited once per use. -/
public theorem copy_same_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (warp : g%L.block/32=6)
    {a1 a2 sp1 sp2 x1 y1 z1 x2 y2 z2 l σ}
    (e1 : X.get (g,k1)=some ⟨pc1,.tensorIssue a1 sp1⟩)
    (e2 : X.get (g,k2)=some ⟨pc2,.tensorIssue a2 sp2⟩)
    (b1 : sp1.mbar = Iface.kvReadyLoc L (g/L.block) σ)
    (b2 : sp2.mbar = Iface.kvReadyLoc L (g/L.block) σ)
    (same : ((X.tr g).take k1).countP (issuesTo sp1.mbar) / 8 =
      ((X.tr g).take k2).countP (issuesTo sp2.mbar) / 8)
    (w1 : TensorCopy.writeLoc sp1 x1 y1 z1 = some l)
    (w2 : TensorCopy.writeLoc sp2 x2 y2 z2 = some l) : k1 = k2 := by
  obtain ⟨site1,pos1,c1,r1⟩ := copy_count hp hX hf e1 warp b1
  obtain ⟨site2,pos2,c2,r2⟩ := copy_count hp hX hf e2 warp b2
  have i1 := Iface.copyIndex_lt site1
  have i2 := Iface.copyIndex_lt site2
  rw [c1, c2] at same
  have vis : Iface.ringVisits (Iface.preloadCount Q L (g/L.block))
      (pollRound 2374 ((X.tr g).take k1)-1) σ =
      Iface.ringVisits (Iface.preloadCount Q L (g/L.block))
        (pollRound 2374 ((X.tr g).take k2)-1) σ := by omega
  have round : pollRound 2374 ((X.tr g).take k1) = pollRound 2374 ((X.tr g).take k2) := by
    unfold Iface.ringVisits at vis
    have := σ.isLt
    omega
  obtain ⟨s1,bar1,d1⟩ := copy_dest hp hX hf e1 site1
  obtain ⟨s2,bar2,d2⟩ := copy_dest hp hX hf e2 site2
  have slot (s : Fin 3) (h : Iface.kvReadyLoc L (g/L.block) s = Iface.kvReadyLoc L (g/L.block) σ) :
      s.val = σ.val := by
    simp only [Iface.kvReadyLoc, Iface.kvReady, Loc.mk.injEq, true_and,
      Nat.add_left_cancel_iff] at h
    omega
  have t1 := slot s1 (bar1.symm.trans b1)
  have t2 := slot s2 (bar2.symm.trans b2)
  obtain ⟨_,_,lo1,hi1⟩ := d1 w1
  obtain ⟨_,_,lo2,hi2⟩ := d2 w2
  have pc : pc1 = pc2 := by
    by_contra ne
    rcases Iface.copyOff_apart site1 site2 ne with h | h <;> omega
  subst pc
  have member : pc1 ∈ [2378,2389,2391,2394,2396,2404,2406,2410,2412] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at site1 ⊢
    omega
  exact packet_unique hp hX hf words warp e1 e2 member
    rfl (by simp) (by simp) rfl rfl round

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
