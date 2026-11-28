-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Tmem.AccessCp
public import Lemmas.Flow.Regs
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.FinalOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Common.Export.LdWait
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DeallocSite

/-! # A load or store is waited for before every deallocation of its CTA

The deallocation is a data lane's event after its final `bar.sync 0` (pc 2850). A load or store
is a data lane's, before its own final rendezvous, and followed by its wait (`Export.ld_wait`,
`Export.st_wait`). The final rendezvous of the two lanes have the same ordinal
(`final_ordinal`), so the wait is before the deallocation. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Proof PTX.Tmem.Pair

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Every event of a data lane before its final rendezvous is before the deallocation. -/
private theorem before_dealloc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {h kd pc grp dst da n y ke ev}
    (hd : X.get (h,kd) = some ⟨pc,.tc (.resource grp dst (.dealloc da n))⟩)
    (cta : h / L.block = y / L.block) (ly : y % L.block < 128)
    (hy : X.get (y,ke) = some ev) (nu : ∀ f, ev.kind ≠ .ub f) (early : Lib.afterFinal ev.pc = 0)
    (other : Lib.finalSync ev.pc = false) :
    ∃ u p, ke < u ∧ X.get (y,u) = some ⟨p,.bar 0 none .sync⟩ ∧
      ∀ w, w < u → baseCausality L X (y,w) (h,kd) := by
  obtain ⟨lh,-,u',pch,hu',hh,fh,ord⟩ := dealloc_site hp hX hf base hd
  have len : kd < (X.tr h).length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨u,p,hyu,fy,ordy⟩ := final_of_passed hp hX hh (by omega) ord cta.symm
  refine ⟨u,p,Export.before_final_sync hp hX hyu ordy hy nu early other,hyu,fun w hw => ?_⟩
  exact before_final_after_final hp hX hf safe cta ly lh hyu hh fy fh hw hu' len

/-- **`LifeCp.ldst_before_dealloc`**: a load (store) is waited for before every deallocation of
its CTA. -/
public theorem ldst_before_dealloc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {e d : EvId} {a : Nat} {vals : List Value}
    {sh : TcShape} {pc : Nat} {grp : CtaGroup} {dst : Option Loc} {da n : Nat}
    (hd : X.get d = some ⟨pc,.tc (.resource grp dst (.dealloc da n))⟩)
    (hc : d.1 / L.block = e.1 / L.block) :
    (X.TLd e a vals sh → TcMma.WaitBefore L X .waitLd e d) ∧
      (X.TSt e a vals sh → TcMma.WaitBefore L X .waitSt e d) := by
  obtain ⟨h,kd⟩ := d
  obtain ⟨y,ke⟩ := e
  refine ⟨fun ⟨pcl,hld⟩ => ?_,fun ⟨pcs,hst⟩ => ?_⟩
  · have ly := Export.tc_data_lane hp hX hf hld (by rfl)
    obtain ⟨i,k,-,hpc,-⟩ := ld_static hp hX hf base hld
    have hpc' : pcl = 1265 ∨ pcl = 2260 ∨ pcl = 2607 := by omega
    obtain ⟨u,p,hke,hyu,caus⟩ := before_dealloc hp hX hf safe base hd hc ly hld
      (fun f h => nomatch h) (by rcases hpc' with h|h|h <;> simp [h, Lib.afterFinal])
      (by rcases hpc' with h|h|h <;> simp [h, Lib.finalSync])
    have hlen : ke + 1 < (X.tr y).length := by
      have : u < (X.tr y).length := (List.getElem?_eq_some_iff.mp hyu).1
      omega
    obtain ⟨e1,g1⟩ : ∃ e1, X.get (y,ke+1) = some e1 :=
      ⟨_,(List.getElem?_eq_some_iff.mpr ⟨hlen,rfl⟩)⟩
    obtain ⟨pcw,rfl⟩ := Export.ld_wait hp hX hf (noUbUpto hX hyu nofun (by omega)) hpc' hld g1
    have lt : ke + 1 < u := by
      rcases Nat.lt_or_ge (ke + 1) u with h|h
      · exact h
      · obtain rfl : u = ke + 1 := by omega
        rw [g1] at hyu
        cases hyu
    exact ⟨(y,ke+1),⟨pcw,g1⟩,rfl,Nat.lt_succ_self _,.inl (caus _ lt)⟩
  · have ly := Export.tc_data_lane hp hX hf hst (by rfl)
    obtain ⟨i,k,-,hpc⟩ := st_static hp hX hf base hst
    have hpc' : pcs = 1009 ∨ pcs = 2328 := by omega
    obtain ⟨u,p,hke,hyu,caus⟩ := before_dealloc hp hX hf safe base hd hc ly hst
      (fun f h => nomatch h) (by rcases hpc' with h|h <;> simp [h, Lib.afterFinal])
      (by rcases hpc' with h|h <;> simp [h, Lib.finalSync])
    have hlen : ke + 1 < (X.tr y).length := by
      have : u < (X.tr y).length := (List.getElem?_eq_some_iff.mp hyu).1
      omega
    obtain ⟨e1,g1⟩ : ∃ e1, X.get (y,ke+1) = some e1 :=
      ⟨_,(List.getElem?_eq_some_iff.mpr ⟨hlen,rfl⟩)⟩
    obtain ⟨pcw,rfl⟩ := Export.st_wait hp hX hf (noUbUpto hX hyu nofun (by omega)) hpc' hst g1
    have lt : ke + 1 < u := by
      rcases Nat.lt_or_ge (ke + 1) u with h|h
      · exact h
      · obtain rfl : u = ke + 1 := by omega
        rw [g1] at hyu
        cases hyu
    exact ⟨(y,ke+1),⟨pcw,g1⟩,rfl,Nat.lt_succ_self _,.inl (caus _ lt)⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
