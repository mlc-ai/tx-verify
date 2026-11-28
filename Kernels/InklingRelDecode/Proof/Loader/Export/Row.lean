-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Loader
public import Kernels.InklingRelDecode.Proof.Loader.Export.Mbar
import Kernels.InklingRelDecode.Proof.Loader.Export.Count
import Lemmas.Protocol.MbarRowSource
import Lemmas.Protocol.MbarRowKind

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX MbarRow PTX.MbarRow

private abbrev copies := [2389,2391,2394,2396,2404,2406,2410,2412]

public theorem mbarRow {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : MbarRow.Loader Q L X := by
  intro g k e l _ he hat hm
  obtain ⟨hw,lo,hi⟩ := hat
  obtain ⟨s,hs,hpc,t,ins,u,ht,_,hop,fire⟩ := region_source loader_sites hX he hm lo hi
  rw [← ht] at fire
  have kinds : ∀ a ∈ loaderSites,
      (a.pc = 2374 ∧ a.shape = .wait (.reg 579)) ∨
      (a.pc = 2378 ∧ a.shape = .arrive (.imm 65536)) ∨
      (a.pc ∈ copies ∧ a.shape = .issue .tile) := by decide
  obtain ⟨pc,kd⟩ := e
  change s.pc = pc at hpc
  rcases kinds s hs with ⟨hs',h⟩ | ⟨hs',h⟩ | ⟨hs',h⟩
  · obtain rfl : pc = 2374 := hpc.symm.trans hs'
    obtain ⟨obj,q,ok,acq,sc,rfl⟩ := emits_wait (h ▸ hop) fire
    obtain rfl : l = obj := hm
    obtain ⟨rfl,rfl,rfl,rfl⟩ := poll hp hX hf hw (.inl he)
    exact .emptyWait rfl rfl ⟨ok,rfl⟩
  · obtain rfl : pc = 2378 := hpc.symm.trans hs'
    obtain ⟨obj,tx,c,rel,sc,rfl⟩ := emits_arrive (h ▸ hop) fire
    obtain rfl : l = obj := hm
    obtain ⟨hn,hh⟩ := packet_credit hp hX hf hw he (List.mem_cons_self) (.inl ⟨_,_,_,_,_,rfl⟩)
    rcases hh with ⟨_,hk⟩ | ⟨_,hk,_⟩
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := Kind.arrive.inj hk
      exact .readyArrive rfl hn rfl rfl
    · cases hk
  · have hcopy : pc ∈ copies := hpc ▸ hs'
    obtain ⟨a,sp,rfl⟩ := emits_issue (h ▸ hop) fire
    obtain rfl : sp.mbar = l := hm
    obtain ⟨hn,hh⟩ := packet_credit hp hX hf hw he (List.mem_cons_of_mem _ hcopy)
      (.inr ⟨_,_,rfl⟩)
    rcases hh with ⟨_,hk⟩ | ⟨sp',hk,hl,hb⟩
    · cases hk
    · obtain ⟨rfl,rfl⟩ := Kind.tensorIssue.inj hk
      exact .readyCopy hcopy hn hl ⟨_,_,rfl,rfl,hb⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
