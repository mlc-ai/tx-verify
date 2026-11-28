-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.StartupEvents
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

theorem prologue_occ {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (hu : ∀ f, ev.kind≠.ub f) (lo : 27<ev.pc) (hi : ev.pc<574) :
    ∃ w d t ins u, (Prologue.Control.code Q L g w).AtD d t ∧
      Prologue.Control.Inv (g%L.block) d ∧ ev.pc=d.site.pc ∧ kernel.code[d.site.pc]?=some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u ∧ g%L.block<128 ∧
      Prologue.History Q L g d (proCounts L g fun c => ((X.tr g).take k).countP (cls c)) := by
  have hg := he.lt hX
  obtain ⟨s,hs,pc,t,ins,u,ht,inv,hc,fire⟩ := he.site hp hX hf hu
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role s).prologue lo hi
  obtain ⟨warp,hist⟩ := ((hf g hg k).2 _ hs (prefix_ub_zero hs (he.noUb hX))).2
  have eq : n = fun c => ((X.tr g).take k).countP (cls c) := funext (fcount hs)
  exact ⟨w,d,t,ins,u,ht,inv.1.1,pc,hc,fire,warp,eq ▸ hist⟩

theorem prologue_event {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : X.get (g,k)=some ev)
    (hu : ∀ f, ev.kind≠.ub f) (lo : 27<ev.pc) (hi : ev.pc<574) :
    ∃ w d t ins u, (Prologue.Control.code Q L g w).AtD d t ∧
      Prologue.Control.Inv (g%L.block) d ∧ ev.pc=d.site.pc ∧ kernel.code[d.site.pc]?=some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u ∧ g%L.block<128 ∧
      Prologue.History Q L g d (proCounts L g fun c => ((X.tr g).take k).countP (cls c)) :=
  prologue_occ hp hX hf (.inl he) hu lo hi

end PTX.Kernels.InklingRelDecode.Proof
