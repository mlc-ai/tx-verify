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
open PTX PTX.Flow PTX.Proof

theorem softmax_occ {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (hu : ∀ f, ev.kind ≠ .ub f) (lo : 574 < ev.pc) (hi : ev.pc < 2331) :
    ∃ ent d t ins u, (Softmax.Control.code ent L g).AtD d t ∧
      Softmax.Control.Inv ent (g%L.block) d ∧
      ev.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u ∧
      Softmax.Ref (g%L.block) d ⟨pollRound 1257 ((X.tr g).take k),pollRound 2239 ((X.tr g).take k),
        ((X.tr g).take k).countP (fun a => a.pc == 1013)⟩ := by
  have hg := he.lt hX
  obtain ⟨s,hs,pc,t,ins,u,ht,hI,hc,fire⟩ := he.site hp hX hf hu
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax lo hi
  have ref := ((hf g hg k).2 _ hs (prefix_ub_zero hs (he.noUb hX))).2
  change Softmax.Ref _ d (softCounts n) at ref
  refine ⟨ent,d,t,ins,u,ht,hI.1,pc,hc,fire,?_⟩
  have cnt (c : Cls) : n c = ((X.tr g).take k).countP (cls c) := fcount hs c
  change Softmax.Ref _ d ⟨((X.tr g).take k).countP (cls (.poll 1257)),
    ((X.tr g).take k).countP (cls (.poll 2239)),((X.tr g).take k).countP (cls (.atPc 1013))⟩
  rw [← cnt (.poll 1257), ← cnt (.poll 2239), ← cnt (.atPc 1013)]
  exact ref

theorem softmax_event {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : X.get (g,k) = some ev)
    (hu : ∀ f, ev.kind ≠ .ub f) (lo : 574 < ev.pc) (hi : ev.pc < 2331) :
    ∃ ent d t ins u, (Softmax.Control.code ent L g).AtD d t ∧
      Softmax.Control.Inv ent (g%L.block) d ∧
      ev.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u ∧
      Softmax.Ref (g%L.block) d ⟨pollRound 1257 ((X.tr g).take k),pollRound 2239 ((X.tr g).take k),
        ((X.tr g).take k).countP (fun a => a.pc == 1013)⟩ :=
  softmax_occ hp hX hf (.inl he) hu lo hi

end PTX.Kernels.InklingRelDecode.Proof
