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

/-- The state of a thread at a Softmax event, with the entry it carries. -/
theorem softmax_occ_entry {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (hu : ∀ f, ev.kind ≠ .ub f) (lo : 574 < ev.pc) (hi : ev.pc < 2331) :
    ∃ w ent d n t ins u, Frame.stateAt (thread Q L) X g k = some (some (softState w ent d n)) ∧
      (Softmax.Control.code ent L g).AtD d t ∧ Softmax.Control.Inv ent (g%L.block) d ∧
      ev.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u := by
  obtain ⟨s,hs,pc,t,ins,u,ht,hI,hc,fire⟩ := he.site hp hX hf hu
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax lo hi
  exact ⟨w,ent,d,n,t,ins,u,hs,ht,hI.1,pc,hc,fire⟩

theorem softmax_event_entry {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : X.get (g,k) = some ev)
    (hu : ∀ f, ev.kind ≠ .ub f) (lo : 574 < ev.pc) (hi : ev.pc < 2331) :
    ∃ w ent d n t ins u, Frame.stateAt (thread Q L) X g k = some (some (softState w ent d n)) ∧
      (Softmax.Control.code ent L g).AtD d t ∧ Softmax.Control.Inv ent (g%L.block) d ∧
      ev.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev u :=
  softmax_occ_entry hp hX hf (.inl he) hu lo hi

end PTX.Kernels.InklingRelDecode.Proof
