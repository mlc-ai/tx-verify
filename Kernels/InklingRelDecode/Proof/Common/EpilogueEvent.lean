-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.StartupEvents
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

/-- The state of a thread at an epilogue event, with the entry it carries. -/
theorem epilogue_occ_entry {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (nu : ∀ f, ev.kind≠.ub f) (lo : 2565≤ev.pc) (hi : ev.pc<2853) :
    ∃ w e d n t ins u, Frame.stateAt (thread Q L) X g k = some (some (epiState w e d n)) ∧
      (Epilogue.Control.code (epiEntry e (g%L.block)) L g).AtD d t ∧
      Epilogue.Control.Inv (epiEntry e (g%L.block)) (g%L.block) d ∧ ev.pc=d.site.pc ∧
      kernel.code[d.site.pc]?=some ins ∧ Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op)
        ev u := by
  have hg := he.lt hX
  obtain ⟨s,hs,pc,t,ins,u,ht,hI,hc,fire⟩ := he.site hp hX hf nu
  have inv := ((hf g hg k).2 _ hs (prefix_ub_zero hs (he.noUb hX))).1
  obtain ⟨w,e,d,n,rfl⟩ := (pc ▸ state_role s).epilogue lo hi inv
  exact ⟨w,e,d,n,t,ins,u,hs,ht,inv,pc,hc,fire⟩

theorem epilogue_event_entry {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : X.get (g,k)=some ev)
    (nu : ∀ f, ev.kind≠.ub f) (lo : 2565≤ev.pc) (hi : ev.pc<2853) :
    ∃ w e d n t ins u, Frame.stateAt (thread Q L) X g k = some (some (epiState w e d n)) ∧
      (Epilogue.Control.code (epiEntry e (g%L.block)) L g).AtD d t ∧
      Epilogue.Control.Inv (epiEntry e (g%L.block)) (g%L.block) d ∧ ev.pc=d.site.pc ∧
      kernel.code[d.site.pc]?=some ins ∧ Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op)
        ev u :=
  epilogue_occ_entry hp hX hf (.inl he) nu lo hi

theorem epilogue_occ {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (nu : ∀ f, ev.kind≠.ub f) (lo : 2565≤ev.pc) (hi : ev.pc<2853) :
    ∃ ent d t ins u, (Epilogue.Control.code ent L g).AtD d t ∧ ev.pc=d.site.pc ∧
      kernel.code[d.site.pc]?=some ins ∧ Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op)
        ev u := by
  obtain ⟨_,e,d,_,t,ins,u,_,ht,_,pc,hc,fire⟩ := epilogue_occ_entry hp hX hf he nu lo hi
  exact ⟨_,d,t,ins,u,ht,pc,hc,fire⟩

theorem epilogue_event {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : X.get (g,k)=some ev)
    (nu : ∀ f, ev.kind≠.ub f) (lo : 2565≤ev.pc) (hi : ev.pc<2853) :
    ∃ ent d t ins u, (Epilogue.Control.code ent L g).AtD d t ∧ ev.pc=d.site.pc ∧
      kernel.code[d.site.pc]?=some ins ∧ Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op)
        ev u :=
  epilogue_occ hp hX hf (.inl he) nu lo hi

end PTX.Kernels.InklingRelDecode.Proof
