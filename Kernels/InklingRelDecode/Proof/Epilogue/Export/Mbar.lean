-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Epilogue
import Kernels.InklingRelDecode.Proof.Common.EpilogueEvent
import Kernels.InklingRelDecode.Proof.Epilogue.Shape
import Kernels.InklingRelDecode.Proof.Epilogue.Ledger
import Lemmas.Protocol.MbarRowSource

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow MbarRow PTX.MbarRow

/-- **The epilogue's poll that occurs** is of the final object. -/
public theorem wait_occ {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k ev)
    (nu : ∀ f, ev.kind≠.ub f) (pc : ev.pc=2565) :
    ∃ ok, ev.kind = .wait (loc L g Iface.oFinal) 0 ok true .cta := by
  obtain ⟨ent,d,t,ins,u,ht,eq,hc,fire⟩ := epilogue_occ hp hX hf he nu (by omega) (by omega)
  obtain ⟨s,v⟩ := d
  have wait : s = .wait := by
    have h : s.pc=2565 := eq.symm.trans pc
    by_contra ne
    exact final_only s ne h
  exact object_shape hp ht hc fire wait

public theorem mbarRow {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : MbarRow.Epilogue Q L X := by
  intro g k ev l _ he hat hm
  have pc : ev.pc=2565 := by
    rcases hat.2 with ⟨lo,hi⟩|⟨lo,hi⟩
    · obtain ⟨s,mem,hpc,_⟩ := region_source epilogue_sites hX he hm lo hi
      simp [epilogueSites] at mem
      exact hpc.symm.trans (congrArg PTX.MbarRow.Site.pc mem)
    · obtain ⟨_,h,_⟩ := region_source epilogue_sites_1 hX he hm lo hi
      cases h
  have nu : ∀ f, ev.kind≠.ub f := by
    have h := objectKind hm
    intro f eq; rw [eq] at h; exact h.elim
  obtain ⟨ok,kind⟩ := wait_occ hp hX hf (.inl he) nu pc
  have addr : l = loc L g Iface.oFinal := by
    obtain ⟨p,kd⟩ := ev
    change kd=_ at kind
    cases kind
    exact hm
  exact .finalWait pc addr ⟨ok,addr ▸ kind⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
