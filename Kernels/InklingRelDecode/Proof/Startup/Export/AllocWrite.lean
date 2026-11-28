-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl

namespace PTX.Kernels.InklingRelDecode.Proof.Startup.Export
open PTX PTX.Flow PTX.Proof

/-- The allocator's result store occupies exactly the first shared word. -/
public theorem alloc_write {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨11,.wr a bs⟩) :
    a.loc = ⟨.shared,g/L.block,L.sharedBase⟩ ∧ a.size=4 := by
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨⟨site,tm,x,w⟩,n,rfl⟩ := (pc ▸ state_role s).startup (by decide : 11<27)
  change 11=site.pc at pc
  have shape := start_ev hp hX he hs (by simp)
  have sites : site=.alloc ∨ site=.allocWr := by
    cases site <;> first | exact .inl rfl | exact .inr rfl | contradiction |
      (rename_i r; cases r <;> contradiction)
  rcases sites with rfl|rfl
  · cases shape
  · obtain ⟨_,_,eq⟩ := shape
    cases eq
    exact ⟨rfl,rfl⟩

/-- The recorded base word is read at the allocator's four-byte location. -/
public theorem base_address {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨13,.rd a bs⟩) :
    a.loc = ⟨.shared,g/L.block,L.sharedBase⟩ ∧ a.size=4 := by
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨⟨site,tm,x,w⟩,n,rfl⟩ := (pc ▸ state_role s).startup (by decide : 13<27)
  change 13=site.pc at pc
  have shape := start_ev hp hX he hs (by simp)
  have only : site=.ld0 := by
    cases site <;> first | rfl | contradiction | (rename_i r; cases r <;> contradiction)
  subst site
  obtain ⟨_,_,eq,loc,size,_⟩ := shape
  cases eq
  exact ⟨loc,size⟩

end PTX.Kernels.InklingRelDecode.Proof.Startup.Export
