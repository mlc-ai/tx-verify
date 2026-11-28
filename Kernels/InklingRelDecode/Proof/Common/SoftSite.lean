-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Common.FollowControl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

/-- The role state at a nonfaulting event of the Softmax interior. -/
theorem at_site {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (clean : ∀ f, ev.kind≠.ub f) (lo : 574<ev.pc) (hi : ev.pc<2331) :
    ∃ w ent d n, Frame.stateAt (thread Q L) X g k=some (some (softState w ent d n)) ∧
      ev.pc=d.site.pc := by
  have nu : ∀ pc f, ev ≠ ⟨pc,.ub f⟩ := fun _ f eq => clean f (congrArg Event.kind eq)
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he nu ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have loc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  obtain ⟨w,ent,d,n,rfl⟩ := (loc ▸ state_role s).softmax lo hi
  exact ⟨w,ent,d,n,hs,loc⟩

end PTX.Kernels.InklingRelDecode.Proof
