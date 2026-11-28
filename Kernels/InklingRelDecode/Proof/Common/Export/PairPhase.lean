-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Regs
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.WorkerCall
import Kernels.InklingRelDecode.Proof.Common.Where

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof PTX.Frame

private theorem loader_phase (s : Loader.Site) (h : s.pc=2345 ∨ s.pc=2423) :
    Loader.publicationPhase s=1 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_phase (s : Mma.Site) (h : s.pc=2345 ∨ s.pc=2423) :
    Mma.publicationPhase s=1 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- Both count loads precede the first scratch reuse. At the later dispatch
every worker reads the exit byte and reaches neither count load. -/
public theorem pair_phase {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨p,.rd a bs⟩) (site : p=2345 ∨ p=2423) :
    ((X.tr g).take k).countP (Execution.isBarId 1)=1 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change p=_ at pc
  obtain ⟨w,x,r,d,n,rfl⟩ := (pc ▸ state_role s).worker (by omega) (by omega) (by omega)
  have call := worker_called hp hX words (List.getElem?_eq_some_iff.mp he).1.le hs
  rw [publication_prefix hp hX hg (Frame.noUbBefore_of_get hX he) hs]
  cases r with
  | loader round =>
    obtain ⟨_,rfl⟩ := call
    change p=d.site.pc at pc
    change 0+Loader.publicationPhase d.site=1
    rw [Nat.zero_add]
    exact loader_phase _ (pc ▸ site)
  | mma round =>
    obtain ⟨_,rfl⟩ := call
    change p=d.site.pc at pc
    change 0+Mma.publicationPhase d.site=1
    rw [Nat.zero_add]
    exact mma_phase _ (pc ▸ site)

end PTX.Kernels.InklingRelDecode.Proof.Export
