-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Lib.WorkerBarSchedule
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.WorkerBar
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.FollowControl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame

/-- **The pc of a worker lane's rendezvous by its ordinal.** At a barrier event of a thread of
warps 4 to 7 the pc is the entry of `Lib.workerBar` at the number of earlier barrier events. -/
theorem worker_bar_pc {Q L m X g k pc id cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k) = some ⟨pc,.bar id cnt md⟩) (lw : 128 ≤ g%L.block) :
    let es := (X.tr g).take k
    pc = Lib.workerBar (g%L.block/32) (es.countP (Execution.isBarId 0) +
      es.countP (Execution.isBarId 1)) := by
  have hg := Frame.lt_of_get hX he
  have nu := Frame.noUbBefore_of_get hX he
  have clean : ∀ f, (⟨pc,.bar id cnt md⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨s,hs,-⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => clean f (congrArg Event.kind eq))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have pcs := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  have c0 : s.2 (.bar 0) = ((X.tr g).take k).countP (Execution.isBarId 0) := by
    rw [fcount hs, cls_bar0]
  have c1 := publication_prefix hp hX hg nu hs
  have site : (thread Q L g).pc s ∈ Lib.barOneSites ∨
      Lib.zeroSite ((thread Q L g).pc s) = true := by
    change pc = _ at pcs
    rw [← pcs]
    obtain ⟨-, one | full | half⟩ := Lib.recorded_bar hX hp.block he
    · exact .inl one.2.2
    · exact .inr (decide_eq_true (List.mem_append_left _ full.2.2))
    · exact .inr (decide_eq_true (List.mem_append_right _ half.2.2))
  have key := worker_bar_state hp hX words hk hs nu lw site
  change pc = _ at pcs
  simp only
  rw [pcs, key, c0, c1]

end PTX.Kernels.InklingRelDecode.Proof.Export
