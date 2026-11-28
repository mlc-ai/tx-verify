-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.BarAfter
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # After a barrier-0 event the lane's clock is later -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Sched

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **After a barrier-0 event the lane's clock is later.** -/
public theorem bar0_after {j pc cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, j) = some ⟨pc, .bar 0 cnt md⟩) :
    timeAt (schedule Q L) X g j < timeAt (schedule Q L) X g (j + 1) := by
  have hg := Frame.lt_of_get hX he
  have nub := Frame.noUbBefore_of_get hX he
  have nu : ∀ f, (⟨pc, .bar 0 cnt md⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ f h => nu f (congrArg Event.kind h)) (hf g hg j)
  have hpc : pc = (thread Q L g).pc s :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  have site : (thread Q L g).pc s ∈ BarRow.fullZeroSites ++ BarRow.halfZeroSites := by
    obtain ⟨_, one | full | half⟩ := Lib.recorded_bar hX hp.block he
    · cases one.1
    · exact hpc ▸ List.mem_append_left _ full.2.2
    · exact hpc ▸ List.mem_append_right _ half.2.2
  have tab := reached_table hf hg nub hs
  rw [time_at hs]
  rcases h1 : Frame.stateAt (thread Q L) X g (j + 1) with _ | _ | s1
  · rw [time_dead hs h1]; omega
  · exact absurd h1 ((hf g hg (j + 1)).1)
  · rw [time_at h1]
    exact TcState.zero_after tab (TcState.step_of he hs h1) site

end PTX.Kernels.InklingRelDecode.Proof.Export
