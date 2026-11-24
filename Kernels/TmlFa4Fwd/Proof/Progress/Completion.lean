-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Resources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX

/-- Once the threads exit, only asynchronous effects can remain pending. -/
theorem completeOfExitsAndEffects {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    (hExit : ∀ g < l.threads, Thread.Exited X g) (hEffects : AsyncDrained X) :
    Complete l X := by
  refine ⟨?_, hEffects, ?_⟩
  · exact fun g hg => .inr ((hExit g hg).lastEvent hX hg)
  · intro i _ group dst request he
    exact Thread.resourceReturnedBeforeExit hX ⟨_, he, rfl⟩
      (hExit i.1 (PTX.Proof.event_thread_lt hX he))

end PTX.Kernels.TmlFa4Fwd.Progress
