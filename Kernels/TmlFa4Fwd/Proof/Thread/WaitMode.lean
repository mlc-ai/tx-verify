-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
import Lemmas.Flow.NotBulk
import Lemmas.Flow.WaitAcquire
import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow AsyncCopy

private def acquiringPoll (op : Op) : Bool :=
  match op with
  | .mbarWait _ _ _ _ acquire _ => acquire
  | _ => true

private theorem acquiringPolls :
    kernel.code.all (fun i => acquiringPoll i.op) = true := by
  decide +kernel

/-- Every actual mbarrier poll is an acquire in this kernel. -/
theorem actualPollAcquires {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc parity : Nat} {loc : Loc}
    {ok acquire : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .wait loc parity ok acquire scope⟩) : acquire = true := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFires⟩
  · cases hBad
  obtain ⟨_, _, _, _, _, hOp, _⟩ := fires_wait_flags hFires rfl
  have hAcq := List.all_eq_true.mp acquiringPolls ins (List.mem_of_getElem? hCode)
  simpa only [hOp, acquiringPoll] using hAcq

/-- Every observed asynchronous completion uses an acquire in this kernel. -/
theorem completionObservationAcquires {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i wait : EvId}
    {part : Part} {acquire : Bool} {scope : MbarScope}
    (h : AsyncObserved X i part wait acquire scope) : acquire = true := by
  obtain ⟨_, _, _, ⟨_, _, he⟩, _⟩ := h
  exact actualPollAcquires hX he

end PTX.Kernels.TmlFa4Fwd.Thread
