-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Lemmas.Flow.WaitAcquire
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Async.BulkExecution

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow

noncomputable section

private def ctaPoll (op : Op) : Bool :=
  match op with
  | .mbarWait _ _ _ _ _ .cta => true
  | op => !isMbarPoll op

private theorem ctaPollCode : kernel.code.all (fun i => ctaPoll i.op) = true := by
  decide +kernel

/-- Successful and failing polls have CTA scope, including those selected by the poll rules. -/
theorem actualPollScope {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc q : Nat} {mb : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .wait mb q ok acq scope⟩) : scope = .cta := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, ins, _, _, hCode, hf⟩
  · cases hf
  obtain ⟨dst, base, off, par, sc, hIns, _⟩ := fires_wait_flags hf rfl
  have hs := List.all_eq_true.mp ctaPollCode ins (List.mem_of_getElem? hCode)
  rw [hIns] at hs hf
  have hSc : sc = .cta := by
    cases sc <;> simp [ctaPoll, isMbarPoll] at hs ⊢
  subst sc
  have hW : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, tmaTmpl, widenMbarScope, hW, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure] at hf
  cases hm : mbarLoc l i.1 t base off with
  | error f => simp [hm, ofExec, Fires] at hf
  | ok a =>
    cases hq : readBits l i.1 t 32 par with
    | error f => simp [hm, hq, ofExec, Fires] at hf
    | ok n =>
      simp only [hm, hq, ofExec, Fires, Event.mk.injEq, Kind.wait.injEq] at hf
      exact hf.choose_spec.1.2.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd
