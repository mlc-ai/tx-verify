-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Remaining
public import Lemmas.Step.RegIssueAny

@[expose] public section

/-!
# `Remaining.regIssue`: a released pending thread at a register request steps

The kernel's threads make several `setmaxnreg` requests and no cluster barrier operation, so the
library's `Step.reg_issue_counted_extension` (a first request after a cluster barrier) does not
apply. `Step.reg_issue_extension_any` (`Lemmas/Step/RegIssueAny.lean`) issues a request for a
thread that has
started, whose last event is released, whatever the thread did before.

A pending thread at a state whose next event is a register request has started (the machines'
first events are a named barrier or an allocation, `ne_nil_of_kind`). Its run ends in a state; by
local steps it reaches a concrete state whose template is undefined behaviour (performed, `ub_ext`)
or the request (`fire`, `KindTmpl .reg`), which is issued.

`regIssue_of` is `Remaining.regIssue` for every time function. It takes the soundness of the
machines and the safety goal (to exclude undefined behaviour in a maximal execution), the same two
facts `Assembly.thread_steps` has (`Interface.threadFacts` for the first, `SafeGoal` for the
second).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at a register request steps**, in an execution without undefined
behaviour. -/
theorem reg_issue_steps (hX : Consistent L kernel asms mem0 X) (hub : ¬ HasUb X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g : Nat} (hp : Frame.Pending L X g)
    {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s)) (hk : nextKind s = .reg)
    (hrel : Step.Released L X g) : Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, m, hl, -, hout, hm⟩ := fire hS hp.1 hσ hrun
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨inc, n, u, rfl⟩
  · exact .inl (ub_ext hX hp.1 hrel hrun hl hout)
  · have hne : X.tr g ≠ [] := ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
    exact .inl (Step.reg_issue_extension_any (pc := t1.pc) (inc := inc) (n := n) (inst := 0) hX
      hp.1 hne hrel.ready hrun hl ⟨_, hout, 0, rfl, rfl⟩ (snoc_wf hX))

/-- **`Remaining.regIssue`**: a released pending thread of a maximal execution at a register
request steps. -/
theorem regIssue_of (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hs : SafeGoal kernel asms L mem0) : RegIssue T Q L mem0 :=
  fun X _ _ hmax hp hσ hk hrel =>
    reg_issue_steps hmax.1 (Sched.safe_noUb (hs.2 X hmax.1)) hS hp hσ hk hrel

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
