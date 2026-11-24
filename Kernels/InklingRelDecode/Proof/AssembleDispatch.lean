-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleBase
public import Kernels.InklingRelDecode.Proof.Bound.Goal
public import Kernels.InklingRelDecode.Proof.Interface.DispatchCount

@[expose] public section

/-!
# `Bound.DispatchBound` from the role byte protocol

`Bound.DispatchBound L mem0 R` says that a worker thread of a consistent execution has at most `R`
events at the position of the load of its role byte (`Worker.Site.ldRole`). It follows from the
facts `Assemble.Base` already holds for every consistent execution:

* `RoleReads` (`Base.roleReads`: the first load returns a role below 3, a later one the exit) and
  the counts along a worker thread (`Interface.phase_inv`), which make the dispatch loop's rounds
  at most two (`Interface.ldN_inv`);
* the machine follows the thread (`ThreadFacts.tracked`), so the only events that are not fired
  from a followed state are the undefined-behaviour event after a stop, at most one
  (`Interface.trace_length_le`).

So the loads are at most two from followed states and one more after a stop: `R = 3`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A worker thread of a consistent execution has at most three events at the position of the
load of its role byte.** -/
theorem Base.dispatch (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (b : Base Q L mem0 X) :
    ∀ g < L.threads, 128 ≤ g % L.block →
      (X.tr g).countP (fun e => decide (e.pc = Worker.Site.ldRole.pc)) ≤ 3 :=
  fun _ hg hw => by
    have := dispatch_count hpre hX b.facts.sound b.facts.tracked (Base.roleReads hpre hX) hg hw
    simpa only [ldN, List.take_length] using this

/-- **`Bound.DispatchBound`**, from `Base` of every consistent execution. -/
theorem dispatchBound_of (hpre : Pre Q L mem0)
    (hbase : ∀ X, Consistent L kernel asms mem0 X → Base Q L mem0 X) :
    Bound.DispatchBound L mem0 3 :=
  fun _ hX => Base.dispatch hpre hX (hbase _ hX)

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
