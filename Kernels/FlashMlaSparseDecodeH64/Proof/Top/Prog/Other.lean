-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsync
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit

@[expose] public section

/-! # Progress class: bulk copies, asynchronous arrivals, cluster launch control

The decoded program issues no linear bulk copy (`noCopy`), no `cp.async.mbarrier.arrive`
(`noAsyncArrive`) and no cancellation request (`noClcIssue`), so none of the three obligations is
open in a consistent execution. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The bulk, arrive-on and CLC obligations are never open.** -/
theorem Prog.other : Prog.AsyncSteps P L m [.bulk, .arriveOn, .clc] := by
  intro _ X hmax _ o ho hob
  have hX := hmax.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact (hob fun i s hc => (noCopy hX hc).elim).elim
  · exact (hob fun i _ _ ha => (noAsyncArrive hX ha).elim).elim
  · exact (hob fun i s t hc => (noClcIssue hX hc).elim).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
