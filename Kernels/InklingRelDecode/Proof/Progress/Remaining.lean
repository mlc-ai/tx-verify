-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Alloc
public import Kernels.InklingRelDecode.Proof.Progress.Async

@[expose] public section

/-!
# What the progress layer takes from the layers below

`Remaining Q L mem0` is the one structure of what the thread and protocol layers have not proved
for the progress goal (like `Safety.Protocol` for the safety goal). Its first field is data, the
virtual time `time` of the abstract machine states (`Rank.lean`); every other field is a statement
about executions, in terms of the machines' abstract states and event shapes only: no program
counter and no register number occurs here.

* `wait_time` (the schedule): a state at an mbarrier poll is timed at least 2.
* `reads` (safety layer): the conflicts at read bytes are ordered, but for the same-value write
  pairs (`ReadsOrdered`, from the safety layer's ordered conflicts).
* `async` (protocols): tensor load sources (the KV ring), MMA operand sources, the layout.
* `polls` (protocols): the six mbarrier polls, the producers of the polled barrier (`Ring*`,
  `SO*`).
* `warpColl` (thread layer): the lanes of a warp agree on their warp collectives.
* `regWaits` (safety and thread layers): the `setmaxnreg` rendezvous of a warp
  (`Safety.Protocol.regAgree`, `regSync`).
* `tcWaits` (thread layer): the warp-collective `tcgen05` events.
* `regIssue`, `barSteps`, `tmemSteps` (library gaps): issuing a non-first `setmaxnreg` request,
  a named barrier whose thread count changes between generations, the `cta_group::1` allocator.

The three Lemmas gaps are classes of blocked or issuing threads for which the library has the
proof only for a different shape (a first request after a cluster barrier; a barrier with one
participant group and count; the `cta_group::2` pair protocol); each has a row in the development
notes,
"thread-layer gaps".
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

/-- **A released pending thread at a register request steps.** The library issues a register
request only for a thread's first request after a cluster-barrier operation
(`Step.reg_issue_counted_extension`); the kernel's threads make several requests (`inc 256`,
`dec 24`) without a cluster barrier. -/
def RegIssue (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g s, Maximal L kernel asms mem0 X → Frame.Pending L X g →
    St Q L X g (X.tr g).length = some (some s) → nextKind s = .reg → Step.Released L X g →
    Sched.Steps (timed T Q L) mem0 X (.thread g)

/-- **A blocked pending thread at a `bar.sync` whose generation is not done steps.** The library's
generation completion (`NamedBar.sync_release`) fixes one participant group and one thread count
per barrier (`NamedBar.Shape`, `Sources`); the kernel's named barrier 0 is used with the whole
CTA, then with the default partition's 128 threads, then with the whole CTA again. -/
def BarSteps (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g, Maximal L kernel asms mem0 X → Frame.Pending L X g → ¬ Step.Released L X g →
    Sched.BarWait L X g → Sched.Steps (timed T Q L) mem0 X (.thread g)

/-- **The Tensor Memory allocator of a single-CTA cluster makes progress**: a blocked pending thread
at an allocation, relinquishment or deallocation steps, and an open paired-request obligation of a
maximal execution steps. The library's pair protocol (`Tmem.Pair`, `PairProtocol`) is for
`cta_group::2` operations of two CTAs of a cluster; the kernel's are `cta_group::1`, made by warp 0
of each CTA alone. -/
def TmemSteps (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  (∀ X g, Maximal L kernel asms mem0 X → Frame.Pending L X g → ¬ Step.Released L X g →
    Sched.TmemOpen L X g → Sched.Steps (timed T Q L) mem0 X (.thread g)) ∧
  ∀ X, Maximal L kernel asms mem0 X → Descent.Obl L X .tmem → Sched.Steps (timed T Q L) mem0 X .tmem

/-- **What the progress goal takes from the thread and protocol layers.** -/
structure Remaining (Q : Params) (L : Launch) (mem0 : Mem0) where
  /-- The virtual time of an abstract machine state of a thread: a ranking by which every blocker
  of a wait is earlier than the wait (`Rank.lean`). -/
  time : Nat → TSt → Nat
  /-- A state whose next event is an mbarrier poll is timed at least 2, so that the asynchronous
  obligations (ranked below 2) rank below a thread at a poll. -/
  wait_time : ∀ g d, nextKind d = .wait → 2 ≤ time g d
  /-- The conflicting accesses at the bytes that are read are ordered, but for two writes of one
  value to the same bytes, as the role table and the `(num_pre, num_iters)` pair, which every
  default-partition thread writes (`ReadsOrdered`). -/
  reads : ∀ X, Consistent L kernel asms mem0 X → ReadsOrdered L X
  /-- The sources of the asynchronous operations (`AsyncSources`). -/
  async : AsyncSources L mem0
  /-- Every released pending thread at an mbarrier poll of a maximal execution polls an object with
  a blocker when the object is not ready: the six polls' wait classes (`PollsBlocked`). -/
  polls : PollsBlocked time Q L mem0
  /-- The lanes of a warp agree on their warp collectives (`WarpCollFacts`), in a maximal
  execution. -/
  warpColl : ∀ X, Maximal L kernel asms mem0 X → WarpCollFacts time Q L X
  /-- The register requests of a warp rendezvous (`RegWaitFacts`). -/
  regWaits : ∀ X, Consistent L kernel asms mem0 X → RegWaitFacts time Q L X
  /-- The warp-collective `tcgen05` events (`Sched.TcWaitFacts`). -/
  tcWaits : ∀ X, Consistent L kernel asms mem0 X → Sched.TcWaitFacts (timed time Q L) X
  /-- A released pending thread at a register request steps (`RegIssue`). -/
  regIssue : RegIssue time Q L mem0
  /-- A blocked `bar.sync` steps (`BarSteps`). -/
  barSteps : BarSteps time Q L mem0
  /-- The Tensor Memory allocator makes progress (`TmemSteps`). -/
  tmemSteps : TmemSteps time Q L mem0
  /-- The next read of a followed thread at a site of the read-only input assumption reads bytes
  that no write covers (`Interface.ReadFresh`). -/
  fresh : ∀ X, Consistent L kernel asms mem0 X → ReadFresh Q L X

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
