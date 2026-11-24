-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorExecution
public import Core.Async.BulkExecution
public import Core.Clc.ClcExecution
public import Core.Sync.Barrier
public import Core.Sync.WarpBarrier
public import Core.Memory.Acquire
public import Core.Tmem.CtaPair
public import Core.Tmem.AllocResult

@[expose] public section

/-!
# Order and visibility composition

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## MEM-PROGRAM-ORDER — program order
Statement: The events of one thread are ordered as they appear in its trace, except that the scalar
  element operations of one vector access are unordered among themselves.

Defs: TraceBefore, Event.acc, Acc.shift, SameAccess, po

Source:
- §8.9.1 (program order)
- §8.2.4: "Memory operations with a vector data type are modeled as a set of equivalent memory
    operations with a scalar data type, executed in an unspecified order on the elements in the
    vector."
- EXT-VECTOR-ELEM

Direction: reading

Applies: Events in a single thread trace

Premises: The source index is smaller than the target index, the target exists, and the two events
  are not elements of one vector access.

Effect: Order construction. MEM-BASE-CAUSALITY states which program-order edges enter
  `baseCausality`. The trace lists the elements of an access in element order, each at the next
  element number and the next address (EXT-VECTOR-ELEM): the events from `e` to `f` are elements of
  one access when each is `e`'s footprint shifted by its distance from `e`. The access as a whole is
  ordered with every other event.
-/

/-- `e` is before `f` in the trace of one thread. -/
def TraceBefore (X : Execution) (e f : EvId) : Prop :=
  e.1 = f.1 ∧ e.2 < f.2 ∧ f.2 < (X.tr f.1).length

/-- The footprint of a memory operation event. -/
def Event.acc : Event → Option Acc
  | ⟨_, .rd a _⟩ | ⟨_, .nc a _⟩ | ⟨_, .wr a _⟩ | ⟨_, .rmw a _ _⟩ => some a
  | _ => none

/-- The footprint of the element `k` places after the element with footprint `a`. -/
def Acc.shift (k : Nat) (a : Acc) : Acc := { a with loc := a.loc.at (k * a.size), elem := a.elem +
    k }

/-- The events from `e` to `f` are consecutive elements of one vector access. -/
def SameAccess (X : Execution) (e f : EvId) : Prop :=
  ((X.get f).bind Event.acc).isSome ∧
    ∀ k, k ≤ f.2 - e.2 → (X.get (e.1, e.2 + k)).bind Event.acc =
      ((X.get e).bind Event.acc).map (Acc.shift k)

instance (X : Execution) (e f : EvId) : Decidable (SameAccess X e f) := by
  unfold SameAccess; infer_instance

/-- Program order (§8.9.1): `e` comes before `f` in the trace of one thread, and the two events
are not elements of one vector access. -/
def po (X : Execution) (e f : EvId) : Prop :=
  e.1 = f.1 ∧ e.2 < f.2 ∧ f.2 < (X.tr f.1).length ∧ ¬ SameAccess X e f

/-! ## MEM-BASE-CAUSALITY — base causality order
Statement: `baseCausality` is the base causality order of §8.9.5 for the thread instructions of one
  launch: the transitive closure of program order and synchronizes-with between thread instructions.
  Its synchronizes-with edges come from CTA barriers, mbarriers, cluster barriers, warp barriers,
  release and acquire patterns and the Fence-SC order.

Defs: baseCausality

Source:
- §8.9.5: "An operation X precedes an operation Y in base causality order if: X precedes Y in
    program order , or X synchronizes with Y, or For some operation Z, X precedes Z in program order
    and Z precedes Y in base causality order , or X precedes Z in base causality order and Z
    precedes Y in program order , or X precedes Z in base causality order and Z precedes Y in base
    causality order ."
- §8.9.4 (memory synchronization: bar.sync and bar.arrive to bar.sync, release/acquire)
- §8.8 (release and acquire patterns)
- §8.9.3 (Fence-SC order)
- §9.7.15.2 (bar.warp.sync memory ordering)
- §9.7.15.16.19 (mbarrier acquire)
- §9.7.15.3 (cluster barrier)

Direction: stricter

Applies: Thread instruction events; independent asynchronous effects are not ordered

Premises: Each edge is program order, CTA/cluster/warp barrier synchronization, phase-matched
  mbarrier synchronization, release/acquire read-from synchronization with or without fences
  (MEM-RELEASE-ACQUIRE), or Fence-SC synchronization (MEM-FENCE-SC).

Effect: Generic-proxy ordering between thread events. The effects of asynchronous operations are
  ordered through the observation of their completion (MEM-OBSERVED-COMPLETION,
  MEM-MODEL-CAUSALITY).

Review: The order departs from §8.9.4 in two ways. First, the model covers the thread
  instructions of one launch and leaves out the synchronizes-with edges of CUDA APIs (§8.9.4: "A
  synchronizes relation can also be established by certain CUDA APIs."); this launch scope only
  adds rejections, and the direction `stricter` records its effect. Second, the edge `WarpBarSync`
  is a reading of §9.7.15.2, which states memory ordering for `bar.warp.sync` ("bar.warp.sync also
  guarantee memory ordering among threads participating in barrier.") and has no synchronizes-with
  sentence in §8.9.4. The edge removes executions: every constraint that uses `baseCausality`
  (`NoFuture`, `Hidden`, the object orders, `DependencyOk.acyclic`) forbids more with more edges,
  and the race check, the one rule that it weakens, only stops rejecting executions. An edge that
  the hardware does not provide can thus remove a hardware execution and accept a program that
  misbehaves; `WarpBarSync` is also a full synchronizes-with edge, so it orders the accesses of the
  two lanes at unrelated addresses as well. The reading is the claim to review.
-/

/-- The base causality order between thread instruction events (§8.9.5): the transitive closure
of program order and the synchronizes-with edges of CTA barriers (`CtaBarSync`), mbarriers
(`MSync`), cluster barriers (`ClusterSync`), warp barriers (`WarpBarSync`), release/acquire
accesses (`synchronizesWith`), and release and acquire patterns with fences and the Fence-SC order
(`FenceSync`). -/
def baseCausality (X : Execution) : EvId → EvId → Prop :=
  Relation.TransGen fun e f => po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨ ClusterSync L X e f ∨
    WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f

/-! ## MEM-OBSERVED-COMPLETION — observation of a particular operation's completion
Statement: An acquire wait that observes the completion notification of a copy, a tensor load, a CLC
  response or an MMA, with scopes that include each other's thread, orders the memory accesses of
  that operation before the accesses that follow the wait, except that the shared-memory reads of
  `tcgen05.mma` and `tcgen05.cp` use a `fence.proxy.async` between the wait and a later generic
  access (MEM-MODEL-CAUSALITY), with a completed source overwrite also ordered under
  EXT-TC-SOURCE-REUSE. A bulk-group wait does the same for the tensor stores and linear copies
  of the groups it covers, and a `.read` bulk-group wait orders their source reads before later
  generic accesses without a proxy fence (EXT-READ-WAIT-ORDER). A
  `cp.async` wait does the same for the `cp.async` operations of the groups it covers, and an
  acquire wait that observes the arrive-on of a `cp.async.mbarrier.arrive` for the `cp.async`
  operations it tracks.

Defs: AsyncFinished, asyncFinished_copy_of_mbarrier

Source:
- §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all
    asynchronous operations tracked by this phase are complete, and all threads participating in
    that mbarrier object can access the result of the asynchronous operations."
- §9.7.10.28.1.2: "Once the mbarrier.test_wait or mbarrier.try_wait operation returns True , access
    the results of the asynchronous operations tracked by the mbarrier object ."
- §9.7.10.28.2: "The completion of a cp{.reduce}.async.bulk operation is followed by an implicit
    generic-async proxy fence. So the result of the asynchronous operation is made visible to the
    generic proxy as soon as its completion is observed."
- §9.7.18.6.2.1.1 (tcgen05.mma completion is observed through the mbarrier based waiting mechanism)
- §9.7.18.6.5: "The shared memory accesses by tcgen05.mma and tcgen05.cp operations are performed
    asynchronously and via the asynchronous proxy (async proxy). These shared memory accesses are
    not subject to the pipelining rules above. Accessing the same memory location across multiple
    proxies needs a cross-proxy fence. For the async proxy, fence.proxy.async should be used to
    synchronize memory between generic proxy and the async proxy."
- §9.7.10.28.6.2 (bulk-group wait)
- §9.7.10.28.3.3: "Writes performed by cp.async operations are made visible to the executing thread
    only after: The completion of cp.async.wait_all or The completion of cp.async.wait_group on the
    cp.async-group in which the cp.async belongs to or mbarrier.test_wait and mbarrier.try_wait
    returns True on an mbarrier object which is tracking the completion of the cp.async operation."
- §9.7.10.28.3.3: "cp.async.wait_group and cp.async.wait_all does not provide any ordering and
    visibility guarantees for any other memory operation apart from cp.async ."
- §9.7.18.12.1 (commit tracks prior tcgen05 operations): "The scope of the arrive-on operation is
    the cluster scope."
- §9.7.15.18 (clusterlaunchcontrol.try_cancel): "The completion of the asynchronous operation is
    tracked using the mbarrier completion mechanism at .cluster scope."
- §8.7 (morally strong)
- OBJ-MBAR-OBSERVE
- EXT-READ-WAIT-ORDER
- EXT-TC-SOURCE-REUSE

Direction: reading

Applies: The actual notification of a copy, tensor load (its `.notify .load`), CLC response or MMA
  (the arrive-on of a commit that tracks it), and the arrive-on of a `cp.async.mbarrier.arrive`, in
  its object's exact generation and phase (`AsyncCopy.Notifies`); the bulk group of a tensor store
  or linear copy; the `cp.async`-group of a `cp.async`

Premises: An acquire wait observes that notification (`AsyncCopy.AsyncObserved`) and its scope and
  the notification's `.cluster` scope each include the other's thread (`ScopesMeet`, as for
  `CopyReleaseSync`); or a group wait whose mode makes the part visible (`GroupWaitVisible`) covers
  the operation's group (`GroupWaitsFor`) and the stages it waits for are present: a full or `.read`
  bulk-group wait for a tensor store or a linear copy, a `cp.async.wait_group` or
  `cp.async.wait_all` for a `cp.async`.

Effect: Completion and visibility (MEM-MODEL-CAUSALITY). The quoted text does not require an acquire
  wait; the rule requires one, and requires the scopes to meet (stricter). The `.read` wait is the
  reading EXT-READ-WAIT-ORDER. The observing thread may belong to another CTA of the issuer's
  cluster when its wait has cluster scope. A `cp.async` group wait makes the writes visible to the
  waiting thread; the order then reaches other threads only through `baseCausality` from the wait,
  as for a full bulk-group wait, and it orders no other memory operation of the thread.

Review: The proxy-fence path for the `tcgen05` reads follows §9.7.18.6.5. The implicit generic-async
  proxy fence of §9.7.10.28.2 is stated for `cp{.reduce}.async.bulk` only.

### EXT-READ-WAIT-ORDER — a `.read` bulk-group wait orders the source reads before generic accesses

Statement: Once a `cp.async.bulk.wait_group.read` that covers the bulk group of a tensor store
  returns, the store's asynchronous-proxy source reads are ordered before the generic accesses that
  the waiting thread's return precedes in causality (`AsyncFinished`, the `.read (.store ..)` case),
  with no `fence.proxy.async` between them.

Source:
- §9.7.10.28.2: "Accessing the same memory location across multiple proxies needs a cross-proxy
    fence. For the async proxy , fence.proxy.async should be used to synchronize memory between
    generic proxy and the async proxy ."
- §9.7.10.28.2: "The completion of a cp{.reduce}.async.bulk operation is followed by an implicit
    generic-async proxy fence."
- §9.7.10.28.6.2: "The optional .read modifier indicates that the waiting has to be done until all
    the bulk async operations in the specified bulk async-group have completed: reading from the
    tensormap the reading from their source locations."

Why it is not spec text: The implicit generic-async proxy fence follows the completion of the
  operation, and a `.read` wait waits only until the source reads are done; it does not wait until
  the operation is complete. Without a proxy fence the async-proxy reads and a later generic store
  to the same bytes are not ordered by §8.9.5 (proxy-preserved base causality).

Direction: reading

Effect: A generic store that reuses the source buffer is not a race with those reads, and the reads
  do not see it. The rule is wider than the text: it relies on hardware completing the source reads
  in a way that a later generic access of the waiting thread's causal successors cannot overtake.
  CUTLASS epilogues rely on it: they wait with `cp.async.bulk.wait_group.read` (`tma_store_wait`)
  and then reuse the shared-memory buffer without a proxy fence. If it does not hold, such a reuse
  is a data race and the store may write the reused buffer's new contents to global memory, which
  the model does not report. Disclosed by every kernel whose statement names
  `Op.bulkWait (mode := BulkGroup.WaitMode.read)`: FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192.
-/

/-- The wait `w` observes the completion of part `p` of the asynchronous operation issued by `i`:
a group wait covering `i` whose kind makes `p` visible (`GroupWaitVisible`, the table of
DEP-BULK-WAIT), once every stage the wait waits for is present (`GroupWaitStages`), or an
acquire wait that observes the operation's own completion notification (for an MMA, the arrive-on
of a commit tracking it; for a `cp.async`, the arrive-on of a `cp.async.mbarrier.arrive` that
tracks it), the wait's scope and the notification's `.cluster` scope each including the other's
thread. -/
def AsyncFinished (X : Execution) (i : EvId) (p : AsyncCopy.Part) (w : EvId) : Prop :=
  (∃ k, GroupWaitVisible k p = true ∧ GroupWaitsFor X k i w ∧
    ∀ q ∈ GroupWaitStages X i k, X.AsyncPresent i q) ∨
  ∃ ws, AsyncCopy.AsyncObserved X i p w true ws ∧ ScopesMeet L .cluster i.1 ws w.1

/-- For a linear copy completed through an mbarrier (every `cp.async.bulk` copy of the earlier
representation), the observation of its read or write is, as before, an acquire wait that observes
its notification with meeting scopes. -/
theorem asyncFinished_copy_of_mbarrier {X : Execution} {i w : EvId} {s : AsyncCopy.Spec}
    {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m) {p : AsyncCopy.Part} :
    AsyncFinished L X i p w ↔
      ∃ ws, AsyncCopy.AsyncObserved X i p w true ws ∧ ScopesMeet L .cluster i.1 ws w.1 := by
  have hk : ∀ k, ¬ GroupWaitsFor X k i w := by
    intro k
    cases k with
    | bulk mode => exact not_bulkWaitsFor_of_copy hc (by simp [hm])
    | cpAsync => exact not_asyncGroupWaitsFor_of_copy hc (by simp [hm])
  simp only [AsyncFinished]
  constructor
  · rintro (⟨k, -, hw, -⟩ | h)
    · exact absurd hw (hk k)
    · exact h
  · exact Or.inr

/-! ## MEM-MODEL-CAUSALITY — base proxy and completion order at one byte
Statement: `modelCausality` is applied at a byte that both accesses touch; between two thread
  accesses it is `baseCausality` (§8.9.5) or allocation-result order at that byte
  (EXT-TMEM-ALLOC-RESULT-ORDER). From a thread access to the
  access of a `cp.async`, `st.async` or `red.async`, which are performed in the generic proxy, it is
  also `baseCausality` to the issue. Its proxy-fence case (`ProxyBefore`), which orders a thread
  access before the async-proxy access of an asynchronous operation through a `fence.proxy.async`,
  is the text of §9.7.15.4. Its observed-completion and async-chain cases, which order the accesses
  of asynchronous operations, are model readings of the manual text quoted for each.
  `ByteCausality` adds the observed MMA operand handoff to these paths
  (EXT-TC-COMMIT-OPERAND-ORDER).

Defs: AsyncCovers, AsyncFenceCovers, ProxyFenceReach, ProxyBefore, proxyBefore_iff_of_cta,
  AsyncOnlyFinished, AsyncBefore, AsyncChain, PairAsync, PairTc, CompletionBefore, GenericCopy,
  not_genericCopy_of_mbarrier, modelCausality, modelCausality.of_base,
  modelCausality.of_allocResultBefore, modelCausality_thread_async_of_not_generic,
  TcReadReuseBefore, TcReadReuseBefore.base, TcReadReuseBefore.congr, ObservedCompletionBefore

Source:
- §8.9.5 (thread-thread case): "An operation X precedes an operation Y in base causality order if:
    X precedes Y in program order , or X synchronizes with Y"
- EXT-TMEM-ALLOC-RESULT-ORDER (allocation-result readback)
- §8.9.5 (proxy-fence and async-chain cases): "A memory operation X precedes a memory operation Y
    in proxy-preserved base causality order if X precedes Y in base causality order , and: X and Y
    are performed to the same address, using the generic proxy , or X and Y are performed to the
    same address, using the same proxy , and by the same thread block, or X and Y are aliases and
    there is an alias proxy fence along the base causality path from X to Y."
- §9.7.15.4 (proxy-fence case): "membar.proxy and fence.proxy instructions establish an ordering
    between memory accesses that may happen through different proxies ."
- §9.7.15.4 (proxy-fence case): "A uni-directional proxy ordering from the from-proxykind to the
    to-proxykind establishes ordering between a prior memory access performed via the
    from-proxykind and a subsequent memory access performed via the to-proxykind ."
- §9.7.15.4 (proxy-fence case): "Value .async of the .proxykind qualifier specifies that the memory
    ordering is established between the async proxy and the generic proxy."
- §9.7.15.4 (proxy-fence case): "The memory ordering is limited only to operations performed on
    objects in the state space specified."
- §9.7.15.4 (proxy-fence case): "If no state space is specified, then the memory ordering applies
    on all state spaces."
- §9.7.15.4 (proxy-fence case, reach of a fence with a scope): "The scope qualifier specifies the
    set of threads that may observe the ordering effect of this operation."
- §9.7.15.4 (proxy-fence case, reach of a fence without a scope): "Their cross-proxy synchronizing
    effect composes with other forms of synchronization according to the rules of the Memory
    Consistency Model ."
- §9.7.10.28.2 (proxy-fence case, async-proxy operations): "The cp{.reduce}.async.bulk operations
    are performed in the asynchronous proxy (or async proxy )."
- §9.7.10.28.3.1 (thread-to-async case, generic-proxy operations, ordered without a fence):
    "cp.async is treated as a weak memory operation performed in the generic proxy in the Memory
    Consistency Model ."
- §9.7.10.12 (thread-to-async case, generic-proxy operations, ordered without a fence): "st.async
    is performed in the generic proxy."
- §9.7.15.7 (thread-to-async case, generic-proxy operations, ordered without a fence): "red.async
    is performed in the generic proxy."
- §8.9.1.1 (thread-to-async case, async-proxy operations: ordered after prior instructions of the
    same thread; the model still requires a proxy fence): "These asynchronous operations are
    ordered after prior instructions in the same thread"
- §9.7.10.28.1.1 (observed-completion case: a wait observes completion): "When an async-group
    completes, all the asynchronous operations belonging to that group are complete and the
    executing thread that initiated the asynchronous operations can read the result of the
    asynchronous operations."
- §9.7.10.28.1.2 (observed-completion case: a wait observes completion): "When the current phase
    of the mbarrier object is complete, it implies that all asynchronous operations tracked by this
    phase are complete, and all threads participating in that mbarrier object can access the result
    of the asynchronous operations."
- §9.7.10.28.6.2 (observed-completion case: bulk-group wait modes)
- §9.7.18.6.5 (observed-completion case: proxy fence for the tcgen05 shared-memory reads)
- EXT-TCACQUIRE
- EXT-TC-SOURCE-REUSE (reusing a completed Tensor Core source)
- EXT-PAIR-ASYNC

Direction: reading

Applies: Ordinary accesses and the independent accesses of copies/MMAs

Premises: Async-to-async order holds between two operations issued by threads of the same CTA ("by
  the same thread block"), or, under EXT-PAIR-ASYNC, by the two CTAs of one `cta_group::2` pair at a
  shared byte of that pair when one of the two operations is a `cta_group::2` `tcgen05.mma` or
  `tcgen05.cp` (`PairTc`), joined by a chain of observed-completion edges; generic-to-async order
  has an explicit async proxy fence whose state space covers the byte (`AsyncFenceCovers`; for
  `.shared::cta` the byte is in the fence's CTA), ordered by baseCausality before the issue, whose
  thread the fence reaches (`ProxyFenceReach`): a thread of the fence's cluster, possibly in a peer
  CTA, and for a fence with a scope a thread that the scope includes, or, for a `cp.async`,
  `st.async` or `red.async` (generic proxy, `GenericCopy`), baseCausality to its issue;
  async-to-later order has an observation of that operation's completion, followed for the
  shared-memory reads of `tcgen05.mma` and `tcgen05.cp` by an async proxy fence covering the byte
  (`CompletionBefore`, §9.7.18.6.5) or a completed source overwrite
  (EXT-TC-SOURCE-REUSE). Scope and accessed byte match.

Effect: Read-source/coherence and conflicting-access checks. The fence composes with ordinary
  synchronization before/after it; it need not be executed by the eventual async issuer. Chains are
  built only from the typed edges above (`AsyncChain`). Direct asynchronous edges compose through an
  actual asynchronous memory effect at the same byte. The composed order relates the two endpoint
  operations only when their issuing threads are in one CTA, or in one `cta_group::2` pair at a byte
  of that pair when one of the two is a `cta_group::2` `tcgen05` operation (EXT-PAIR-ASYNC), and the
  interior operations of the chain may belong to any CTA. Each edge relates the accesses of one
  operation, or of the next operation in the chain, at the one byte.

### EXT-PAIR-ASYNC — a cta_group::2 pair is one thread block for asynchronous accesses

Statement: Asynchronous-proxy accesses to the shared memory of either CTA of a `cta_group::2` pair,
  issued by either CTA of the pair, count as performed by the same thread block when one of the two
  operations is a `cta_group::2` `tcgen05.mma` or `tcgen05.cp`; a chain of observed completions then
  orders them as it orders the asynchronous accesses of one CTA.

Source:
- §8.9.5: "A memory operation X precedes a memory operation Y in proxy-preserved base causality
    order if X precedes Y in base causality order , and: X and Y are performed to the same address,
    using the generic proxy , or X and Y are performed to the same address, using the same proxy ,
    and by the same thread block, or X and Y are aliases and there is an alias proxy fence along the
    base causality path from X to Y."
- §9.7.18.10.10.1: "The qualifier .cta_group::2 specifies that the matrix multiply and accumulate
    operation is performed on the Tensor Memory of the executing thread’s CTA and its peer CTA ."
- §9.7.10.28.5.3: "When .cta_group::2 is specified, the mbarrier object mbar can be in shared memory
    of either the same CTA as the shared memory destination dstMem or in its peer-CTA ."

Why it is not spec text: The ISA text does not extend "by the same thread block" to the two CTAs of
  a pair. The model reads it so: for a CTA pair formed by `cta_group::2` (`SameCtaGroup L .two`),
  asynchronous-proxy accesses to the shared memory of either CTA of the pair, issued by either CTA
  of the pair, count as performed by the same thread block in §8.9.5 (`PairAsync`) when one of the
  two operations is a `cta_group::2` `tcgen05.mma` or `tcgen05.cp` (`PairTc`). A `cta_group::2`
  operation is meaningful only under this reading: the peer CTA's load, observed through an mbarrier
  of the leader's CTA, is read by the leader's MMA, and the MMA's completion, committed to the
  peer's barrier, frees the peer's load. CUTLASS and DeepGEMM 2-CTA kernels rely on it. Each of
  these orders relates a `cta_group::2` MMA to a copy. For two operations neither of which is a
  `cta_group::2` `tcgen05` operation the text and this evidence say nothing: two copies of two CTAs
  of a pair (a `cp.async.bulk` into the peer CTA's shared memory and a later bulk read of it by the
  peer) stay unordered, as for any two CTAs, even when a `cta_group::2` MMA lies between them on
  the chain.

Direction: reading

Effect: The rule is wider than the text for the cross-CTA endpoints of a pair. If it does not hold,
  an asynchronous access by one CTA of a pair and a conflicting asynchronous access by the other (a
  peer CTA's tensor load and the leader's MMA operand read, an MMA's read and the next load into the
  same buffer) are unordered on hardware: such programs race, which the model does not report.
  Disclosed by every kernel whose statement names `CtaGroup.two`: FlashAttn4Fwd, Fp16Gemm8192.
-/

/-- `i` issues a linear operation performed in the generic proxy: a `cp.async`
(§9.7.10.28.3.1), an `st.async` (§9.7.10.12) or a `red.async` (§9.7.15.7). -/
def GenericCopy (X : Execution) (i : EvId) : Prop :=
  ∃ s, X.Copy i s ∧ s.generic = true

/-- A linear operation that is not performed in the generic proxy (every `cp.async.bulk` copy)
uses the async proxy. -/
theorem not_genericCopy_of_mbarrier {X : Execution} {i : EvId} {s : AsyncCopy.Spec}
    (hc : X.Copy i s) (hg : s.generic = false) : ¬ GenericCopy X i := by
  rintro ⟨s', hc', hs'⟩
  cases Execution.Copy.unique hc hc'
  rw [hg] at hs'
  cases hs'

/-- Part `p` of the asynchronous operation issued by `i` accesses byte `l`, pending or
performed. -/
def AsyncCovers (X : Execution) (i : EvId) (p : AsyncCopy.Part) (l : Loc) : Prop :=
  ∃ a w, X.Intent (.async i p) a w ∧ a.Covers l

/-- The bytes an async proxy fence of thread `g` orders (§9.7.15.4): all state spaces without a
state space, the global bytes for `.global`, the shared bytes of `g`'s CTA for `.shared::cta` and
the shared bytes of a CTA of `g`'s cluster for `.shared::cluster`. -/
def AsyncFenceCovers : Option StateSpace → Nat → Loc → Prop
  | none, _, _ => True
  | some .global, _, l => l.space = .global
  | some (.shared .cta), g, l => l.space = .shared ∧ l.cta = g / L.block
  | some (.shared .cluster), g, l => l.space = .shared ∧ SameCluster L g (l.cta * L.block)
  | some _, _, _ => False

/-- The threads `h` that an async proxy fence of thread `g` with scope `scope` reaches: the
threads of `g`'s cluster, and for a fence with a scope only those its scope includes (§9.7.15.4,
`MbarScopeIncludes`). -/
def ProxyFenceReach : Option MbarScope → Nat → Nat → Prop
  | none, g, h => SameCluster L g h
  | some s, g, h => SameCluster L g h ∧ MbarScopeIncludes L s g h

/-- A `fence.proxy.async` whose state space covers byte `l` is ordered after `e` and before the
issue of an asynchronous operation by `baseCausality`, and the issuer is a thread the fence reaches
(`ProxyFenceReach`). ISA §9.7.15.4 permits the proxy fence effect to compose with other forms of
synchronization; the fence and the async issue may occur in different threads. For a fence without
a scope the issuer may be another CTA of the fence's cluster (a multicast or peer write into this
CTA): the fence then reaches it only through `baseCausality`, i.e. through synchronization whose
scope includes both CTAs. -/
def ProxyBefore (X : Execution) (e issuer : EvId) (l : Loc) : Prop :=
  ∃ fence sp scope, X.IsProxyFence fence (.async sp) scope ∧ fence.1 < L.threads ∧
    AsyncFenceCovers L sp fence.1 l ∧ ProxyFenceReach L scope fence.1 issuer.1 ∧
    baseCausality L X e fence ∧ baseCausality L X fence issuer

/-- With only `fence.proxy.async.shared::cta` fences without a scope in the execution,
`ProxyBefore` orders a shared byte of the fence's CTA for an issuer of the fence's cluster. -/
theorem proxyBefore_iff_of_cta {X : Execution} {e issuer : EvId} {l : Loc}
    (h : ∀ f sp scope, X.IsProxyFence f (.async sp) scope →
      sp = some (.shared .cta) ∧ scope = none) :
    ProxyBefore L X e issuer l ↔ l.space = .shared ∧ ∃ fence,
      X.IsProxyFence fence (.async (some (.shared .cta))) none ∧ fence.1 < L.threads ∧
      l.cta = fence.1 / L.block ∧ SameCluster L fence.1 issuer.1 ∧ baseCausality L X e fence ∧
      baseCausality L X fence issuer := by
  constructor
  · rintro ⟨fence, sp, scope, hf, hlt, hc, hs, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := h _ _ _ hf
    exact ⟨hc.1, fence, hf, hlt, hc.2, hs, h1, h2⟩
  · rintro ⟨hsp, fence, hf, hlt, hc, hs, h1, h2⟩
    exact ⟨fence, _, _, hf, hlt, ⟨hsp, hc⟩, hs, h1, h2⟩

/-- Async-only group waits do not publish to generic accesses. Their direct ordering
is used only for a subsequent async instruction of the same thread: an `.asyncProxy` bulk wait
covering `i`, once the stages it waits for are present, for every memory part of `i` that a full
wait would make visible. -/
def AsyncOnlyFinished (X : Execution) (i : EvId) (p : AsyncCopy.Part) (w : EvId) : Prop :=
  GroupWaitVisible (.bulk .full) p = true ∧ GroupWaitsFor X (.bulk .asyncProxy) i w ∧
    ∀ q ∈ GroupWaitStages X i (.bulk .asyncProxy), X.AsyncPresent i q

/-- Direct byte-specific asynchronous order. Each edge keeps the operation
identities, completion mode, observer scope and wait-to-issue order. -/
def AsyncBefore (X : Execution) (l : Loc)
    (a b : EvId × AsyncCopy.Part) : Prop :=
  AsyncCovers X a.1 a.2 l ∧ AsyncCovers X b.1 b.2 l ∧
    ((∃ w, AsyncFinished L X a.1 a.2 w ∧ baseCausality L X w b.1) ∨
     ∃ w, AsyncOnlyFinished X a.1 a.2 w ∧ po X w b.1)

/-- Only actual asynchronous memory effects can be interior vertices. The
fixed byte and typed vertices exclude chaining through unrelated addresses,
ordinary issuing instructions, or completion notifications. Endpoints retain
their issue footprints so pending conflicting accesses are still checked. -/
inductive AsyncChain (X : Execution) (l : Loc) :
    (EvId × AsyncCopy.Part) → (EvId × AsyncCopy.Part) → Prop
  | direct {a b} : AsyncBefore L X l a b → AsyncChain X l a b
  | tail {a b c} : AsyncChain X l a b → X.AsyncPresent b.1 b.2 →
      AsyncBefore L X l b c → AsyncChain X l a c

/-- Two threads issue asynchronous accesses to shared byte `l` of one `cta_group::2` pair:
both issuing CTAs and the byte's CTA belong to the pair (EXT-PAIR-ASYNC). -/
def PairAsync (l : Loc) (a b : Nat) : Prop :=
  l.space = .shared ∧ SameCtaGroup L .two (a / L.block) (b / L.block) ∧
    SameCtaGroup L .two (a / L.block) l.cta

/-- `i` issues a `tcgen05` operation with `.cta_group::2` that reads shared memory: a
`tcgen05.mma` or a `tcgen05.cp` of the pair (EXT-PAIR-ASYNC). -/
def PairTc (X : Execution) (i : EvId) : Prop :=
  (∃ d s acc mask, X.MmaIssue i d s acc mask ∧ s.descriptor.group = .two) ∨
    ∃ c, X.CpIssue i c ∧ c.ctas.length = 2

/-- From the observation `w` of part `p`'s completion to the generic access `f`: causality,
and for the shared-memory reads of `tcgen05.mma` and `tcgen05.cp` (asynchronous proxy,
§9.7.18.6.5) a `fence.proxy.async` between them (`ProxyBefore`). -/
def CompletionBefore (X : Execution) (l : Loc) : AsyncCopy.Part → EvId → EvId → Prop
  | .mmaRead .., w, f => ProxyBefore L X w f l
  | _, w, f => baseCausality L X w f

/-!
### EXT-TC-SOURCE-REUSE — overwriting a shared source after observed Tensor Core completion
Statement: Observed completion of a shared-byte read by a Tensor Memory copy or an MMA ends
  its use of that byte before a covering generic store. For an MMA, the store must follow the
  acquire in the same thread. The copy's operand handoff also carries an earlier write that
  precedes the copy read to the covering store.

Source:
- PTX ISA 9.5 §9.7.18.6.2.1.1 (mbarrier-based completion of `tcgen05.cp` and `tcgen05.mma`)
- PTX ISA 9.5 §9.7.18.12.1: "Upon the completion of the tracked asynchronous tcgen05 operations,
  the signal specified by the .completion_mechanism is triggered by the system
  on the mbarrier object."
- PTX ISA 9.5 §9.7.18.6.5: "Accessing the same memory location across multiple proxies needs a
  cross-proxy fence."

Why it is not spec text: The commit mechanism fixes when the tracked source read finishes. The
  shared-memory rule requires a fence across proxies and does not make an exception for
  recycling a source whose read has already finished. The reading treats the observed end of
  the read as enough to avoid overlap with a later plain overwrite of that byte. Generic
  writes supplying the read still require their original proxy order into the operation.

Direction: reading

Applies: A `tcgen05.cp` or `tcgen05.mma` shared operand byte and an ordinary store covering
  that byte.

Premises: A real source footprint covers the byte and an in-scope acquire observes that
  operation's completion (`AsyncFinished`). The acquire precedes the store in base causality.
  For MMA it also precedes the store in the same thread's trace. Carrying an earlier write into
  the copy-source overwrite requires a recorded copy byte read, byte order into that read, and
  a store after the acquire in the same thread (`CommitOperandIssue`).

Effect: Orders the source read before the overwrite at that byte. No fence is inferred for
  another address or for accesses that consume an asynchronously written value.
  Disclosed by every kernel whose statement names `Op.tcCp` and `Op.tcCommit` or `Op.tcMma` and
  `Op.tcCommit`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.
-/

/-- The post-wait path for a completed Tensor Core operand read and a covering plain store.
`modelCausality` also requires the source footprint and an observation of completion. -/
def TcReadReuseBefore (X : Execution) (l : Loc) (i : EvId) :
    AsyncCopy.Part → EvId → EvId → Prop
  | .mmaRead isB _, w, f =>
    l.space = .shared ∧
      ((isB = false ∧ ∃ s, X.CpIssue i s) ∨
        (w.1 = f.1 ∧ w.2 < f.2 ∧ ∃ d s acc mask, X.MmaIssue i d s acc mask)) ∧
      baseCausality L X w f ∧ (∃ a bs, X.Writes f a bs ∧ a.Covers l)
  | _, _, _ => False

/-- Both the original proxy path and source reuse extend base causality after the wait. -/
def ObservedCompletionBefore (X : Execution) (l : Loc) (i : EvId)
    (p : AsyncCopy.Part) (w f : EvId) : Prop :=
  CompletionBefore L X l p w f ∨ TcReadReuseBefore L X l i p w f

/-- Source reuse has a wait-to-store base path. -/
theorem TcReadReuseBefore.base {X : Execution} {l : Loc} {i w f : EvId}
    {p : AsyncCopy.Part} (h : TcReadReuseBefore L X l i p w f) :
    baseCausality L X w f := by
  cases p <;> try contradiction
  exact h.2.2.1

theorem TcReadReuseBefore.congr {X Y : Execution} {l : Loc} {i w f : EvId}
    {p : AsyncCopy.Part} (hi : X.get i = Y.get i) (hf : X.get f = Y.get f)
    (hb : baseCausality L X w f ↔ baseCausality L Y w f) :
    TcReadReuseBefore L X l i p w f ↔ TcReadReuseBefore L Y l i p w f := by
  cases p <;> try rfl
  simp only [TcReadReuseBefore, Execution.CpIssue, Execution.MmaIssue, Execution.Writes,
    hi, hf, hb]

/-- The proxy and completion order at byte `l` (MEM-MODEL-CAUSALITY) between thread accesses and the
parts of asynchronous operations: `baseCausality` or a same-byte allocation-result handoff
between two thread accesses; from a thread access
to an asynchronous access, an async proxy fence (`ProxyBefore`), or `baseCausality` to the issue of
an operation performed in the generic proxy (`GenericCopy`); an observed completion
(`AsyncFinished`, `ObservedCompletionBefore`) from an asynchronous access to a thread access;
and a chain of observed completions (`AsyncChain`) between asynchronous accesses in one CTA or one
`cta_group::2` pair (`PairAsync`) when one of the two operations is a `cta_group::2` `tcgen05`
operation (`PairTc`). -/
def modelCausality (X : Execution) (l : Loc) : AsyncCopy.Ref → AsyncCopy.Ref → Prop
  | .thread e, .thread f => baseCausality L X e f ∨ Tmem.Pair.AllocResultBefore L X l e f
  | .thread e, .async i p => AsyncCovers X i p l ∧
    (ProxyBefore L X e i l ∨ (GenericCopy X i ∧ baseCausality L X e i))
  | .async i p, .thread f => AsyncCovers X i p l ∧
    ∃ w, AsyncFinished L X i p w ∧ ObservedCompletionBefore L X l i p w f
  | .async i p, .async j q =>
    (SameCta L i.1 j.1 ∨ PairAsync L l i.1 j.1 ∧ (PairTc X i ∨ PairTc X j)) ∧
      AsyncChain L X l (i, p) (j, q)

theorem modelCausality.of_base {X : Execution} {l : Loc} {e f : EvId}
    (h : baseCausality L X e f) : modelCausality L X l (.thread e) (.thread f) := .inl h

theorem modelCausality.of_allocResultBefore {X : Execution} {l : Loc} {e f : EvId}
    (h : Tmem.Pair.AllocResultBefore L X l e f) :
    modelCausality L X l (.thread e) (.thread f) := .inr h

/-- For an asynchronous operation that is not a `cp.async`, a thread access precedes its access
only through an async proxy fence. -/
theorem modelCausality_thread_async_of_not_generic {X : Execution} {l : Loc} {e i : EvId}
    {p : AsyncCopy.Part} (hg : ¬ GenericCopy X i) :
    modelCausality L X l (.thread e) (.async i p) ↔
      AsyncCovers X i p l ∧ ProxyBefore L X e i l := by
  simp only [modelCausality, hg, false_and, or_false]

end

end PTX
