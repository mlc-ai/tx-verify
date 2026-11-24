-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Waiting
public import Core.Memory.Order
public import Core.Thread.Run

@[expose] public section

/-!
# Causality, observation and per-object order (memory layer)

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## MEM-OBJECT-ORDER-CAUSALITY — memory-layer axioms over causality, observation and object order

Statement: An execution is allowed only if no cycle combines causality with the synchronizing part
  of the operation order of a single synchronization object, no synchronizing observation follows
  in causality the issue of what it observed, and no asynchronous update is placed in its object's
  order before an operation that is tied to its issue by program order, the object's lifetime or an
  acquire observation. Causality here is `stageCausality`, the model's extension of base causality
  (`baseCausality`, §8.9.5) to the issue and completion nodes of instructions and asynchronous
  stages: the stage order, base causality from a completion to a later issue, and a copy's release
  complete-tx to the successors of a wait that observes it.

Defs: CounterUpdate, MbarObserved, ReleaseUpdate, SyncObserved, CopyReleaseSync, stageCausality,
  CtaBarOn, OrderObject, ObjectOrder, MbarSyncRecord, MbarLifetimeRecord, SyncObjectOrder,
  ObservationCausal, ObjectCoherent, AsyncObjectOrdered, OrderObject.Enabling

Source:
- §8.9.1
- §8.9.1.1 (program order; asynchronous operations)
- §8.9.4 (synchronizes-with)
- §8.9.5 (base causality order)
- §8.10.1
- §8.10.6 (Coherence, Causality axioms)
- §8.8: "A release pattern on a location M consists of one of the following: A release operation
    on M E.g.: st.release [M]; or atom.release [M]; or mbarrier.arrive.release [M];"
- §8.8: "An acquire pattern on a location M consists of one of the following: An acquire operation
    on M E.g.: ld.acquire [M]; or atom.acquire [M]; or mbarrier.test_wait.acquire [M];"
- §8.7 (morally strong)
- §9.7.10.28.4.1
- §9.7.10.28.5.3 (copy stages; complete-tx upon completion of the copy; complete-tx has .release
    semantics at .cluster scope; mbarrier operand accessed using generic-proxy)
- §9.7.10.28.6.2 (bulk-group wait: writes being made visible to the executing thread)
- §9.7.10.28.3.3 (cp.async.wait_group)
- §9.7.15.16.5.1 (primary phases)
- §9.7.15.16.8 (atomic phase transition)
- §9.7.15.16.16
- §9.7.15.16.19: "The .relaxed qualifier does not provide any memory ordering semantics and
    visibility guarantees."
- §9.7.15.16.19: "When mbarrier.test_wait and mbarrier.try_wait operations with .acquire qualifier
    returns True , they form the acquire pattern as described in the Memory Consistency Model ."
- §9.7.15.18 (CLC complete-tx upon completion)
- §9.7.18.12.1 (commit signals upon completion of tracked operations)
- EXT-OBJECT-ORDER
- EXT-ASYNC-OBJECT
- EXT-STAGE-ORDER

Direction: reading

Applies: The issue/completion nodes of thread instructions and asynchronous stages

Premises: none

Effect: Consistent.observation, Consistent.object and Consistent.asyncObject. These are the
  memory-layer axioms. No edge of the dependency order (DEP-ORDER: needs, witnesses, the
  returns of blocking instructions and the canonical spins) enters them, so the collectives without
  memory text (vote, redux, shfl, match, elect, the `.sync` tcgen05 instructions, setmaxnreg, the
  warp-level matrix instructions) and the relaxed mbarrier observations order no memory operation.
  The barriers' memory effects are their own base-causality edges in MEM-BASE-CAUSALITY
  (`CtaBarSync`, `ClusterSync`, `WarpBarSync`, `MSync`), each with its memory quote.

Review: The litmus tests of these predicates are in `Tests/Progress/DependencyLitmus.lean` (K2, K3,
  K9, K9b). The shape follows the PTX axioms. Base causality order (§8.9.5) is the transitive
  closure of program order and synchronizes-with; observation (reads-from) is not part of it and
  appears only in the Causality axiom, `irreflexive(observation; causality)` (§8.10.6), and in
  Coherence (§8.10.1). Here `stageCausality` plays the part of base causality, `SyncObserved` of
  observation, and `SyncObjectOrder` of the coherence order of one object. A relaxed arrival
  observed by a relaxed wait is no observation of the memory layer: §8.4 lists no mbarrier
  instruction as a read, write or memory operation, §8.8 names only `mbarrier.arrive.release` and
  `mbarrier.test_wait.acquire` in the release and acquire patterns, and §9.7.15.16.19 gives
  `.relaxed` no ordering. So load buffering through two mbarriers with relaxed operations is not
  excluded here, and with release arrivals and acquire waits it is forbidden.
  Program-order edges are PTX's logical program order inside base causality. They are not a claim
  about execution time. Nodes are not time points: the object record point of a thread operation is
  its completion node, related to other nodes only through `stageCausality` and through the order of
  one object at a time. Exits of a CTA are not placed in any logical barrier's order (fewer edges).
  The stages of one asynchronous operation enter `stageCausality` through `StageOrder`, and a copy's
  complete-tx through `CopyReleaseSync`; each `stageCausality` relation rests on a quote that allows
  chaining it with base causality. §8.9.1.1 orders the operations of `cp.async`, `cp.async.bulk` and
  `cp.reduce.async.bulk` after prior instructions of the thread, but says of the complete-tx of
  `cp.async.bulk` and `cp.reduce.async.bulk` that it "is ordered only with respect to the memory
  operations performed by the same asynchronous instruction, and in particular it does not
  transitively establish ordering with respect to prior instructions from the issuing thread". So
  the relation `IssueStage` is not one of the edges of `stageCausality`, and `stageCausality` leads
  from a thread instruction only to thread instructions. A stage chain meets base causality through
  `CopyReleaseSync`, whose release orders exactly the memory operations of the same copy before the
  waiter's successors; the other stage chains (stores, MMA and commit, CLC) end at notifications
  with no outgoing `stageCausality` edge. Edges of `stageCausality` and `SyncObserved`, as (Lean
  names; class; PTX ISA 9.5; basis):
  - Issue to completion of one node, and stage to stage inside one asynchronous operation:
    `StageOrder`; class stageCausality; EXT-STAGE-ORDER and the stage quotes of
    DEP-ASYNC-STAGE-ORDER; basis: stated for copies and commit, reading EXT-STAGE-ORDER for MMA read
    to done and CLC resolve to write.
  - Program order and synchronizes-with between thread instructions: `baseCausality`; class
    stageCausality; §8.9.5; MEM-BASE-CAUSALITY lists the edges: po, `CtaBarSync`, `MSync`,
    `ClusterSync`, `WarpBarSync`, `synchronizesWith`, `FenceSync`; basis: stated.
  - Copy complete-tx (release, `.cluster`) to the program-order successors of an acquire wait
    observing it whose scope includes the issuing thread: `CopyReleaseSync`; class stageCausality;
    §9.7.10.28.4.1, §9.7.10.28.5.3, §9.7.15.16.19, §8.7; basis: stated.
  - Release counter update (a `.release` arrival, or a copy's complete-tx) counted in the phase an
    acquire wait observes, scopes meeting: `SyncObserved` (1st), `MbarObserved`, `ReleaseUpdate`;
    class observation; §8.8 (release and acquire patterns), §9.7.15.16.19; basis: stated.
  - Covered stage of a group wait: `SyncObserved` (2nd), `GroupWaitsFor`, `GroupWaitStages`; class
    observation; §9.7.10.28.6.2, §9.7.10.28.3.3; basis: stated.
  Order of one object, as (Lean names; PTX ISA 9.5; basis):
  - One mbarrier's history: `ObjectOrder` `.mbar`, `MBarrier.Before`; its memory part
    `SyncObjectOrder` keeps the pairs of two synchronizing records whose scopes meet, the pairs with
    the object's `mbarrier.init` or `mbarrier.inval`, and the pairs of one thread; §9.7.15.16.8,
    §8.8, §9.7.15.16.5.1; basis: reading EXT-OBJECT-ORDER.
  - One logical CTA barrier (CTA, ID): `ObjectOrder` `.ctaBar`, `CtaBarOn`; §9.7.15.1; basis:
    reading EXT-OBJECT-ORDER; whole order in both layers.
  - One cluster barrier history: `ObjectOrder` `.cluster`; §9.7.15.3; basis: reading
    EXT-OBJECT-ORDER; whole order in both layers.
  - One CTA's Tensor Memory allocator: `ObjectOrder` `.tmem`, `Tmem.Pair.Precedes`; not in the
    dependency axiom (`OrderObject.Enabling`); §9.7.18.7.1; basis: reading EXT-TMEM-ALLOC-ORDER.
  `clusterScopeMbar` remains a separate explicit assumption: it adds synchronization for
  `.cta`-scoped arrivals and waits at the sites it selects and is not part of these predicates.

### EXT-ASYNC-OBJECT — an asynchronous update follows its issue in its object's order

Statement: An update that an asynchronous operation makes to an mbarrier, a complete-tx or an
  arrive-on, comes in that mbarrier's order after every operation of the issuing thread that
  precedes the issuing instruction in program order. It also comes after the object's
  `mbarrier.init` or `mbarrier.inval`, and after an acquire wait that observes it, whenever that
  operation causally precedes the issuing instruction.

Source:
- §8.9.1.1: "These asynchronous operations are ordered after prior instructions in the same
    thread"
- §9.7.10.28.5.3 (the complete-tx is performed upon completion of the copy)
- §9.7.18.12.1 (the commit's arrive-on is signalled upon completion of the tracked operations)
- §9.7.15.18
- §8.8 (acquire pattern)

Why it is not spec text: The quoted text states the ordering of the operation's memory accesses and
  not the object order of its notification. The model reads it as: the update of an object by an
  asynchronous operation comes, in that object's atomic order, after the operations of the same
  object that the manual ties to the issue: the issuing thread's earlier operations (program
  order), the object's lifetime records, and an acquire wait that observes the update. Other
  operations of other threads, relaxed operations among them, do not take part, whatever the
  notification's release semantics, because a relaxed operation forms no synchronization (§8.8,
  §9.7.15.16.19).

Evidence: An operation completes after it is issued, and the canonical pipelines initialize an
  mbarrier, publish the initialization (`fence.mbarrier_init`, then a CTA or cluster barrier) and
  only then issue copies or commits that signal it (CUTLASS (NVIDIA/cutlass) commit b2f249ac
  (v4.8.0-23), include/cutlass/pipeline/sm90_pipeline.hpp, sm100_pipeline.hpp); a notification that
  reached the object before its initialization would make these programs fault.

Direction: reading

Effect: Executions in which an asynchronous update is ordered in its object's history before such
  an operation are removed from `Consistent`; if hardware allows them, the model excludes executions
  that may occur. The relaxed-poll example with a copy's complete-tx (K9b in
  `Tests/Progress/DependencyLitmus.lean`) stays consistent. Disclosed by every kernel whose
  statement names `Op.cpBulk`, `Op.cpTensor`, `Op.tcCommit` or `Op.clcTryCancel`: FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm, TmaCopy.

### EXT-OBJECT-ORDER — the operations on one synchronization object are totally ordered

Statement: (Execution layer.) The operations on one mbarrier, on one CTA barrier and on one cluster
  barrier each take effect in a single total order, the history the execution records for the
  object, and the dependency order together with that order of any single object has no cycle
  (`DependencyOk.acyclic`, DEP-ORDER). (Memory layer.) For an mbarrier, the pairs of that
  order of two synchronizing records whose scopes meet, the pairs with the object's initialization
  or invalidation, and the pairs of one thread never contradict causality; for a CTA barrier or a
  cluster barrier the whole order never does (`ObjectCoherent` over `SyncObjectOrder`).

Source:
- §9.7.15.16.8 (mbarrier; when the phase completes): "the following actions are performed
    atomically"
- §8.10.1 (mbarrier; coherence orders only overlapping writes)
- §8.10.5 (mbarrier)
- §9.7.15.1 (CTA barrier): "Each CTA instance has sixteen barriers"
- §9.7.15.1 (CTA barrier): "the barrier is reinitialized so that it can be immediately reused"
- §9.7.15.3 (cluster barrier): "the barrier completes and is automatically reinitialized"
- §8.4: "read operation All variants of ld instruction and atom instruction (but not red
    instruction)."
- §8.4: "write operation All variants of st instruction, and atomic operations if they result in a
    write."
- §8.8 (release and acquire patterns, as quoted in MEM-OBJECT-ORDER-CAUSALITY)
- §9.7.15.16.19: "The .relaxed qualifier does not provide any memory ordering semantics and
    visibility guarantees."
- §9.7.15.16.5.1: "In each primary phase {0, 1, 2, …}, threads perform in program order :
    arrive-on operations to complete the current primary phase and test_wait / try_wait operations
    to check for the completion of the current primary phase."

Why it is not spec text: §8.10.1 orders writes to overlapping memory locations. The CTA barrier and
  the cluster barrier have no memory location, and for the mbarrier the text states the atomicity of
  one phase transition. It does not state that all its operations form one order that agrees with
  causality. One order per object is the reading that each such object is a single atomic state
  machine whose operations take effect one after another. The memory part is restricted for the
  mbarrier because the manual is inconsistent about it: §8.4 lists only `ld` and `atom` as read
  operations and `st` and atomic writes as write operations, while §8.8 names
  `mbarrier.arrive.release [M]` and `mbarrier.test_wait.acquire [M]` as release and acquire
  operations, and §8.9.4 requires a write in the release pattern and a read in the acquire pattern.
  So it is unclear whether a release or acquire mbarrier operation is a write or read operation of
  the memory model, and whether a relaxed one is a strong operation. The model keeps every
  execution that either reading allows: synchronization is taken only from the release and acquire
  mbarrier operations that §8.8 names, with scopes that include each other's thread (§8.7), and a
  relaxed mbarrier operation contributes no memory-layer order. No proof may derive an order from a
  relaxed poll combined with a release/acquire chain.

Direction: reading

Effect: Executions in which the operations on one object cannot be ordered consistently with the
  dependency order, or its synchronizing part with causality, are removed. The relaxed-poll example
  (K9 in `Tests/Progress/DependencyLitmus.lean`: one thread's relaxed poll succeeds and then it
  stores with release; another thread loads that value with acquire and then arrives relaxed) stays
  consistent. The fourth object kind, one CTA's Tensor Memory allocator, is EXT-TMEM-ALLOC-ORDER.
  Disclosed by every kernel whose statement names `Op.mbarInit`, `Op.mbarArrive`, `Op.mbarWait`,
  `Op.barSync`, `Op.barSyncN`, `Op.barArrive` or `Op.cluster`: BlockSum, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.

### EXT-STAGE-ORDER — the stages of one operation follow each other

Statement: Within one operation, the issue precedes the completion, the operand reads of a tracked
  `tcgen05.mma` precede its completion, and the resolution of a CLC request precedes the write of
  its response. (1) The issue of an instruction or stage precedes its completion: the two points of
  one node (`StageOrder`). (2) The reads of the operands of a tracked `tcgen05.mma` precede its
  completion, and the resolution of a `clusterlaunchcontrol.try_cancel` request precedes the write
  of its response (`StageEdge`).

Source:
- §9.7.10.28.5.3 (1): "Upon the completion of the asynchronous copy operation, the complete-tx
    operation, with completeCount argument equal to amount of data copied in bytes, will be
    performed on the mbarrier object specified by the operand mbar"
- §9.7.18.12.1 (1): "Upon the completion of the tracked asynchronous tcgen05 operations, the signal
    specified by the .completion_mechanism is triggered by the system on the mbarrier object"
- §9.7.18.10.10.1 (2, tcgen05.mma): "is an asynchronous instruction which initiates an MxNxK matrix
    multiply and accumulate operation, D = A*B+D"
- §9.7.15.18 (2, try_cancel): "asynchronously writes an opaque response to shared memory indicating
    whether the operation succeeded or failed"

Why it is not spec text: The sentences state that completion follows initiation and that a response
  indicates the outcome. They state no order between the operand reads and the completion, or
  between the resolution and the response write. The edges read completion as following the
  initiation, and the result as following the decision that it reports.

Evidence: Each edge relates two points of one hardware operation (an operation cannot complete
  before it is issued or report an outcome before it is decided), and no edge of this reading leads
  from one operation to a different one.

Direction: reading

Effect: Executions in which a completion precedes its own issue, an MMA completes before its operand
  reads, or a CLC response is written before its request resolves are removed from `Consistent`
  (`Consistent.observation`, `.object`, `.dependency`, ERR-SHARED-LIFETIME). If hardware allows
  them, the model excludes executions that may occur. Disclosed by every kernel whose statement
  names `Op.mbarInit`, `Op.mbarArrive`, `Op.mbarWait`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive`,
  `Op.cluster`, `Op.cpBulk`, `Op.cpTensor`, `Op.cpTensorStore`, `Op.tcMma`, `Op.tcCommit` or
  `Op.clcTryCancel`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192,
  InklingRelDecode, RmsNorm, TcGemm, TmaCopy.
-/

/-- The mbarrier operations that change its counters: arrivals (including asynchronous
arrive-on notifications), the pending-count increment of `cp.async.mbarrier.arrive`, and
complete-tx. Initialization and polls are not updates. -/
def CounterUpdate : MBarrier.Action → Prop
  | .arrive .. => True
  | .increment => True
  | .completeTx _ => True
  | _ => False

/-- The present counter update `x` belongs to the phase whose completion the successful
wait `w` observed (`AsyncCopy.WaitObserves`, any qualifiers). Relaxed and release updates
alike; the memory layer uses it only through `SyncObserved`. -/
def MbarObserved (X : Execution) (x w : AsyncCopy.Ref) : Prop :=
  X.RefPresent x ∧ ∃ j m acquire ws, w = .thread j ∧ AsyncCopy.WaitObserves X x j m acquire ws ∧
    ∀ r ∈ X.objects m, r.id = x → CounterUpdate r.action

/-- `x` is a release counter update by thread `g` at scope `s`: a `.release` arrival, or the
complete-tx of a bulk or tensor copy (`.release` at `.cluster` scope, §9.7.10.28.5.3). -/
def ReleaseUpdate (X : Execution) (x : AsyncCopy.Ref) (s : MbarScope) (g : Nat) : Prop :=
  (∃ j m tx count, x = .thread j ∧ g = j.1 ∧ X.Arrive j m tx count true s) ∨
  (∃ i, (x = .async i (.notify .copy) ∨ x = .async i (.notify .load)) ∧ g = i.1 ∧ s = .cluster)

/-- `w` observed `x` with a synchronization the manual states: an acquire wait observing a release
counter update of its phase, with scopes that include each other's thread (§8.8, §8.7), or a group
wait covering the stage `x` of one of its operations (§9.7.10.28.6.2, §9.7.10.28.3.3). -/
def SyncObserved (X : Execution) (x w : AsyncCopy.Ref) : Prop :=
  (MbarObserved X x w ∧ ∃ j m pc q ws us g, w = .thread j ∧
    X.get j = some ⟨pc, .wait m q true true ws⟩ ∧ ReleaseUpdate X x us g ∧
    ScopesMeet L us g ws j.1) ∨
  (∃ i p j k, x = .async i p ∧ w = .thread j ∧ X.AsyncPresent i p ∧ GroupWaitsFor X k i j ∧
    p ∈ GroupWaitStages X i k)

/-- The release complete-tx (`.cluster` scope) of a tensor or bulk copy synchronizes with an
acquire wait observing it whose scope includes the issuing thread, ordering it before the
wait's program-order successor `f`. -/
def CopyReleaseSync (X : Execution) (n : AsyncCopy.Ref) (f : EvId) : Prop :=
  ∃ i p w ws, n = .async i p ∧ (p = .notify .copy ∨ p = .notify .load) ∧
    AsyncCopy.AsyncObserved X i p w true ws ∧ ScopesMeet L .cluster i.1 ws w.1 ∧ po X w f

/-- The model's extension of base causality (`baseCausality`, §8.9.5) to nodes: the stage order
(`StageOrder`, which also orders the issue point of a thread instruction before its completion
point), `baseCausality` from the completion of a thread instruction to the issue of another, and a
copy's release complete-tx to the successors of a wait observing it. Read it through its
transitive closure. The relation `IssueStage` is not one of its edges. -/
def stageCausality (X : Execution) : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | (e, b), (f, b') =>
    StageOrder X (e, b) (f, b') ∨
    (b = true ∧ b' = false ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧ baseCausality L X i j) ∨
    (b = true ∧ b' = false ∧ ∃ j, f = .thread j ∧ CopyReleaseSync L X e j)

/-- A CTA barrier history record belongs to logical barrier `id`; exits belong to none. -/
def CtaBarOn (id : Fin 16) : CtaBarrier.Record EvId → Prop
  | .arrival n .. => n = id.val
  | .exit .. => False

/-- One object with an atomic operation order. -/
inductive OrderObject where
  | mbar (m : Loc)
  | ctaBar (cta : Nat) (id : Fin 16)
  | cluster (cluster : Nat)
  | tmem (cta : Nat)

/-- The recorded operation order of one object. -/
def ObjectOrder (X : Execution) :
    OrderObject → AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | .mbar m, (e, b), (f, b') => b = true ∧ b' = true ∧ MBarrier.Before (X.objects m) e f
  | .ctaBar c id, (e, b), (f, b') => b = false ∧ b' = false ∧
      ∃ i j, e = .thread i ∧ f = .thread j ∧
      (∃ ev, X.get i = some ev) ∧ (∃ ev, X.get j = some ev) ∧
      ∃ (k l : Nat) (r q : CtaBarrier.Record EvId),
        (X.barriers c)[k]? = some r ∧ (X.barriers c)[l]? = some q ∧ k < l ∧
        CtaBarOn id r ∧ CtaBarOn id q ∧ i ∈ r.refs ∧ j ∈ q.refs
  | .cluster c, (e, b), (f, b') => ∃ i j, e = .thread i ∧ f = .thread j ∧
      (∃ ev, X.get i = some ev) ∧ (∃ ev, X.get j = some ev) ∧
      ∃ (k l : Nat) (r q : ClusterBarrier.Record EvId),
        (X.clusters c)[k]? = some r ∧ (X.clusters c)[l]? = some q ∧ k < l ∧
        i ∈ r.refs ∧ j ∈ q.refs ∧ b = ClusterPoint r ∧ b' = ClusterPoint q
  | .tmem cta, (e, b), (f, b') => b = true ∧ b' = true ∧ ∃ i j, e = .thread i ∧ f = .thread j ∧
      Tmem.Pair.Precedes L X cta i j

/-- The record `x` of mbarrier `m` synchronizes in the manual's terms, performed by thread `g` at
scope `s`: a release arrival or a bulk or tensor copy's complete-tx (`ReleaseUpdate`), or an
acquire poll that returned True (§8.8, §9.7.15.16.19). -/
def MbarSyncRecord (X : Execution) (m : Loc) (x : AsyncCopy.Ref) (s : MbarScope) (g : Nat) :
    Prop :=
  (ReleaseUpdate X x s g ∧ ((∃ j tx count, x = .thread j ∧ X.Arrive j m tx count true s) ∨
    ∃ i p, x = .async i p)) ∨
  ∃ j pc q, x = .thread j ∧ g = j.1 ∧ X.get j = some ⟨pc, .wait m q true true s⟩

/-- The record `x` is the initialization or invalidation of mbarrier `m`. -/
def MbarLifetimeRecord (X : Execution) (m : Loc) (x : AsyncCopy.Ref) : Prop :=
  ∃ j, x = .thread j ∧ ((∃ c, X.MbInit j m c) ∨ X.MbInval j m)

/-- The part of one object's order that the memory layer combines with causality
(EXT-OBJECT-ORDER): for an mbarrier, the pairs of two synchronizing records whose scopes include
each other's thread, the pairs with its initialization or invalidation, and the pairs of one
thread; for every other object, its whole order. -/
def SyncObjectOrder (X : Execution) :
    OrderObject → AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | .mbar m, a, c => ObjectOrder L X (.mbar m) a c ∧
      ((∃ s g s' g', MbarSyncRecord X m a.1 s g ∧ MbarSyncRecord X m c.1 s' g' ∧
          ScopesMeet L s g s' g') ∨
        MbarLifetimeRecord X m a.1 ∨ MbarLifetimeRecord X m c.1 ∨
        ∃ i j, a.1 = .thread i ∧ c.1 = .thread j ∧ i.1 = j.1)
  | o, a, c => ObjectOrder L X o a c

/-- A synchronizing observer's return does not causally precede the issue of what it observed
(`irreflexive(observation; causality)`). -/
def ObservationCausal (X : Execution) : Prop :=
  ∀ x w, SyncObserved L X x w → ¬ Relation.TransGen (stageCausality L X) (w, true) (x, false)

/-- Causality together with the synchronizing part of the order of any single object has no
cycle. -/
def ObjectCoherent (X : Execution) : Prop :=
  ∀ o n, ¬ Relation.TransGen (fun a c => stageCausality L X a c ∨ SyncObjectOrder L X o a c) n n

/-- EXT-ASYNC-OBJECT: an asynchronous update `.async i p` on object `m` is not before, in `m`'s
history, an earlier operation of the issuing thread, and not before the object's initialization
or invalidation or an acquire wait observing the update when that operation causally precedes
the issue of `i`. -/
def AsyncObjectOrdered (X : Execution) : Prop :=
  ∀ m i p y, MBarrier.Before (X.objects m) (.async i p) y →
    (¬ ∃ j, y = .thread j ∧ j.1 = i.1 ∧ j.2 < i.2) ∧
    ((MbarLifetimeRecord X m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves X (.async i p) j m true ws) →
      ¬ Relation.TransGen (stageCausality L X) (y, true) (.thread i, false))

/-- The objects whose order enters the dependency axiom (`DependencyOk.acyclic`): all but the
Tensor Memory allocator histories (EXT-TMEM-ALLOC-ORDER). -/
def OrderObject.Enabling : OrderObject → Prop
  | .tmem _ => False
  | _ => True

end

end PTX
