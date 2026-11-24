# Barriers and warp collectives

How the model treats CTA barriers (`bar`, `barrier`), cluster barriers (`barrier.cluster`), cluster membership, and the warp collectives `bar.warp.sync`, `elect.sync`, `shfl.sync`, `vote.sync`, `redux.sync`, `match.sync` and `activemask`, together with the rule that threads of a warp agree on the guard of a uniform instruction. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [CTA barriers](#cta-barriers)
    - [`CtaBarrier.Slot`](#c-ctabarrier-slot)
    - [`CtaBarrier.State`](#c-ctabarrier-state)
    - [`CtaBarrier.Error`](#c-ctabarrier-error)
    - [`CtaBarrier.arrive`](#c-ctabarrier-arrive)
    - [`CtaBarrier.exitThread`](#c-ctabarrier-exitthread)
    - [`CtaBarrier.Record`](#c-ctabarrier-record)
    - [`CtaBarrier.run`](#c-ctabarrier-run)
    - [`CtaBarrier.GenerationOf`](#c-ctabarrier-generationof)
    - [`CtaBarrier.Released`](#c-ctabarrier-released)
    - [`CtaBarArrivalK`](#c-ctabararrivalk)
    - [`CtaBarK`](#c-ctabark)
    - [`CtaBarDone`](#c-ctabardone)
    - [`CtaBarSync`](#c-ctabarsync)
  - [Clusters](#clusters)
    - [`Launch.oneDimLaunch`](#c-launch-onedimlaunch)
    - [`Launch.clusterOfCta`](#c-launch-clusterofcta)
    - [`Launch.rankOfCta`](#c-launch-rankofcta)
    - [`Launch.peerCta`](#c-launch-peercta)
    - [`Launch.mapShared`](#c-launch-mapshared)
    - [`SameCluster`](#c-samecluster)
  - [Cluster barriers](#cluster-barriers)
    - [`ClusterBarrier.State`](#c-clusterbarrier-state)
    - [`ClusterBarrier.Action`](#c-clusterbarrier-action)
    - [`ClusterBarrier.Outcome`](#c-clusterbarrier-outcome)
    - [`ClusterBarrier.perform`](#c-clusterbarrier-perform)
    - [`ClusterBarrier.Record`](#c-clusterbarrier-record)
    - [`ClusterBarrier.run`](#c-clusterbarrier-run)
    - [`ClusterBarrier.ArrivalOf`](#c-clusterbarrier-arrivalof)
    - [`ClusterBarrier.WaitOf`](#c-clusterbarrier-waitof)
    - [`ClusterBarrier.Synchronizes`](#c-clusterbarrier-synchronizes)
    - [`ClusterSync`](#c-clustersync)
  - [Warp collectives](#warp-collectives)
    - [`electMember`](#c-electmember)
    - [`Execution.Elect`](#c-execution-elect)
    - [`Execution.WarpBar`](#c-execution-warpbar)
    - [`WarpBarSync`](#c-warpbarsync)
    - [`shflSource`](#c-shflsource)
    - [`Execution.ShflK`](#c-execution-shflk)
    - [`voteClass`](#c-voteclass)
    - [`maskInWarp`](#c-maskinwarp)
    - [`Execution.MaskK`](#c-execution-maskk)
    - [`MaskInstance`](#c-maskinstance)
    - [`MaskWait`](#c-maskwait)
    - [`voteResult`](#c-voteresult)
    - [`reduxResult`](#c-reduxresult)
    - [`matchMask`](#c-matchmask)
  - [Warp-uniform control flow](#warp-uniform-control-flow)
    - [`Visit`](#c-visit)
    - [`Walk`](#c-walk)
    - [`DepBefore`](#c-depbefore)
    - [`SameUniformGroup`](#c-sameuniformgroup)
    - [`WarpDivergent`](#c-warpdivergent)
- [Rules](#rules)
  - [What a barrier or collective instruction does](#what-a-barrier-or-collective-instruction-does)
    - [barrier arrival](#thread-bar) (`THREAD-BAR`)
      - [`bar.sync b, 0` means every thread of the CTA](#ext-bar-zero-count) (`EXT-BAR-ZERO-COUNT`)
    - [named CTA barrier resources and generations](#obj-cta-barrier-state) (`OBJ-CTA-BARRIER-STATE`)
    - [cluster arrival, completion and observation](#obj-cluster-barrier-state) (`OBJ-CLUSTER-BARRIER-STATE`)
      - [a cluster wait waits for the phase of its thread's latest arrival](#ext-cluster-wait-phase) (`EXT-CLUSTER-WAIT-PHASE`)
    - [warp barrier template](#thread-warp-bar) (`THREAD-WARP-BAR`)
    - [leader election template](#thread-elect) (`THREAD-ELECT`)
    - [warp shuffle](#thread-shfl) (`THREAD-SHFL`)
    - [warp vote](#thread-vote) (`THREAD-VOTE`)
    - [integer warp reduction](#thread-redux) (`THREAD-REDUX`)
    - [warp match](#thread-match) (`THREAD-MATCH`)
    - [active-thread query](#thread-activemask) (`THREAD-ACTIVEMASK`)
    - [matrix loads, stores and the register transpose](#thread-matrix) (`THREAD-MATRIX`)
    - [warp-level matrix multiply-accumulate](#thread-mma-sync) (`THREAD-MMA-SYNC`)
  - [Cluster membership](#cluster-membership)
    - [cluster membership, coordinates and logical peer addresses](#prog-cluster) (`PROG-CLUSTER`)
      - [cluster coordinates and rank](#ext-cluster-rank) (`EXT-CLUSTER-RANK`)
  - [Which executions are allowed](#which-executions-are-allowed)
    - [actual arrivals identify barrier generations](#obj-cta-barrier-history) (`OBJ-CTA-BARRIER-HISTORY`)
    - [named-resource histories refer to source arrivals](#obj-cta-barrier-sync) (`OBJ-CTA-BARRIER-SYNC`)
    - [collective arrivals and completed waits](#obj-cluster-barrier-history) (`OBJ-CLUSTER-BARRIER-HISTORY`)
    - [cluster synchronization and rendezvous](#obj-cluster-barrier-sync) (`OBJ-CLUSTER-BARRIER-SYNC`)
    - [warp rendezvous and memory ordering](#dep-warp-barrier) (`DEP-WARP-BARRIER`)
    - [completed election collectives](#dep-warp-elect) (`DEP-WARP-ELECT`)
      - [the lanes of one election execute one `elect.sync` instruction](#ext-elect-site) (`EXT-ELECT-SITE`)
    - [warp shuffle instances](#dep-warp-shuffle) (`DEP-WARP-SHUFFLE`)
      - [the source lane of `shfl.sync.up` is an integer difference](#ext-shfl-up-index) (`EXT-SHFL-UP-INDEX`)
    - [instances of a masked warp collective](#dep-warp-instance) (`DEP-WARP-INSTANCE`)
      - [the n-th executions with one member mask form one instance](#ext-warp-instance) (`EXT-WARP-INSTANCE`)
    - [warp vote instances](#dep-warp-vote) (`DEP-WARP-VOTE`)
    - [integer warp reduction instances](#dep-warp-redux) (`DEP-WARP-REDUX`)
    - [warp match instances](#dep-warp-match) (`DEP-WARP-MATCH`)
    - [the mask of active threads](#dep-warp-activemask) (`DEP-WARP-ACTIVEMASK`)
    - [fragment layouts](#thread-matrix-layout) (`THREAD-MATRIX-LAYOUT`)
      - [the layouts and the row accesses of ldmatrix, stmatrix and movmatrix](#ext-matrix-figures) (`EXT-MATRIX-FIGURES`)
      - [the sparse metadata layout](#ext-mma-sparse-figures) (`EXT-MMA-SPARSE-FIGURES`)
      - [the fragment layouts of mma.sync, including the A columns of `mma.m16n8k256`](#ext-mma-fragments) (`EXT-MMA-FRAGMENTS`)
    - [instances of the warp-level matrix instructions](#dep-warp-matrix) (`DEP-WARP-MATRIX`)
    - [the values of `mma` and `mma.sp`](#dep-warp-mma) (`DEP-WARP-MMA`)
  - [What counts as an error](#what-counts-as-an-error)
    - [aligned participants execute the same instruction](#err-aligned-mismatch) (`ERR-ALIGNED-MISMATCH`)
    - [divergent barrier collectives](#err-barrier-mismatch) (`ERR-BARRIER-MISMATCH`)
      - [the participants of an aligned barrier or setmaxnreg](#ext-bar-participants) (`EXT-BAR-PARTICIPANTS`)
    - [an arrival the CTA barrier resource cannot perform](#err-cta-barrier) (`ERR-CTA-BARRIER`)
    - [an operation the cluster barrier cannot perform](#err-cluster-barrier) (`ERR-CLUSTER-BARRIER`)
    - [warp-uniform control flow](#err-nonuniform-guard) (`ERR-NONUNIFORM-GUARD`)
      - [executions ordered by blocking collectives are not executed together](#ext-dependency-order) (`EXT-DEPENDENCY-ORDER`)
    - [an instance whose result cannot be computed](#err-warp-matrix) (`ERR-WARP-MATRIX`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### CTA barriers

The sixteen barrier resources of a CTA, their generations, and how recorded arrivals refer to source events.

<a id="c-ctabarrier-slot"></a>
#### `CtaBarrier.Slot`

*structure*

One of the sixteen barrier resources of a CTA (§9.7.15.1): the number of its current
generation, the number of warp arrivals that generation requests, and the warps that have
arrived in it.

- `generation`: The number of the current generation; completion increments it.
- `expected`: Number of warp arrivals requested in the active generation.
- `arrived`: The warps that have arrived in the current generation.

[Lean source: `Core/Sync/CtaBarrierObject.lean` L49-L59](../../Core/Sync/CtaBarrierObject.lean#L49-L59)

<a id="c-ctabarrier-state"></a>
#### `CtaBarrier.State`

*structure*

The barrier resources of one CTA together with the threads of the CTA that have exited.

- `slots`: The resource with each barrier number.
- `exited`: The threads of the CTA that have exited.

[Lean source: `Core/Sync/CtaBarrierObject.lean` L61-L66](../../Core/Sync/CtaBarrierObject.lean#L61-L66)

<a id="c-ctabarrier-error"></a>
#### `CtaBarrier.Error`

*inductive*

The ways an update of the barrier resources fails.

- `badId`
- `badCount`
- `badWarp`
- `countMismatch`
- `duplicateArrival`
- `badExit`

[Lean source: `Core/Sync/CtaBarrierObject.lean` L68-L71](../../Core/Sync/CtaBarrierObject.lean#L68-L71)

<a id="c-ctabarrier-arrive"></a>
#### `CtaBarrier.arrive`

*def*

One warp's arrival at one named resource. The old generation identifies its wait.

[Lean source: `Core/Sync/CtaBarrierObject.lean` L118-L131](../../Core/Sync/CtaBarrierObject.lean#L118-L131)

<a id="c-ctabarrier-exitthread"></a>
#### `CtaBarrier.exitThread`

*def*

Exit is visible to every resource of this CTA; it is not a barrier arrival.

[Lean source: `Core/Sync/CtaBarrierObject.lean` L133-L137](../../Core/Sync/CtaBarrierObject.lean#L133-L137)

<a id="c-ctabarrier-record"></a>
#### `CtaBarrier.Record`

*inductive*

One update of the barrier resources of a CTA, naming its source events by references of type
`α`: the collective arrival of one warp (its barrier number, warp, count and arriving lanes), or
the exit of a thread.

- `arrival`
- `exit`

[Lean source: `Core/Sync/CtaBarrierHistory.lean` L39-L44](../../Core/Sync/CtaBarrierHistory.lean#L39-L44)

<a id="c-ctabarrier-run"></a>
#### `CtaBarrier.run`

*def*

Apply the records of a history in order, from the state of the first.

[Lean source: `Core/Sync/CtaBarrierHistory.lean` L64-L67](../../Core/Sync/CtaBarrierHistory.lean#L64-L67)

<a id="c-ctabarrier-generationof"></a>
#### `CtaBarrier.GenerationOf`

*def*

A source arrival's generation is read from the resource, not a thread ordinal.

[Lean source: `Core/Sync/CtaBarrierHistory.lean` L73-L78](../../Core/Sync/CtaBarrierHistory.lean#L73-L78)

<a id="c-ctabarrier-released"></a>
#### `CtaBarrier.Released`

*def*

Completion is a specific update in the history, preserved by later updates.

[Lean source: `Core/Sync/CtaBarrierHistory.lean` L86-L89](../../Core/Sync/CtaBarrierHistory.lean#L86-L89)

<a id="c-ctabararrivalk"></a>
#### `CtaBarArrivalK`

*def*

`e` is an arrival of either form at instance `key`: `key % 16` is the barrier ID and
`key / 16` its actual resource generation.

[Lean source: `Core/Sync/CtaBarrierExecution.lean` L84-L90](../../Core/Sync/CtaBarrierExecution.lean#L84-L90)

<a id="c-ctabark"></a>
#### `CtaBarK`

*def*

`e` is a `bar.sync` arrival at instance `key`: `key % 16` is the barrier ID; `key / 16` is its
actual resource generation.

[Lean source: `Core/Sync/CtaBarrierExecution.lean` L92-L98](../../Core/Sync/CtaBarrierExecution.lean#L92-L98)

<a id="c-ctabardone"></a>
#### `CtaBarDone`

*def*

The generation of instance `key` of the barrier resources of CTA `cta` has completed.

[Lean source: `Core/Sync/CtaBarrierExecution.lean` L100-L102](../../Core/Sync/CtaBarrierExecution.lean#L100-L102)

<a id="c-ctabarsync"></a>
#### `CtaBarSync`

*def*

Generic memory synchronization through two actual arrivals in one named phase: an
arrival of either form after `e`, and a `bar.sync` arrival before `f`.

[Lean source: `Core/Sync/CtaBarrierExecution.lean` L104-L109](../../Core/Sync/CtaBarrierExecution.lean#L104-L109)

### Clusters

Cluster membership, ranks and peer addresses.

<a id="c-launch-onedimlaunch"></a>
#### `Launch.oneDimLaunch`

*def*

A one-dimensional launch with clusters of one shape whose grid is a whole number of clusters
(§2.2.2): the launch condition of the kernels proved with the one-dimensional model.

[Lean source: `Core/Sync/Cluster.lean` L196-L199](../../Core/Sync/Cluster.lean#L196-L199)

<a id="c-launch-clusterofcta"></a>
#### `Launch.clusterOfCta`

*def*

The cluster that contains CTA `cta`.

[Lean source: `Core/Sync/Cluster.lean` L125-L126](../../Core/Sync/Cluster.lean#L125-L126)

<a id="c-launch-rankofcta"></a>
#### `Launch.rankOfCta`

*def*

The rank of CTA `cta` in its cluster (`%cluster_ctarank`).

[Lean source: `Core/Sync/Cluster.lean` L128-L129](../../Core/Sync/Cluster.lean#L128-L129)

<a id="c-launch-peercta"></a>
#### `Launch.peerCta`

*def*

The CTA with rank `rank` in the cluster of CTA `cta`, if there is one. The rank is relative
to that cluster and is not a grid-wide CTA number.

[Lean source: `Core/Sync/Cluster.lean` L319-L325](../../Core/Sync/Cluster.lean#L319-L325)

<a id="c-launch-mapshared"></a>
#### `Launch.mapShared`

*def*

Logical meaning of mapa on a shared location within the issuer's cluster.

[Lean source: `Core/Sync/Cluster.lean` L327-L332](../../Core/Sync/Cluster.lean#L327-L332)

<a id="c-samecluster"></a>
#### `SameCluster`

*def*

Threads `g` and `h` belong to CTAs of one cluster.

[Lean source: `Core/Sync/Cluster.lean` L334-L337](../../Core/Sync/Cluster.lean#L334-L337)

### Cluster barriers

The barrier of one cluster, its phases and the recorded arrivals and waits.

<a id="c-clusterbarrier-state"></a>
#### `ClusterBarrier.State`

*structure*

The state of the barrier of one cluster (§9.7.15.3).

- `phase`: The number of the current phase; completion increments it.
- `arrived`: The threads that have arrived in the current phase.
- `exited`: The threads of the cluster that have exited.
- `lastArrival`: The phase of each thread's latest arrival, if it has arrived.

[Lean source: `Core/Sync/ClusterBarrierObject.lean` L91-L100](../../Core/Sync/ClusterBarrierObject.lean#L91-L100)

<a id="c-clusterbarrier-action"></a>
#### `ClusterBarrier.Action`

*inductive*

An operation on the cluster barrier: `barrier.cluster.arrive` (release or relaxed),
`barrier.cluster.wait`, or the exit of a thread.

- `arrive`
- `wait`
- `exit`

[Lean source: `Core/Sync/ClusterBarrierObject.lean` L102-L108](../../Core/Sync/ClusterBarrierObject.lean#L102-L108)

<a id="c-clusterbarrier-outcome"></a>
#### `ClusterBarrier.Outcome`

*inductive*

The result of an operation: the new state, a blocked wait, or a fault.

- `done`
- `blocked`
- `fault`

[Lean source: `Core/Sync/ClusterBarrierObject.lean` L120-L124](../../Core/Sync/ClusterBarrierObject.lean#L120-L124)

<a id="c-clusterbarrier-perform"></a>
#### `ClusterBarrier.perform`

*def*

The effect of one operation on the barrier of a cluster with `threads` threads.

[Lean source: `Core/Sync/ClusterBarrierObject.lean` L132-L146](../../Core/Sync/ClusterBarrierObject.lean#L132-L146)

<a id="c-clusterbarrier-record"></a>
#### `ClusterBarrier.Record`

*inductive*

One update of the barrier of a cluster, naming its source events by references of type `α`:
the collective arrival or wait of the live lanes of one warp, or the exit of a thread.

- `arrival`
- `wait`
- `exit`

[Lean source: `Core/Sync/ClusterBarrierHistory.lean` L40-L45](../../Core/Sync/ClusterBarrierHistory.lean#L40-L45)

<a id="c-clusterbarrier-run"></a>
#### `ClusterBarrier.run`

*def*

Apply the records of a history in order, stopping at a blocked record or a fault.

[Lean source: `Core/Sync/ClusterBarrierHistory.lean` L80-L85](../../Core/Sync/ClusterBarrierHistory.lean#L80-L85)

<a id="c-clusterbarrier-arrivalof"></a>
#### `ClusterBarrier.ArrivalOf`

*def*

Event `e` is a lane of a collective arrival of the given kind that is recorded in phase
`phase`.

[Lean source: `Core/Sync/ClusterBarrierHistory.lean` L90-L97](../../Core/Sync/ClusterBarrierHistory.lean#L90-L97)

<a id="c-clusterbarrier-waitof"></a>
#### `ClusterBarrier.WaitOf`

*def*

Event `e` is a lane of a recorded wait whose thread's latest arrival was in phase `phase`.

[Lean source: `Core/Sync/ClusterBarrierHistory.lean` L99-L104](../../Core/Sync/ClusterBarrierHistory.lean#L99-L104)

<a id="c-clusterbarrier-synchronizes"></a>
#### `ClusterBarrier.Synchronizes`

*def*

Arrival `a` and wait `w` synchronize: `a` is a release arrival and `w` is a wait for its
phase. Only release arrivals publish memory through this rule; counter completion alone
is not a visibility edge.

[Lean source: `Core/Sync/ClusterBarrierHistory.lean` L106-L110](../../Core/Sync/ClusterBarrierHistory.lean#L106-L110)

<a id="c-clustersync"></a>
#### `ClusterSync`

*def*

Cluster barrier synchronization from `e` to `f`: a release arrival at or after `e` in `e`'s
thread synchronizes with a wait that precedes `f` in `f`'s thread (`Synchronizes`).

[Lean source: `Core/Sync/ClusterBarrierExecution.lean` L79-L85](../../Core/Sync/ClusterBarrierExecution.lean#L79-L85)

### Warp collectives

Instances of `bar.warp.sync`, `elect.sync`, `shfl.sync`, `vote.sync`, `redux.sync` and `match.sync`.

<a id="c-electmember"></a>
#### `electMember`

*def*

Lane `lane` is a member of the mask: it is a lane of the warp and its bit is set.

[Lean source: `Core/Sync/Elect.lean` L31-L32](../../Core/Sync/Elect.lean#L31-L32)

<a id="c-execution-elect"></a>
#### `Execution.Elect`

*def*

Event `e` is an election at source position `pc` with member mask `mask`, instance label
`inst` and returned leader `leader`.

[Lean source: `Core/Sync/Elect.lean` L105-L108](../../Core/Sync/Elect.lean#L105-L108)

<a id="c-execution-warpbar"></a>
#### `Execution.WarpBar`

*def*

Event `e` is a `bar.warp.sync` with member mask `mask` and instance label `inst`.

[Lean source: `Core/Sync/WarpBarrier.lean` L58-L60](../../Core/Sync/WarpBarrier.lean#L58-L60)

<a id="c-warpbarsync"></a>
#### `WarpBarSync`

*def*

Warp barrier synchronization from `e` to `f`: an event `i` at or after `e` and an event `j`
before `f` belong to one instance.

[Lean source: `Core/Sync/WarpBarrier.lean` L75-L79](../../Core/Sync/WarpBarrier.lean#L75-L79)

<a id="c-shflsource"></a>
#### `shflSource`

*def*

Source lane and validity of `shfl.sync` (PTX ISA, `shfl.sync` pseudo-code).

[Lean source: `Core/Sync/Shuffle.lean` L131-L144](../../Core/Sync/Shuffle.lean#L131-L144)

<a id="c-execution-shflk"></a>
#### `Execution.ShflK`

*def*

`e` is the `n`-th shuffle of its thread.

[Lean source: `Core/Sync/Shuffle.lean` L150-L153](../../Core/Sync/Shuffle.lean#L150-L153)

<a id="c-voteclass"></a>
#### `voteClass`

*def*

The `vote.sync` class (DEP-WARP-INSTANCE): a ballot or a mode vote contributes its member
mask, its mode (`.ballot` for a ballot) and its predicate.

[Lean source: `Core/Sync/Vote.lean` L134-L139](../../Core/Sync/Vote.lean#L134-L139)

<a id="c-maskinwarp"></a>
#### `maskInWarp`

*def*

Every lane named in member mask `m` is a thread of the warp of thread `g`.

[Lean source: `Core/Sync/WarpInstance.lean` L112-L113](../../Core/Sync/WarpInstance.lean#L112-L113)

<a id="c-execution-maskk"></a>
#### `Execution.MaskK`

*def*

`e` is an event of class `c` with member mask `m`, and the thread performed `n` events of
class `c` with mask `m` before it.

[Lean source: `Core/Sync/WarpInstance.lean` L128-L132](../../Core/Sync/WarpInstance.lean#L128-L132)

<a id="c-maskinstance"></a>
#### `MaskInstance`

*def*

The instance of the `n`-th events of class `c` with member mask `m` in the warp of thread `g`,
with qualifiers `q`: `part lane` is the input of a lane of the mask that takes part, and none for
a lane of the mask that exited before its `n`-th event and for a lane outside the mask.

[Lean source: `Core/Sync/WarpInstance.lean` L143-L153](../../Core/Sync/WarpInstance.lean#L143-L153)

<a id="c-maskwait"></a>
#### `MaskWait`

*def*

The waiting dependency of an instance of class `c` (DEP-WARP-INSTANCE): `f` is the `n`-th
event of class `c` with member mask `m` and qualifiers `q` of its thread, and `e`, of the same
warp, is the `n`-th such event of its thread with the same qualifiers, or the exit of a lane of the
mask that exited before its `n`-th such event. The return of `f` waits for `e`.

[Lean source: `Core/Sync/WarpInstance.lean` L173-L180](../../Core/Sync/WarpInstance.lean#L173-L180)

<a id="c-voteresult"></a>
#### `voteResult`

*def*

The predicate a mode vote returns, from the predicates of the lanes that take part.

[Lean source: `Core/Sync/Vote.lean` L141-L148](../../Core/Sync/Vote.lean#L141-L148)

<a id="c-reduxresult"></a>
#### `reduxResult`

*def*

The result of a reduction over the sources `vs`, in lane order.

[Lean source: `Core/Sync/Redux.lean` L104-L107](../../Core/Sync/Redux.lean#L104-L107)

<a id="c-matchmask"></a>
#### `matchMask`

*def*

The mask a match returns to a lane with operand `a`, from the operands of the lanes that take
part.

[Lean source: `Core/Sync/Match.lean` L110-L114](../../Core/Sync/Match.lean#L110-L114)

### Warp-uniform control flow

The records of a thread's steps and the order that decides which executions may coincide.

<a id="c-visit"></a>
#### `Visit`

*structure*

The record of one step of a thread.

- `pc`: The position of the instruction the step executes.
- `guard`: The guard's value, for a guarded instruction that requires a uniform guard.
- `ev`: The event the step performs (`none` for a local step).
- `index`: The index a `brx.idx.uni` reads, when it can be read.

[Lean source: `Core/Sync/WarpUniform.lean` L228-L237](../../Core/Sync/WarpUniform.lean#L228-L237)

<a id="c-walk"></a>
#### `Walk`

*inductive*

From `t`, the thread performs exactly the events `es` in the steps recorded in `vs`; it
may stop at any state.

- `stop`
- `tau`
- `ev`
- `last`

[Lean source: `Core/Sync/WarpUniform.lean` L268-L278](../../Core/Sync/WarpUniform.lean#L268-L278)

<a id="c-depbefore"></a>
#### `DepBefore`

*def*

Thread event `e` precedes thread event `f` in the execution-dependency order: from the issue
of `e` to the issue of `f` (EXT-DEPENDENCY-ORDER), used only by this rule.

[Lean source: `Core/Sync/WarpUniform.lean` L295-L298](../../Core/Sync/WarpUniform.lean#L295-L298)

<a id="c-sameuniformgroup"></a>
#### `SameUniformGroup`

*def*

Threads `g` and `h` belong to one group of scope `s`.

[Lean source: `Core/Sync/WarpUniform.lean` L336-L339](../../Core/Sync/WarpUniform.lean#L336-L339)

<a id="c-warpdivergent"></a>
#### `WarpDivergent`

*def*

Two threads of one warp, or of one warpgroup for `setmaxnreg`, execute a guarded instruction
that requires a uniform guard, or a `brx.idx.uni`, in two executions that the
execution-dependency order does not order (they may coincide), and evaluate the guard differently
or read different indices (`Visit.Disagree`), outside the pairs a kernel assumption exempts
(`PollAgreeExempt`).

[Lean source: `Core/Sync/WarpUniform.lean` L341-L352](../../Core/Sync/WarpUniform.lean#L341-L352)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### What a barrier or collective instruction does

The event a thread produces for each instruction, and how a barrier object changes.

<a id="thread-bar"></a>
#### barrier arrival (`THREAD-BAR`)

*Rule* · [Lean comment: `Core/Sync/Barrier.lean` L23-L48](../../Core/Sync/Barrier.lean#L23-L48)

`bar.sync` and `bar.arrive` produce an arrival at one of the sixteen CTA barrier resources, with an optional participant count. The barrier number must be below 16 and an explicit count must be a multiple of 32, nonzero for `bar.arrive`; any other operand is a fault. A count equal to the CTA size, or zero on `bar.sync`, means every thread of the CTA.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`barTmpl`](../../Core/Sync/Barrier.lean#L77-L93)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1 (bar, barrier): "Source operand a specifies a logical barrier resource as an immediate
    constant or register with value 0 through 15 ."
- §9.7.15.1 (bar, barrier): "Note that a non-zero thread count is required for barrier{.cta}.arrive
    ."
- EXT-BAR-ZERO-COUNT

**Applies:** bar.sync with omitted or explicit participant count; bar.arrive with its participant count

**Premises:** Barrier ID is below 16; an explicit count is a multiple of 32, and nonzero for `bar.arrive`.

**Effect:** Event production; completion is decided by the named resource history. The zero-count reading is EXT-BAR-ZERO-COUNT. A zero count of `bar.arrive` is a `badBarrier` fault, as is any other operand outside these ranges.

</details>

<a id="ext-bar-zero-count"></a>
##### `bar.sync b, 0` means every thread of the CTA (`EXT-BAR-ZERO-COUNT`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/Barrier.lean` L50-L74](../../Core/Sync/Barrier.lean#L50-L74)

An explicit participant count of zero on `bar.sync` is read as every thread of the CTA, the same as an omitted count. A count equal to the CTA size has the same meaning.

Source:

- - §9.7.15.1: "If no thread count is specified, all threads in the CTA participate in the barrier" - §9.7.15.1: "When specifying a thread count, the value must be a multiple of the warp size" - §9.7.15.1: "Note that a non-zero thread count is required for barrier{.cta}.arrive" - §9.7.15.1: "Depending on operand b , either specified number of threads (in multiple of warp size) or all threads in the CTA participate in barrier{.cta} instruction." - implementation cross-check: ptxas 13.2.51 targeting sm_100a emits identical SASS for `bar.sync 0, 0` and `bar.sync 0`

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text requires a nonzero count only for `bar.arrive` and says nothing about the meaning of an explicit zero on `bar.sync`; zero is a multiple of the warp size, so the count may be read as zero participating threads (a barrier that no thread completes) as well as all threads.

**Effect:** A program using `bar.sync b, 0` is accepted with the whole-CTA meaning; if the hardware meaning differed, that program's synchronization would be wrong. Disclosed by every kernel whose statement names `Op.barSyncN`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm.

</details>

<a id="obj-cta-barrier-state"></a>
#### named CTA barrier resources and generations (`OBJ-CTA-BARRIER-STATE`)

*Rule* · [Lean comment: `Core/Sync/CtaBarrierObject.lean` L11-L46](../../Core/Sync/CtaBarrierObject.lean#L11-L46)

Each of the sixteen barrier resources of a CTA counts the distinct warps that arrive in its current generation. The generation completes when the requested number of warps has arrived, or when every warp that still has a live thread has arrived, and the resource then starts a new generation. A warp that arrives twice in one generation, or an arrival whose count differs from the count of the open generation, is a fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`CtaBarrier.Slot`](../../Core/Sync/CtaBarrierObject.lean#L49-L59) ([concept](#c-ctabarrier-slot)), [`CtaBarrier.State`](../../Core/Sync/CtaBarrierObject.lean#L61-L66) ([concept](#c-ctabarrier-state)), [`CtaBarrier.Error`](../../Core/Sync/CtaBarrierObject.lean#L68-L71) ([concept](#c-ctabarrier-error)), [`CtaBarrier.Error.isFault`](../../Core/Sync/CtaBarrierObject.lean#L73-L78), [`CtaBarrier.warps`](../../Core/Sync/CtaBarrierObject.lean#L80-L80), [`CtaBarrier.target`](../../Core/Sync/CtaBarrierObject.lean#L82-L87), [`CtaBarrier.warpLive`](../../Core/Sync/CtaBarrierObject.lean#L89-L91), [`CtaBarrier.allArrived`](../../Core/Sync/CtaBarrierObject.lean#L98-L100), [`CtaBarrier.complete`](../../Core/Sync/CtaBarrierObject.lean#L107-L112), [`CtaBarrier.settle`](../../Core/Sync/CtaBarrierObject.lean#L114-L116), [`CtaBarrier.arrive`](../../Core/Sync/CtaBarrierObject.lean#L118-L131) ([concept](#c-ctabarrier-arrive)), [`CtaBarrier.exitThread`](../../Core/Sync/CtaBarrierObject.lean#L133-L137) ([concept](#c-ctabarrier-exitthread))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1 (named resources, warp arrivals, counts, reset)
- §9.7.14.7 (exit)

**Applies:** The sixteen CTA barrier resources; sync/arrive completion, without reductions

**Premises:** An arrival represents all non-exited lanes of one warp reaching a barrier with matching operands. Thread/event matching and aligned-instruction requirements are checked separately.

**Effect:** Object-local resource transitions; faults are reported by ERR-CTA-BARRIER (`CtaBarFault`), and the executions are not removed. The bank is local to one CTA. An explicit count counts warp slots, including the slots of exited lanes in an arriving warp. An omitted or zero sync count waits for all non-exited warps. The instruction layer must reject zero for `bar.arrive`, which requires a nonzero operand. The actual arrivals determine the participating warps. A sync return must be linked to completion of its recorded generation by the execution layer. OBJ-CTA-BARRIER-SYNC uses checked source-event histories built from these resource operations.

</details>

<a id="obj-cluster-barrier-state"></a>
#### cluster arrival, completion and observation (`OBJ-CLUSTER-BARRIER-STATE`)

*Rule* · [Lean comment: `Core/Sync/ClusterBarrierObject.lean` L11-L51](../../Core/Sync/ClusterBarrierObject.lean#L11-L51)

A cluster barrier completes a phase when every non-exited thread of the cluster has arrived in it, and it then starts the next phase. A wait returns once the phase of the waiting thread's own latest arrival has completed, and it stays blocked for a thread that has not arrived. A thread that arrives a second time before its phase has completed is a fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`ClusterBarrier.State`](../../Core/Sync/ClusterBarrierObject.lean#L91-L100) ([concept](#c-clusterbarrier-state)), [`ClusterBarrier.Action`](../../Core/Sync/ClusterBarrierObject.lean#L102-L108) ([concept](#c-clusterbarrier-action)), [`ClusterBarrier.Error`](../../Core/Sync/ClusterBarrierObject.lean#L110-L112), [`ClusterBarrier.Error.isFault`](../../Core/Sync/ClusterBarrierObject.lean#L114-L118), [`ClusterBarrier.Outcome`](../../Core/Sync/ClusterBarrierObject.lean#L120-L124) ([concept](#c-clusterbarrier-outcome)), [`ClusterBarrier.finish`](../../Core/Sync/ClusterBarrierObject.lean#L126-L130), [`ClusterBarrier.perform`](../../Core/Sync/ClusterBarrierObject.lean#L132-L146) ([concept](#c-clusterbarrier-perform))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.3 (barrier.cluster)
- §9.7.15.3 (barrier.cluster): "barrier.cluster.wait instruction causes the executing thread to wait
    for all non-exited threads of the cluster to perform barrier.cluster.arrive ."
- §9.7.15.3 (barrier.cluster): "When all non-exited threads in the cluster have executed
    barrier.cluster.arrive , the barrier completes and is automatically reinitialized. After using
    barrier.cluster.wait to detect completion of the barrier, a thread may immediately arrive at the
    barrier once again. Each thread must arrive at the barrier only once before the barrier
    completes."
- §9.7.14.7 (exit)
- EXT-CLUSTER-WAIT-PHASE

**Applies:** One cluster's barrier, with an arbitrary number of threads and unbounded generations

**Premises:** The execution layer separately enforces the warp rendezvous required by both instructions.

**Effect:** Object transitions only; the fault is reported by ERR-CLUSTER-BARRIER (`ClusterFault`), and the execution is not removed. OBJ-CLUSTER-BARRIER-SYNC uses checked source-event histories built from these resource operations.

</details>

<a id="ext-cluster-wait-phase"></a>
##### a cluster wait waits for the phase of its thread's latest arrival (`EXT-CLUSTER-WAIT-PHASE`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/ClusterBarrierObject.lean` L53-L88](../../Core/Sync/ClusterBarrierObject.lean#L53-L88)

A `barrier.cluster.wait` waits for the completion of the phase in which the executing thread most recently arrived. It returns once that phase has completed, even when other threads have already arrived in the next phase, and it returns every time it is executed for that arrival. A wait of a thread that has not arrived stays blocked.

Source:

- - §9.7.15.3: "barrier.cluster.wait instruction causes the executing thread to wait for all non-exited threads of the cluster to perform barrier.cluster.arrive ." - §9.7.15.3: "When all non-exited threads in the cluster have executed barrier.cluster.arrive , the barrier completes and is automatically reinitialized. After using barrier.cluster.wait to detect completion of the barrier, a thread may immediately arrive at the barrier once again. Each thread must arrive at the barrier only once before the barrier completes." - §9.7.15.3: "The barrier.cluster.wait instruction guarantees that when it completes the execution, memory accesses (except asynchronous operations) requested, in program order, prior to the preceding barrier.cluster.arrive by all threads in the cluster are complete and visible to the executing thread."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text says the wait is for "all non-exited threads of the cluster to perform barrier.cluster.arrive", without saying which arrival of a reinitialized barrier: the current phase of the barrier, the phase after the executing thread's arrival, or the phase of the executing thread's "preceding barrier.cluster.arrive" (the phrase of the memory guarantee). The model takes the last, which also fixes what a second wait for one arrival, and a wait while other threads have arrived in the next phase, return. A wait read as waiting for the barrier's current phase would block in those two cases. If it does not hold, i.e. the hardware wait is for a different phase than the executing thread's most recent arrive, the model can accept a program that hangs, and the ordering edges it gives come from the wrong phase.

**Evidence:** Hardware probe on B200, driver 595.58.03, CUDA 13.2.51: a second `barrier.cluster.wait` after one arrive returns, immediately and after a delay; SASS keeps both `UCGABAR_WAIT`.

**Effect:** Disclosed by every kernel whose statement names `ClusterOp.wait`: FlashAttn4Fwd, Fp16Gemm8192.

</details>

<a id="thread-warp-bar"></a>
#### warp barrier template (`THREAD-WARP-BAR`)

*Rule* · [Lean comment: `Core/Sync/WarpBarrier.lean` L11-L26](../../Core/Sync/WarpBarrier.lean#L11-L26)

`bar.warp.sync` produces a collective event that retains its member mask. The executing lane must be named in the mask, and otherwise the instruction is a barrier fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`warpBarTmpl`](../../Core/Sync/WarpBarrier.lean#L28-L32)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.2

**Applies:** bar.warp.sync on sm_70 and later

**Premises:** The executing lane belongs to the 32-bit member mask.

**Effect:** Returns are constrained by DEP-WARP-BARRIER; this template alone grants no completion.

</details>

<a id="thread-elect"></a>
#### leader election template (`THREAD-ELECT`)

*Rule* · [Lean comment: `Core/Sync/Elect.lean` L12-L29](../../Core/Sync/Elect.lean#L12-L29)

`elect.sync` produces an election event for the executing lane, which must be named in the 32-bit member mask. The predicate result is true exactly in the elected leader lane, and the optional destination receives the lane number of the leader.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`electMember`](../../Core/Sync/Elect.lean#L31-L32) ([concept](#c-electmember)), [`electTmpl`](../../Core/Sync/Elect.lean#L36-L49)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.15 (elect.sync)

**Applies:** 32-bit member masks, a predicate destination and optional lane-ID destination

**Premises:** The executing lane is named in the mask and operand reads succeed.

**Effect:** Event template. Other lanes and deterministic choice are constrained by DEP-WARP-ELECT, not assumed from the member mask alone.

</details>

<a id="thread-shfl"></a>
#### warp shuffle (`THREAD-SHFL`)

*Rule* · [Lean comment: `Core/Sync/Shuffle.lean` L22-L39](../../Core/Sync/Shuffle.lean#L22-L39)

`shfl.sync` in any mode on a 32-bit value, with the full member mask in a CTA whose size is a multiple of 32, produces a shuffle event with the lane's operands. The received value is determined by DEP-WARP-SHUFFLE. Other masks have no rule, and an operand of another size is a type fault.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`shflTmpl`](../../Core/Sync/Shuffle.lean#L42-L55)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.6 (shfl.sync)

**Applies:** Full-mask `shfl.sync.{up,down,bfly,idx}.b32`

**Premises:** The CTA size is a multiple of 32, the member mask is full, and operands pass type checks.

**Effect:** Event production.

</details>

<a id="thread-vote"></a>
#### warp vote (`THREAD-VOTE`)

*Rule* · [Lean comment: `Core/Sync/Vote.lean` L22-L54](../../Core/Sync/Vote.lean#L22-L54)

`vote.sync.ballot.b32` with the full member mask in a CTA whose size is a multiple of 32 produces a ballot event with the lane's predicate, complemented when requested, and the ballot is written to the destination as a 32-bit integer. `vote.sync` with mode `.all`, `.any` or `.uni` produces a vote event with the mode, the member mask and the lane's predicate, complemented when requested, and the predicate received is written to the destination. The behaviour is undefined when the executing lane is not named in the member mask.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`voteTmpl`](../../Core/Sync/Vote.lean#L57-L66), [`voteModeTmpl`](../../Core/Sync/Vote.lean#L68-L78)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.10 (vote.sync): "Operand a is a predicate register."
- §9.7.15.10 (vote.sync): "In the ballot form, the destination operand d is a .b32 register."
- §9.7.15.10 (vote.sync): "The destination operand d is a predicate register and its value is the
    same across all threads in membermask ."
- §9.7.15.10 (vote.sync): "The behavior of vote.sync is undefined if the executing thread is not in
    the membermask ."

**Applies:** `vote.sync.ballot.b32` with the full member mask; `vote.sync.{all,any,uni}.pred`

**Premises:** For the ballot, the CTA size is a multiple of 32 and the member mask is full. For a mode, the executing lane is named in the member mask and every lane named in it is a thread of the warp. The source is a predicate.

**Effect:** Event production; a mode form whose executing lane is outside the member mask is a `badValue` fault. Other masks of the ballot have no rule (`noRule`, as for `shfl.sync`): every lane of the warp is then in the member mask, so the undefined case of an executing thread outside the mask cannot arise. A mode form with a member mask that names a lane with no thread (the last warp of a CTA whose size is not a multiple of 32) has no rule (`noRule`): the text does not say whether such a lane counts as exited.

</details>

<a id="thread-redux"></a>
#### integer warp reduction (`THREAD-REDUX`)

*Rule* · [Lean comment: `Core/Sync/Redux.lean` L22-L48](../../Core/Sync/Redux.lean#L22-L48)

An integer `redux.sync` produces a reduction event with its operation, its member mask and the lane's 32-bit source, and the result received is written to the destination as a 32-bit integer. The behaviour is undefined when the executing lane is not named in the member mask.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`reduxTmpl`](../../Core/Sync/Redux.lean#L51-L62)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.13 (redux.sync): "redux.sync performs a reduction operation .op of the 32 bit source
    register src across all non-exited threads in the membermask ."
- §9.7.15.13 (redux.sync): "The result of the reduction operation is written to the 32 bit
    destination register dst ."
- §9.7.15.13 (redux.sync): "The behavior of redux.sync is undefined if the executing thread is not
    in the membermask ."

**Applies:** `redux.sync.{add,min,max}.{u32,s32}` and `redux.sync.{and,or,xor}.b32`

**Premises:** The executing lane is named in the member mask, every lane named in it is a thread of the warp, and the operands can be read.

**Effect:** Event production; an executing lane outside the member mask is a `badValue` fault. A member mask that names a lane with no thread (the last warp of a CTA whose size is not a multiple of 32) has no rule (`noRule`): the text does not say whether such a lane counts as exited. The `.f32` forms have no rule (`WarpInstr.rule`).

</details>

<a id="thread-match"></a>
#### warp match (`THREAD-MATCH`)

*Rule* · [Lean comment: `Core/Sync/Match.lean` L22-L49](../../Core/Sync/Match.lean#L22-L49)

`match.sync` produces a match event with its mode, its type, its member mask and the lane's operand of 32 or 64 bits. The mask received is written to the 32-bit destination, and for `.all` the optional predicate destination receives whether the operands of the instance are all equal; a sink destination is not written. The behaviour is undefined when the executing lane is not named in the member mask.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`matchTmpl`](../../Core/Sync/Match.lean#L52-L69)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.11 (match.sync): "Operand a has instruction type and d has .b32 type."
- §9.7.15.11 (match.sync): "The sink symbol ‘_’ may be used in place of any one of the destination
    operands."
- §9.7.15.11 (match.sync): "The behavior of match.sync is undefined if the executing thread is not
    in the membermask ."

**Applies:** `match.any.sync.{b32,b64}` and `match.all.sync.{b32,b64}`, with or without the predicate destination

**Premises:** The executing lane is named in the member mask, every lane named in it is a thread of the warp, and the operands can be read.

**Effect:** Event production; an executing lane outside the member mask is a `badValue` fault. A member mask that names a lane with no thread (the last warp of a CTA whose size is not a multiple of 32) has no rule (`noRule`): the text does not say whether such a lane counts as exited.

</details>

<a id="thread-activemask"></a>
#### active-thread query (`THREAD-ACTIVEMASK`)

*Rule* · [Lean comment: `Core/Sync/ActiveMask.lean` L21-L39](../../Core/Sync/ActiveMask.lean#L21-L39)

`activemask` produces an event that returns a 32-bit mask, which is written to the destination as a 32-bit integer.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`activemaskTmpl`](../../Core/Sync/ActiveMask.lean#L42-L44)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.12 (activemask): "activemask queries predicated-on active threads from the executing warp
    and sets the destination d with 32-bit integer mask where bit position in the mask corresponds
    to the thread’s laneid ."
- §9.7.15.12 (activemask): "Destination d is a 32-bit destination register."

**Applies:** `activemask.b32`

**Effect:** Event production; the mask is constrained by DEP-WARP-ACTIVEMASK.

</details>

<a id="thread-matrix"></a>
#### matrix loads, stores and the register transpose (`THREAD-MATRIX`)

*Rule* · [Lean comment: `Core/Sync/Matrix.lean` L22-L78](../../Core/Sync/Matrix.lean#L22-L78)

In a CTA whose size is a multiple of 32, `ldmatrix` makes each thread that supplies a row address read the 16 bytes of its row, as one weak read, and then take part in the warp's instance with those bytes; it writes the bytes it receives to its destination registers. `stmatrix` makes each thread take part with the bytes of its source registers and then write the 16 bytes it receives to the row whose address it supplies. `movmatrix` takes part with its source register and writes what it receives to its destination. A row address must lie in the thread's own `.shared::cta` window and be aligned to 16 bytes.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`byteValue`](../../Core/Sync/Matrix.lean#L81-L82), [`valueByte`](../../Core/Sync/Matrix.lean#L84-L87), [`matrixRowLoc`](../../Core/Sync/Matrix.lean#L89-L97), [`regBytes`](../../Core/Sync/Matrix.lean#L99-L105), [`afterMatrix`](../../Core/Sync/Matrix.lean#L107-L116), [`matrixMoveTmpl`](../../Core/Sync/Matrix.lean#L118-L146), [`matrixTmpl`](../../Core/Sync/Matrix.lean#L182-L197)

<details>
<summary>Details for reviewers</summary>

- §9.7.16.5.15: "Collectively load one or more matrices across all threads in a warp from the
    location indicated by the address operand p , from .shared state space into destination register
    r ."
- §9.7.16.5.15: "If the generic address doesn’t fall in .shared state space, then the behavior is
    undefined."
- §9.7.16.5.15: "Each address corresponds to the start of a matrix row."
- §9.7.16.5.15: "When reading 8x8 matrices, a group of four consecutive threads loads 16 bytes. The
    matrix addresses must be naturally aligned accordingly."
- §9.7.16.5.15: "For .b6x16_p32 format source data is 16 unsigned 6-bit elements with 32 bits
    padding."
- §9.7.16.5.15: "For .b4x16_p64 format source data is 16 unsigned 4-bit elements with 64 bits
    padding."
- §9.7.16.5.15: "The ldmatrix instruction is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.16.5.16: "When storing 8x8 matrices, a group of four consecutive threads stores 16 bytes."
- §9.7.16.5.16: "The stmatrix instruction is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.16.5.17: "Operands a and d are 32-bit registers containing fragments of the input matrix and
    the resulting matrix respectively."
- EXT-MATRIX-FIGURES

**Applies:** The forms whose rule is THREAD-MATRIX (`MatrixInstr.rule`)

**Premises:** The CTA size is a multiple of 32, the row address is in the thread's own `.shared::cta` window and aligned to 16 bytes, and the source registers hold 32-bit values.

**Effect:** Event production: a read or write of the thread's row (THREAD-ACCESS events) and a matrix event (DEP-WARP-MATRIX). The rows of matrix `k` are supplied by threads `rows k` to `rows (k + 1) - 1` (`MatrixMove.rows`); the other threads supply no address, read no row and take part with no bytes. Every row of a supported form is 16 bytes: eight 16-bit elements, sixteen 8-bit elements, or sixteen 6-bit or 4-bit elements with their padding. Between the read and the matrix event of `ldmatrix`, and between the matrix event and the write of `stmatrix`, the thread keeps the row's bytes in `TState.acc`, each as the one-byte slice of its value (`byteValue`), at sub-step 1. A row with an unknown byte makes the reading thread fault (`uninitialized`): every byte of a row of a form with known values reaches some register, where the load would fault (THREAD-BYTES). A received list that does not rebuild into the destination registers faults the same way. A generic address must be a pointer into the thread's own shared memory (THREAD-ADDR); any other address is `badValue` (stricter for a `.shared::cluster` address of the own CTA, which the text does not mention), and a row address that is not a multiple of 16 is `misaligned`. In a CTA whose size is not a multiple of 32 the instructions have no rule, as for `shfl.sync`: the text does not say what the missing lanes of the last warp supply.

</details>

<a id="thread-mma-sync"></a>
#### warp-level matrix multiply-accumulate (`THREAD-MMA-SYNC`)

*Rule* · [Lean comment: `Core/Sync/Matrix.lean` L148-L169](../../Core/Sync/Matrix.lean#L148-L169)

In a CTA whose size is a multiple of 32, `mma` and `mma.sp` make each thread take part in the warp's instance with the bytes of its A, B and C registers and, for `mma.sp`, of its metadata register, and write the bytes it receives to its D registers.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`mmaOwn`](../../Core/Sync/Matrix.lean#L172-L180)

<details>
<summary>Details for reviewers</summary>

- §9.7.16.5.14: "Operands a and b represent two multiplicand matrices A and B, while c and d
    represent the accumulator and destination matrices, distributed across the threads in warp."
- §9.7.16.6.3: "Operands e and f represent sparsity metadata and sparsity selector respectively."

**Applies:** The forms whose rule is THREAD-MMA-SYNC (`MatrixInstr.rule`)

**Premises:** The CTA size is a multiple of 32 and the source registers hold values of their widths.

**Effect:** Event production: a matrix event (DEP-WARP-MATRIX) whose received bytes DEP-WARP-MMA gives. A and B registers are 64 bits wide for `.f64` and 32 bits otherwise, C and D registers likewise for their own types, and the metadata register is 32 bits (`MmaSpec.regBits`).

</details>

### Cluster membership

Which CTAs form a cluster and what a rank denotes.

<a id="prog-cluster"></a>
#### cluster membership, coordinates and logical peer addresses (`PROG-CLUSTER`)

*Rule* · [Lean comment: `Core/Sync/Cluster.lean` L11-L78](../../Core/Sync/Cluster.lean#L11-L78)

The grid of a cluster launch consists of whole clusters, each of the regular or of the preferred cluster shape. The model numbers the CTAs so that the CTAs of one cluster are consecutive, ordered by their rank in the cluster. The rank of a CTA selects the CTA with that position in the same cluster. A CTA's `%cluster_nctaid`, `%cluster_ctaid`, `%cluster_ctarank`, `%cluster_nctarank`, `%clusterid`, `%nclusterid` and `%ctaid` are those of its own cluster (EXT-CLUSTER-RANK). Mapping a shared location to a peer rank keeps its byte offset and changes its owning CTA to the peer.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Launch.locate`](../../Core/Sync/Cluster.lean#L116-L123), [`Launch.clusterOfCta`](../../Core/Sync/Cluster.lean#L125-L126) ([concept](#c-launch-clusterofcta)), [`Launch.rankOfCta`](../../Core/Sync/Cluster.lean#L128-L129) ([concept](#c-launch-rankofcta)), [`Launch.clusterSizeAt`](../../Core/Sync/Cluster.lean#L131-L132), [`Launch.clusterStart`](../../Core/Sync/Cluster.lean#L134-L137), [`Launch.placeOf`](../../Core/Sync/Cluster.lean#L139-L140), [`Launch.clusterSizeOf`](../../Core/Sync/Cluster.lean#L142-L143), [`Launch.clusterNctaidOf`](../../Core/Sync/Cluster.lean#L145-L146), [`Launch.clusterCtaidOf`](../../Core/Sync/Cluster.lean#L148-L151), [`Launch.clusteridOf`](../../Core/Sync/Cluster.lean#L153-L154), [`Launch.nclusteridOf`](../../Core/Sync/Cluster.lean#L156-L157), [`Launch.ctaidOf`](../../Core/Sync/Cluster.lean#L159-L164), [`Launch.clusterGridValid`](../../Core/Sync/Cluster.lean#L166-L190), [`Launch.oneDimLaunch`](../../Core/Sync/Cluster.lean#L196-L199) ([concept](#c-launch-onedimlaunch)), [`Launch.locate_regular`](../../Core/Sync/Cluster.lean#L201-L218), [`Launch.oneDim_clusterPlaces`](../../Core/Sync/Cluster.lean#L220-L227), [`Launch.oneDim_clusterSizeAt`](../../Core/Sync/Cluster.lean#L229-L232), [`Launch.oneDim_clusterOfCta`](../../Core/Sync/Cluster.lean#L234-L237), [`Launch.oneDim_rankOfCta`](../../Core/Sync/Cluster.lean#L239-L242), [`Launch.oneDim_clusterStart`](../../Core/Sync/Cluster.lean#L244-L249), [`Launch.oneDim_clusterSizeOf`](../../Core/Sync/Cluster.lean#L251-L253), [`Launch.oneDim_clusterNctaidOf`](../../Core/Sync/Cluster.lean#L255-L258), [`Launch.oneDim_nclusteridOf`](../../Core/Sync/Cluster.lean#L260-L263), [`Launch.oneDim_clusterCtaidOf`](../../Core/Sync/Cluster.lean#L265-L272), [`Launch.oneDim_clusteridOf`](../../Core/Sync/Cluster.lean#L274-L277), [`Launch.oneDim_ctaidOf`](../../Core/Sync/Cluster.lean#L279-L285), [`Launch.oneDimLaunch_clusterGridValid`](../../Core/Sync/Cluster.lean#L287-L313), [`Launch.clusterGridValid_start`](../../Core/Sync/Cluster.lean#L315-L317), [`Launch.peerCta`](../../Core/Sync/Cluster.lean#L319-L325) ([concept](#c-launch-peercta)), [`Launch.mapShared`](../../Core/Sync/Cluster.lean#L327-L332) ([concept](#c-launch-mapshared)), [`SameCluster`](../../Core/Sync/Cluster.lean#L334-L337) ([concept](#c-samecluster))

<details>
<summary>Details for reviewers</summary>

- §2.2.2: "Each CTA in a cluster has a unique CTA identifier within its cluster ( cluster_ctaid ).
    Each cluster of CTAs has 1D, 2D or 3D shape specified by the parameter cluster_nctaid . Each CTA
    in the cluster also has a unique CTA identifier ( cluster_ctarank ) across all dimensions. The
    total number of CTAs across all the dimensions in the cluster is specified by cluster_nctarank
    ."
- §2.2.3: "Each cluster has a unique cluster identifier ( clusterid ) within a grid of clusters."
- §10.12: "Each cluster in a grid has a unique identifier."
- §10.14: "It is guaranteed that: 0 <= %cluster_ctaid.x < %cluster_nctaid.x"
- §10.16: "It is guaranteed that: 0 <= %cluster_ctarank < %cluster_nctarank"
- §9.7.10.26 (mapa)
- EXT-CLUSTER-RANK
- EXT-PREFERRED-CLUSTER

**Applies:** Grids and clusters of up to three dimensions, with clusters of the regular or the preferred shape

**Premises:** A valid cluster launch tiles the grid with its clusters (`Launch.clusterGridValid`, CORRECT-LAUNCH); a target rank belongs to the issuer's cluster.

**Effect:** Launch topology, special-register values and the logical location mapping used by peer-memory operations. The launch places each cluster (`Launch.clusterPlaces`, PROG-LAUNCH): its origin `%ctaid`, its shape and the `%clusterid` and `%nclusterid` its threads read. The CTA number (PROG-LAUNCH) is the model's own name of a CTA, used for the ownership of shared memory, barriers and Tensor Memory; no register shows it. Cluster `k` has the CTA numbers from `Launch.clusterStart k`, one for each rank (`Launch.locate`, `Launch.clusterOfCta`, `Launch.rankOfCta`). Every rule that names the cluster of a CTA, its rank or the size of its cluster (cluster barriers, peer addresses, CTA pairs, multicast masks, cluster launch control) uses these functions, so it applies to the CTA's own cluster, of either shape. `Launch.clusterGridValid` states what a placement must satisfy (EXT-PREFERRED-CLUSTER): the counts are the products of the shapes, each cluster lies in the grid on the lattice of the regular shape, the clusters together have the grid's CTAs, no two CTAs have one `%ctaid`, and no two clusters one `%clusterid`.

</details>

<a id="ext-cluster-rank"></a>
##### cluster coordinates and rank (`EXT-CLUSTER-RANK`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/Cluster.lean` L80-L113](../../Core/Sync/Cluster.lean#L80-L113)

The model relates `%ctaid` to the cluster registers. In each dimension `d`, `%ctaid.d = origin.d + %cluster_ctaid.d` for the origin of the CTA's cluster. `%cluster_ctarank` is the linear index of `%cluster_ctaid` in the cluster's shape with `x` varying fastest: `%cluster_ctaid.x + %cluster_ctaid.y * %cluster_nctaid.x + %cluster_ctaid.z * %cluster_nctaid.x * %cluster_nctaid.y`. The rank is also the bit position of a `ctaMask` and the operand of `mapa`. When every cluster has the regular shape (`ClusterPlace.uniform`), `origin.d = %clusterid.d * %cluster_nctaid.d` and `%nclusterid.d = %nctaid.d / %cluster_nctaid.d`. In a one-dimensional launch with cluster size `s`, the CTA with `%ctaid.x` equal to `c` is in cluster `c / s` and has rank `c % s`; cluster `k` holds CTAs `k s` to `k s + s - 1`, and the grid is a multiple of `s`.

Source:

- - §2.2.2 and §2.2.3 (a cluster is a group of CTAs; the grid is a grid of clusters) - §10.12–§10.17 (`%clusterid`, `%cluster_ctaid`, `%cluster_nctarank`, `%cluster_ctarank`) - §10.12–§10.17: "It is guaranteed that: 0 <= %cluster_ctarank < %cluster_nctarank" - the production FP16 GEMM, which mixes peer ranks derived from `%ctaid` with `mapa` and `%cluster_ctarank`

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** §10.12–§10.17 give the ranges of the identifiers and say that each CTA of a cluster has a unique one; the text does not relate `%ctaid` to the cluster, the cluster identifier or the rank, and it does not say how the rank linearizes `%cluster_ctaid`, so these formulas are not in the ISA. The order with `x` fastest is the one §9.7.17.1 gives for the warp rank of a thread.

**Effect:** A program that derives a peer from `%ctaid` is judged with this mapping; if the hardware numbering differs, `mapa` targets and multicast masks denote other CTAs. Disclosed by every kernel whose statement names `SRegName.clusterid`, `SRegName.nclusterid`, `SRegName.clusterCtaid`, `SRegName.clusterNctaid`, `SRegName.clusterCtarank`, `SRegName.clusterNctarank`, `AddrInstr.mapa`, `Op.cluster`, `Op.clcTryCancel`, `SharedWindow.cluster`, `Op.mbarArrive (cluster := true)`, `Op.cpTensor (multicast ≠ none)` or `CtaGroup.two`: FlashAttn4Fwd, Fp16Gemm8192.

</details>

### Which executions are allowed

The recorded histories of barriers, the synchronization and blocking they give, and the agreement of the lanes of a collective.

<a id="obj-cta-barrier-history"></a>
#### actual arrivals identify barrier generations (`OBJ-CTA-BARRIER-HISTORY`)

*Rule* · [Lean comment: `Core/Sync/CtaBarrierHistory.lean` L10-L36](../../Core/Sync/CtaBarrierHistory.lean#L10-L36)

The history of a CTA's barrier resources lists their updates in order: the collective arrivals of whole warps and the exits of threads. The generation of an arrival is the generation of its resource just before that update, so it does not depend on how many barriers a thread has met earlier. A generation is released by the update that completes it.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`CtaBarrier.Record`](../../Core/Sync/CtaBarrierHistory.lean#L39-L44) ([concept](#c-ctabarrier-record)), [`CtaBarrier.Record.refs`](../../Core/Sync/CtaBarrierHistory.lean#L46-L49), [`CtaBarrier.Record.perform`](../../Core/Sync/CtaBarrierHistory.lean#L51-L62), [`CtaBarrier.run`](../../Core/Sync/CtaBarrierHistory.lean#L64-L67) ([concept](#c-ctabarrier-run)), [`CtaBarrier.At`](../../Core/Sync/CtaBarrierHistory.lean#L69-L71), [`CtaBarrier.GenerationOf`](../../Core/Sync/CtaBarrierHistory.lean#L73-L78) ([concept](#c-ctabarrier-generationof)), [`CtaBarrier.Released`](../../Core/Sync/CtaBarrierHistory.lean#L86-L89) ([concept](#c-ctabarrier-released)), [`CtaBarrier.CompletesAt`](../../Core/Sync/CtaBarrierHistory.lean#L80-L84)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1 (warp arrivals and resource reuse)
- §9.7.14.7 (exited threads)

**Applies:** One CTA's named barrier resources and exits

**Premises:** Each arrival records exactly the non-exited lanes of its warp; event references must separately match the source execution.

**Effect:** Associates actual source-event references with object generations and their release. The history orders resource updates. It does not order memory instructions or thread returns. A partial warp arrival may be present in a thread trace before there is a collective record; its barrier cannot return until its collective record and phase release exist. The execution adapter is responsible for reference provenance, uniqueness, source ordering, and the dependence of a collective arrival on every recorded lane.

</details>

<a id="obj-cta-barrier-sync"></a>
#### named-resource histories refer to source arrivals (`OBJ-CTA-BARRIER-SYNC`)

*Rule* · [Lean comment: `Core/Sync/CtaBarrierExecution.lean` L10-L60](../../Core/Sync/CtaBarrierExecution.lean#L10-L60)

A CTA barrier instance is a barrier number together with a generation of its resource. An arrival of either form (`bar.sync` or `bar.arrive`) in an instance orders the arriving thread's earlier accesses before the later accesses of every thread that has passed a `bar.sync` of the same instance. A `bar.sync` returns only after its generation has completed, and a `bar.arrive` returns once its warp's arrival is recorded. An arrival that the resource cannot perform is ERR-CTA-BARRIER.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`CtaBarSources`](../../Core/Sync/CtaBarrierExecution.lean#L63-L72), [`CtaBarHistoryOk`](../../Core/Sync/CtaBarrierExecution.lean#L74-L82), [`CtaBarArrivalK`](../../Core/Sync/CtaBarrierExecution.lean#L84-L90) ([concept](#c-ctabararrivalk)), [`CtaBarK`](../../Core/Sync/CtaBarrierExecution.lean#L92-L98) ([concept](#c-ctabark)), [`CtaBarDone`](../../Core/Sync/CtaBarrierExecution.lean#L100-L102) ([concept](#c-ctabardone)), [`CtaBarSync`](../../Core/Sync/CtaBarrierExecution.lean#L104-L109) ([concept](#c-ctabarsync))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier."
- §9.7.15.1: "barrier{.cta}.arrive does not cause executing thread to wait for threads of other
    participating warps."
- §9.7.15.1: "The barrier{.cta}.sync or barrier{.cta}.red or barrier{.cta}.arrive instruction
    guarantees that when the barrier completes, prior memory accesses requested by this thread are
    performed relative to all threads participating in the barrier. The barrier{.cta}.sync and
    barrier{.cta}.red instruction further guarantees that no new memory access is requested by this
    thread before the barrier completes."
- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count."
- §8.9.4: "A bar{.cta}.sync or bar{.cta}.red or bar{.cta}.arrive operation synchronizes with a
    bar{.cta}.sync or bar{.cta}.red operation executed on the same barrier."

**Applies:** CTA barrier arrival events of both forms (`bar.sync`, `bar.arrive`) with omitted or explicit participant counts

**Premises:** Resource histories contain unique source-event references and complete collective arrivals; source threads and operands match the recorded CTA-local operations.

**Effect:** Named barrier synchronization used by MEM-BASE-CAUSALITY (`CtaBarSync`), the history used by the needs of both forms (`KindNeeds`, DEP-ORDER), and the history that ERR-CTA-BARRIER checks for an arrival the resource cannot perform. The needs are: for each lane of the warp, its arrival in the warp's record or its exit recorded before it (both forms, the warp wait of the first quoted sentence); for `bar.sync`, also the release of its generation (`CtaBarDone`) and the records that the release counted. The direction is `reading` because the model takes a `bar.arrive` to be performed, with its warp's arrival recorded, when its warp's lanes have executed it.

</details>

<a id="obj-cluster-barrier-history"></a>
#### collective arrivals and completed waits (`OBJ-CLUSTER-BARRIER-HISTORY`)

*Rule* · [Lean comment: `Core/Sync/ClusterBarrierHistory.lean` L10-L37](../../Core/Sync/ClusterBarrierHistory.lean#L10-L37)

The history of a cluster barrier lists, in order, the collective arrivals and waits of whole warps and the exits of threads. An arrival uses the phase that is open when it is recorded, and a wait observes the phase of its thread's own preceding arrival. A release arrival synchronizes with a wait only when both are of the same phase. A lane that arrives twice before its phase completes is a fault, even if another lane of the same warp arrival completes the phase.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`ClusterBarrier.Record`](../../Core/Sync/ClusterBarrierHistory.lean#L40-L45) ([concept](#c-clusterbarrier-record)), [`ClusterBarrier.Record.refs`](../../Core/Sync/ClusterBarrierHistory.lean#L47-L49), [`ClusterBarrier.liveWarp`](../../Core/Sync/ClusterBarrierHistory.lean#L51-L60), [`ClusterBarrier.performAll`](../../Core/Sync/ClusterBarrierHistory.lean#L62-L66), [`ClusterBarrier.Record.perform`](../../Core/Sync/ClusterBarrierHistory.lean#L68-L78), [`ClusterBarrier.run`](../../Core/Sync/ClusterBarrierHistory.lean#L80-L85) ([concept](#c-clusterbarrier-run)), [`ClusterBarrier.At`](../../Core/Sync/ClusterBarrierHistory.lean#L87-L88), [`ClusterBarrier.ArrivalOf`](../../Core/Sync/ClusterBarrierHistory.lean#L90-L97) ([concept](#c-clusterbarrier-arrivalof)), [`ClusterBarrier.WaitOf`](../../Core/Sync/ClusterBarrierHistory.lean#L99-L104) ([concept](#c-clusterbarrier-waitof)), [`ClusterBarrier.Synchronizes`](../../Core/Sync/ClusterBarrierHistory.lean#L106-L110) ([concept](#c-clusterbarrier-synchronizes))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.3 (barrier.cluster)

**Applies:** The matched arrive/wait protocol of OBJ-CLUSTER-BARRIER-STATE, for arbitrary CTA and cluster sizes

**Premises:** Each collective record contains exactly the live lanes of one warp in one CTA. References, instruction qualifiers and per-thread order must separately match source events.

**Effect:** Source-reference associations used by OBJ-CLUSTER-BARRIER-SYNC. History order is barrier-object order. It is not a global order on memory. A blocked wait cannot be a completed record, and arrival and wait records both enforce warp rendezvous. The adapter must distinguish events before arrival from those between arrival and wait, and exclude asynchronous operations from this generic-proxy synchronization.

</details>

<a id="obj-cluster-barrier-sync"></a>
#### cluster synchronization and rendezvous (`OBJ-CLUSTER-BARRIER-SYNC`)

*Rule* · [Lean comment: `Core/Sync/ClusterBarrierExecution.lean` L11-L50](../../Core/Sync/ClusterBarrierExecution.lean#L11-L50)

A `barrier.cluster.arrive` returns once its whole warp has arrived, without waiting for the cluster, and a `barrier.cluster.wait` returns only when the phase of its own arrival has completed. A release arrival makes the thread's earlier generic accesses visible to the operations that follow the matched wait, and a relaxed arrival does not. An arrival or wait that the barrier cannot perform is ERR-CLUSTER-BARRIER, and ERR-ALIGNED-MISMATCH checks the `.aligned` qualifier.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`ClusterSources`](../../Core/Sync/ClusterBarrierExecution.lean#L53-L67), [`ClusterHistoryOk`](../../Core/Sync/ClusterBarrierExecution.lean#L69-L77), [`ClusterSync`](../../Core/Sync/ClusterBarrierExecution.lean#L79-L85) ([concept](#c-clustersync)), [`ClusterPoint`](../../Core/Sync/ClusterBarrierExecution.lean#L87-L90), [`isCluster`](../../Core/Sync/ClusterBarrierExecution.lean#L92-L94)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.3: "barrier.cluster.arrive instruction marks warps’ arrival at barrier without causing
    executing thread to wait for threads of other participating warps."
- §9.7.15.3: "barrier.cluster.wait instruction causes the executing thread to wait for all
    non-exited threads of the cluster to perform barrier.cluster.arrive ."
- §9.7.15.3: "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no
    memory ordering and visibility guarantees provided for the memory accesses performed prior to
    barrier.cluster.arrive ."
- §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation."

**Applies:** Matched cluster arrive/wait protocols, including release and relaxed arrival and aligned/unqualified forms

**Premises:** Object records have unique source references, correct cluster-local thread IDs and actual instruction operands. Both collectives contain all live warp lanes. A cluster's history has the size of that cluster (`Launch.clusterSizeAt`, PROG-CLUSTER), regular or preferred.

**Effect:** Constrains Consistent, contributes baseCausality (`ClusterSync`) and object-order edges (MEM-OBJECT-ORDER-CAUSALITY), gives the history the needs of both forms use (`KindNeeds`, DEP-ORDER: every lane of the warp in the same record or exited before it, and for a wait every arrival of its phase and every exit of the cluster recorded before its record), and gives the history that ERR-CLUSTER-BARRIER checks for an operation the barrier cannot perform. Aligned divergence and an aligned instruction skipped by an exited lane of its warp are ERR-ALIGNED-MISMATCH. Async effects have distinct references and receive no generic-memory edge here; accesses between arrival and wait are not published. Each history orders this barrier's operations only: arrival is recorded at collective issue, completed wait at return. A source trace may end at a pending collective without claiming that it returned.

</details>

<a id="dep-warp-barrier"></a>
#### warp rendezvous and memory ordering (`DEP-WARP-BARRIER`)

*Rule* · [Lean comment: `Core/Sync/WarpBarrier.lean` L34-L56](../../Core/Sync/WarpBarrier.lean#L34-L56)

Every lane named in the mask of a `bar.warp.sync` executes it with the same mask, once per instance, and no participant returns before all have arrived. The memory accesses that a participant performs before the barrier are ordered before the accesses that the participants perform after it.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Execution.WarpBar`](../../Core/Sync/WarpBarrier.lean#L58-L60) ([concept](#c-execution-warpbar)), [`WarpBarEdge`](../../Core/Sync/WarpBarrier.lean#L62-L64), [`WarpBarOk`](../../Core/Sync/WarpBarrier.lean#L66-L73), [`WarpBarSync`](../../Core/Sync/WarpBarrier.lean#L75-L79) ([concept](#c-warpbarsync))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.2

**Applies:** Dynamic bar.warp.sync instances on sm_70 and later, including partial masks

**Premises:** Matching labels identify a single rendezvous within one warp; every named lane participates once with the same mask.

**Effect:** `Consistent.warpBar` checks participation, the needs of the barrier (`KindNeeds`, DEP-ORDER) make every lane's arrival a witness of every return of the instance (execution layer), and baseCausality includes WarpBarSync (memory layer). Labels identify the participants of one rendezvous. Different source positions may participate.

</details>

<a id="dep-warp-elect"></a>
#### completed election collectives (`DEP-WARP-ELECT`)

*Rule* · [Lean comment: `Core/Sync/Elect.lean` L51-L78](../../Core/Sync/Elect.lean#L51-L78)

Every lane named in the member mask of an election executes the same `elect.sync` instruction with the same mask and receives the same leader, which is a lane of the mask. Repeated elections of one warp with equal masks return the same leader.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Execution.Elect`](../../Core/Sync/Elect.lean#L105-L108) ([concept](#c-execution-elect)), [`ElectOk`](../../Core/Sync/Elect.lean#L110-L123)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.15 (one leader, deterministic mask choice, mandatory sync)
- EXT-ELECT-SITE (one source instruction per instance)

**Applies:** Dynamic warp election instances, including partial masks and repeated calls

**Premises:** Events identify a member mask, instance label and returned leader. Labels are matching witnesses within a warp. They are not timestamps or global instruction ordinals.

**Effect:** `Consistent.elect` constrains returned results. The needs of an election (`KindNeeds`, DEP-ORDER) are the events of every lane of its mask with its label, so each participant's arrival is a witness of every return of that instance; this is execution-layer order only. A lane contributes at most once to an instance. Repeated elections return the same leader because §9.7.15.15 says that "the same leader thread is elected for the same membermask every time", and the member mask names lanes of the executing warp. An unfinished collective has no completed election event yet. `DependencyOk.acyclic` rules out mutually dependent returns. Every leader choice satisfying the instruction's contract is admitted; no lane (including lane zero) is singled out.

</details>

<a id="ext-elect-site"></a>
##### the lanes of one election execute one `elect.sync` instruction (`EXT-ELECT-SITE`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/Elect.lean` L80-L103](../../Core/Sync/Elect.lean#L80-L103)

An election instance consists of the lanes of the member mask that execute the same `elect.sync` instruction, at one source position. Lanes that wait at two different `elect.sync` instructions never form one instance.

Source:

- - §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to wait until all threads in the membermask execute the elect instruction before resuming execution."

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** "the elect instruction" does not say whether the other lanes must execute this instruction or any `elect.sync`; §9.7.15.2 states the other choice for `bar.warp.sync` ("have executed a bar.warp.sync with the same membermask value"), which WarpBarOk follows. The same-position reading matches ERR-NONUNIFORM-GUARD, whose collectives are executions of one position.

**Effect:** If the lanes of a mask wait at two different `elect.sync` instructions, the model forms no instance and they block, so that execution is not Complete and the kernel's progress theorem cannot be proved; in a kernel whose theorems are proved no such state is reachable, and the reading excludes none of its executions. Disclosed by every kernel whose statement names `WarpKind.elect`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.

</details>

<a id="dep-warp-shuffle"></a>
#### warp shuffle instances (`DEP-WARP-SHUFFLE`)

*Rule* · [Lean comment: `Core/Sync/Shuffle.lean` L57-L101](../../Core/Sync/Shuffle.lean#L57-L101)

The n-th shuffles of the lanes of a warp form one instance, and every lane of the warp either takes part in it with the same mode or has exited before reaching it. A lane receives the operand of its source lane, which the pseudo-code of the instruction computes from the lane number and the `b` and `c` operands, together with the validity predicate. The value received from a source lane that exited is unconstrained. A lane returns from an instance only after every lane of the warp has executed its shuffle of the instance or exited.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`shflSource`](../../Core/Sync/Shuffle.lean#L131-L144) ([concept](#c-shflsource)), [`Execution.ShflK`](../../Core/Sync/Shuffle.lean#L150-L153) ([concept](#c-execution-shflk)), [`ShflExited`](../../Core/Sync/Shuffle.lean#L158-L160), [`ShflOk`](../../Core/Sync/Shuffle.lean#L162-L173), [`shflClass`](../../Core/Sync/Shuffle.lean#L175-L179), [`maskK_shflClass`](../../Core/Sync/Shuffle.lean#L188-L200), [`maskExitK_shflClass`](../../Core/Sync/Shuffle.lean#L202-L210)

<details>
<summary>Details for reviewers</summary>

- §9.7.10.6 (shfl.sync): "wait until all non-exited threads corresponding to membermask have
    executed shfl.sync with the same qualifiers and same membermask value before resuming execution"
- §9.7.10.6 (shfl.sync): "results are undefined if a thread sources a register from an inactive
    thread or a thread that is not in membermask"
- §9.7.10.6 (shfl.sync): "case .up: j = lane - bval; pval = (j >= maxLane); break; case .down: j =
    lane + bval; pval = (j <= maxLane); break;"
- §9.7.10.6 (shfl.sync): "if (!pval) j = lane; // copy from own lane"
- EXT-SHFL-UP-INDEX

**Applies:** Full-member-mask shuffle instances

**Premises:** A shuffle event exists at a given ordinal.

**Effect:** Execution constraint in `Consistent.shfl` (the received values); the waiting dependency `MaskWait L shflClass` (DEP-WARP-INSTANCE) gives the needs of a shuffle in `KindNeeds` (DEP-ORDER), so a shuffle exists in a consistent execution only when every lane of the warp has executed its shuffle of the instance with the same mode or exited. The `n`-th shuffles of the lanes of a warp form one instance. A lane whose guard is false performs no shuffle event; an instance therefore never contains a predicated-off lane, and executions in which lanes that may execute one `shfl.sync` together evaluate its guard differently are unsafe (ERR-NONUNIFORM-GUARD), so no predicated-off lane is paired into a later instance. Lanes may reach it from different source positions (sm_70 and later), and their `b`, `c` operands are their own. A lane that exited before its `n`-th shuffle does not take part; a value read from such a source lane is unconstrained. The waiting dependency of an instance is the one of DEP-WARP-INSTANCE for the class `shflClass`, whose member mask is the full mask: the shuffle of every lane of the warp, and the exit of every lane that exited before its `n`-th shuffle, precede the return of each shuffle of the `n`-th instance. `ShflK` is the class ordinal `MaskK shflClass` with the full mask, which `maskK_shflClass` proves, so the value rule and the needs pair the same executions. `maskK_shflClass` and `maskExitK_shflClass` restate the class in terms of `ShflK` and the exits of `ShflExited`.

</details>

<a id="ext-shfl-up-index"></a>
##### the source lane of `shfl.sync.up` is an integer difference (`EXT-SHFL-UP-INDEX`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/Shuffle.lean` L103-L128](../../Core/Sync/Shuffle.lean#L103-L128)

In `.up` mode the source lane index `lane - bval` is an integer, so a lane whose number is smaller than `bval` has no source lane: its predicate is false and it receives its own operand. `shflSource .up lane b c` is in range only when `b % 32 ≤ lane` and the maximum lane of the segment is at most `lane - b % 32`; otherwise the lane copies its own operand with predicate false.

Source:

- - §9.7.10.6: "lane[4:0] = [Thread].laneid;" - §9.7.10.6: "bval[4:0] = b[4:0];" - §9.7.10.6: "case .up: j = lane - bval; pval = (j >= maxLane); break;" - §9.7.10.6: "If the computed source lane index j is in range, the thread will copy the input operand a from lane j into its own destination register d ; otherwise, the thread will simply copy its own input a to destination d ."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The pseudo-code declares `lane` and `bval` as 5-bit fields and does not declare `j`. If `j` were a 5-bit field, `lane - bval` would wrap for a lane below `bval` and name a lane at the top of the warp, which `pval` would then compare with `maxLane`. The model takes the integer difference, which is below every `maxLane` for such a lane.

**Effect:** If the hardware wrapped the index, a lane below `bval` would receive another lane's operand with predicate true, and the values the model derives for it would differ from the hardware's. Disclosed by every kernel whose statement names `ShflMode.up`: none.

</details>

<a id="dep-warp-instance"></a>
#### instances of a masked warp collective (`DEP-WARP-INSTANCE`)

*Rule* · [Lean comment: `Core/Sync/WarpInstance.lean` L23-L78](../../Core/Sync/WarpInstance.lean#L23-L78)

In each lane, the n-th execution of a masked warp collective with member mask m belongs to the n-th instance of that collective and mask in the warp. Every lane of the mask either takes part in the instance with the same qualifiers and the same mask, or has exited before reaching it, and the inputs of the instance are those of the lanes that take part. A lane returns from an instance only after every lane of the mask has executed its event of the instance or exited.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`warpSize`](../../Core/Sync/WarpInstance.lean#L108-L110), [`maskInWarp`](../../Core/Sync/WarpInstance.lean#L112-L113) ([concept](#c-maskinwarp)), [`WarpPart`](../../Core/Sync/WarpInstance.lean#L117-L122), [`Execution.MaskK`](../../Core/Sync/WarpInstance.lean#L128-L132) ([concept](#c-execution-maskk)), [`MaskExited`](../../Core/Sync/WarpInstance.lean#L136-L141), [`MaskInstance`](../../Core/Sync/WarpInstance.lean#L143-L153) ([concept](#c-maskinstance)), [`laneBits`](../../Core/Sync/WarpInstance.lean#L196-L198), [`Execution.MaskExitK`](../../Core/Sync/WarpInstance.lean#L155-L160), [`Execution.MaskAt`](../../Core/Sync/WarpInstance.lean#L168-L171), [`MaskWait`](../../Core/Sync/WarpInstance.lean#L173-L180) ([concept](#c-maskwait)), [`maskExited_iff`](../../Core/Sync/WarpInstance.lean#L162-L166), [`MaskWait.ret`](../../Core/Sync/WarpInstance.lean#L182-L186), [`MaskWait.src`](../../Core/Sync/WarpInstance.lean#L188-L194)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads
    corresponding to membermask have executed vote.sync with the same qualifiers and same membermask
    value before resuming execution."
- §9.7.15.11: "match.sync will cause executing thread to wait until all non-exited threads from
    membermask have executed match.sync with the same qualifiers and same membermask value before
    resuming execution."
- §9.7.15.13: "redux.sync will cause the executing thread to wait until all non-exited threads
    corresponding to membermask have executed redux.sync with the same qualifiers and same
    membermask value before resuming execution."
- EXT-WARP-INSTANCE

**Applies:** Instances of `vote.sync` with mode `.all`, `.any` or `.uni` (DEP-WARP-VOTE), of the integer `redux.sync` forms (DEP-WARP-REDUX) and of `match.sync` (DEP-WARP-MATCH)

**Premises:** An event of the collective exists at a given per-mask ordinal.

**Effect:** Instance membership and inputs, used by VoteModeOk, VoteOk, ReduxOk and MatchOk; the waiting dependency `MaskWait`, from which `KindNeeds` (DEP-ORDER) takes the needs of `shfl.sync`, `vote.sync`, `redux.sync` and `match.sync`. A class `c` maps the event kind of a collective to what the lane contributes (`WarpPart`): its member mask, the qualifiers that the lanes of one instance share, and its input. `MaskK` numbers the events of a class with one member mask within a thread; it is the one instance identification of these collectives, used by their value rules and by their needs alike. The instance of the `n`-th events of mask `m` in the warp of thread `g` assigns each lane its input (`part`): the input of its `n`-th event, which has the same qualifiers and mask, for a lane that takes part, and none for a lane of the mask that exited before its `n`-th event and for every lane outside the mask. The thread rules give these collectives a rule only when every lane named in the mask is a thread of the warp (`maskInWarp`), so a lane of the mask is always a thread of the launch. Lanes may reach an instance from different source positions, as for `shfl.sync`. The quoted sentences make every lane of the instance wait: a lane resumes only after each non-exited lane of the mask has executed the instruction with the same qualifiers and the same mask. `MaskWait` states this waiting dependency. It relates, within the warp, the `n`-th event with mask `m` and the same qualifiers of every lane, and the exit of every lane of the mask that exited before its `n`-th such event (`Execution.MaskExitK`), to the return of the `n`-th event of each lane: a lane of the mask that has not exited when another lane waits has not exited for that wait, so the wait ends at its arrival or at its exit. A lane whose `n`-th event has other qualifiers fills no need, so no consistent execution contains the waiting event (`DependencyOk.ready`). Two lanes that reach two instances in opposite orders, such as a `vote.sync` followed by a `redux.sync` in one lane and the reverse in the other, form a cycle of the dependency order that `DependencyOk.acyclic` excludes: no consistent execution contains both returns, the execution stays incomplete and the kernel's progress obligation fails, as on hardware, where both lanes wait forever. The dependency is part of the execution layer only and orders no memory operation.

</details>

<a id="ext-warp-instance"></a>
##### the n-th executions with one member mask form one instance (`EXT-WARP-INSTANCE`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/WarpInstance.lean` L80-L105](../../Core/Sync/WarpInstance.lean#L80-L105)

The lanes of a member mask pair their executions of a masked warp collective by order: in every lane, the n-th execution of the collective with member mask m belongs to the n-th instance of that collective and mask. An instance of `vote.sync`, `redux.sync` or `match.sync` with member mask m contains, for each lane of m that has not exited, that lane's n-th execution of the instruction with member mask m; executions with other member masks belong to other instances.

Source:

- - §9.7.15.10 - §9.7.15.11 and §9.7.15.13, as quoted in DEP-WARP-INSTANCE

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text says what an executing thread waits for. Read literally, an execution that another lane completed earlier with the same mask would satisfy the wait. The text does not say that each execution of a lane takes part in exactly one instance together with one execution of every other non-exited lane of the mask, which is the pairing that the results of these instructions ("the same across all threads in membermask" for `vote.sync`) presuppose.

**Effect:** If a hardware instance paired other executions, the inputs, and so the results, the model assigns would differ from the hardware's. Pairing by order with one mask is the only pairing in which every execution of a lane takes part in one instance with every other non-exited lane of the mask and no two lanes reach two instances in opposite orders. Disclosed by every kernel whose statement names `VoteMode.all`, `VoteMode.any`, `VoteMode.uni`, `VoteMode.ballot`, `WarpKind.redux` or `WarpKind.match_`: FlashAttn4Fwd, FlashMlaSparseDecodeH64.

</details>

<a id="dep-warp-vote"></a>
#### warp vote instances (`DEP-WARP-VOTE`)

*Rule* · [Lean comment: `Core/Sync/Vote.lean` L80-L131](../../Core/Sync/Vote.lean#L80-L131)

The n-th `vote.sync` executions with one member mask of the lanes of a warp form one instance, and every lane named in the member mask either takes part in it with the same qualifiers or has exited before reaching it. The bit of a participating lane in the ballot is that lane's predicate, and the bit of a lane outside the mask is zero. In an instance of a vote with mode `.all`, `.any` or `.uni` the lanes share the mode, and every lane receives the reduction of the predicates of the lanes that take part. A lane returns from a vote only after every non-exited lane of the member mask has executed its vote of the instance (DEP-WARP-INSTANCE). A vote orders no memory operation.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`voteClass`](../../Core/Sync/Vote.lean#L134-L139) ([concept](#c-voteclass)), [`voteResult`](../../Core/Sync/Vote.lean#L141-L148) ([concept](#c-voteresult)), [`VoteOk`](../../Core/Sync/Vote.lean#L150-L159), [`VoteModeOk`](../../Core/Sync/Vote.lean#L161-L166)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.10 (vote.sync): "vote.sync will cause executing thread to wait until all non-exited
    threads corresponding to membermask have executed vote.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.15.10 (vote.sync): "In this form, vote.sync.ballot.b32 simply copies the predicate from each
    thread in membermask into the corresponding bit position of destination register d , where the
    bit position corresponds to the thread’s lane id. A thread not specified in membermask will
    contribute a 0 for its entry in vote.sync.ballot.b32 ."
- §9.7.15.10 (vote.sync): "In the mode form, vote.sync performs a reduction of the source predicate
    across all non-exited threads in membermask ."
- §9.7.15.10 (vote.sync): ".all True if source predicate is True for all non-exited threads in
    membermask ."
- §9.7.15.10 (vote.sync): ".any True if source predicate is True for some thread in membermask ."
- §9.7.15.10 (vote.sync): ".uni True if source predicate has the same value in all non-exited
    threads in membermask ."

**Applies:** Ballot instances; instances of `vote.sync.{all,any,uni}.pred`

**Premises:** A ballot or mode event exists at a given per-mask ordinal.

**Effect:** Execution constraints in `Consistent.vote` and `Consistent.warpValue` (the received values); the waiting dependency `MaskWait L voteClass` (DEP-WARP-INSTANCE) gives the needs of every `vote.sync` in `KindNeeds` (DEP-ORDER). Ballots and mode votes have one instance identification, the per-mask ordinal of every `vote.sync` execution (`MaskK voteClass`), in the value rules and in the needs alike. A lane whose execution at that ordinal has other qualifiers (a ballot against a mode, or another mode) fills no need, so the waiting vote does not exist in a consistent execution, as the text requires the same qualifiers. The negation of the source is part of the lane's predicate and is no qualifier. `.any` takes the predicates of the lanes that take part: a lane that exited has no predicate. `.uni` holds when the predicates of the lanes that take part are all true or all false.

</details>

<a id="dep-warp-redux"></a>
#### integer warp reduction instances (`DEP-WARP-REDUX`)

*Rule* · [Lean comment: `Core/Sync/Redux.lean` L64-L91](../../Core/Sync/Redux.lean#L64-L91)

A reduction belongs to an instance of the `redux.sync` executions with its member mask (DEP-WARP-INSTANCE) whose lanes share the operation and type, and every lane receives the operation applied to the sources of the lanes that take part. Addition wraps modulo 2^32, `.min` and `.max` compare as signed integers for `.s32` and as unsigned integers for `.u32`, and `.and`, `.or`, `.xor` are bitwise. A reduction orders no memory operation.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`reduxStep`](../../Core/Sync/Redux.lean#L94-L102), [`reduxResult`](../../Core/Sync/Redux.lean#L104-L107) ([concept](#c-reduxresult)), [`reduxClass`](../../Core/Sync/Redux.lean#L109-L113), [`ReduxOk`](../../Core/Sync/Redux.lean#L115-L121)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.13 (redux.sync): "redux.sync performs a reduction operation .op of the 32 bit source
    register src across all non-exited threads in the membermask ."
- §9.7.15.13 (redux.sync): "Reduction operation can be one of the bitwise operation in .and , .or ,
    .xor or arithmetic operation in .add , .min , .max ."
- §9.7.15.13 (redux.sync): "For the .add operation result is truncated to 32 bits."
- EXT-WARP-INSTANCE

**Applies:** Instances of the integer `redux.sync` forms

**Premises:** A reduction event exists at a given per-mask ordinal.

**Effect:** Execution constraint in `Consistent.warpValue`. The operations are associative and commutative, so the result does not depend on the order in which `reduxResult` combines the sources; it takes them by lane. `.min` and `.max` on `.u32` and `.s32` compare the values of the type. A lane that exited contributes no source.

</details>

<a id="dep-warp-match"></a>
#### warp match instances (`DEP-WARP-MATCH`)

*Rule* · [Lean comment: `Core/Sync/Match.lean` L71-L103](../../Core/Sync/Match.lean#L71-L103)

A match belongs to an instance of the `match.sync` executions with its member mask (DEP-WARP-INSTANCE) whose lanes share the mode and type. In `.any` mode a lane receives the mask of the lanes that take part and whose operand equals its own. In `.all` mode a lane receives the mask of the lanes that take part when all their operands are equal and zero otherwise, and its predicate is whether they are all equal. A match orders no memory operation.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`matchEqual`](../../Core/Sync/Match.lean#L106-L108), [`matchMask`](../../Core/Sync/Match.lean#L110-L114) ([concept](#c-matchmask)), [`matchClass`](../../Core/Sync/Match.lean#L116-L120), [`MatchOk`](../../Core/Sync/Match.lean#L122-L128)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.11 (match.sync): "match.sync performs broadcast and compare of operand a across all
    non-exited threads in membermask and sets destination d and optional predicate p based on mode."
- §9.7.15.11 (match.sync): "Destination d is a 32-bit mask where bit position in mask corresponds to
    thread’s laneid."
- §9.7.15.11 (match.sync): ".all d is set to mask corresponding to non-exited threads in membermask
    if all non-exited threads in membermask have same value of operand a ; otherwise d is set to 0.
    Optionally predicate p is set to true if all non-exited threads in membermask have same value of
    operand a ; otherwise p is set to false."
- §9.7.15.11 (match.sync): ".any d is set to mask of non-exited threads in membermask that have same
    value of operand a ."
- EXT-WARP-INSTANCE

**Applies:** Instances of `match.sync`

**Premises:** A match event exists at a given per-mask ordinal.

**Effect:** Execution constraint in `Consistent.warpValue`. The event of an `.any` match records the equality predicate as well; THREAD-MATCH does not write it. In `.any` mode the lanes that "have same value of operand a" are those whose operand equals the operand of the receiving lane, which takes part in the instance.

</details>

<a id="dep-warp-activemask"></a>
#### the mask of active threads (`DEP-WARP-ACTIVEMASK`)

*Rule* · [Lean comment: `Core/Sync/ActiveMask.lean` L46-L70](../../Core/Sync/ActiveMask.lean#L46-L70)

The mask that `activemask` returns has the bit of the executing lane set and the bit of every lane with no thread clear. The bits of the other lanes of the warp are unconstrained. The query waits for no other lane and orders no memory operation.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`ActiveMaskOk`](../../Core/Sync/ActiveMask.lean#L73-L77)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.12 (activemask): "An active thread will contribute 1 for its entry in the result and
    exited or inactive or predicated-off thread will contribute 0 for its entry in the result."
- §3.2: "A schedule optimizer determines how to group active threads from the same warp together
    into SIMT units"

**Applies:** Every `activemask` event

**Premises:** An `activemask` event exists.

**Effect:** Execution constraint in `Consistent.warpValue`. The executing thread is active and its guard is true, so its bit is set. Which other lanes are active is decided by the schedule optimizer (§3.2) and is not determined by the program, so every value of their bits is kept, including a set bit for a lane that has exited (stricter). A lane with no thread (the last warp of a CTA whose size is not a multiple of 32) is never active.

</details>

<a id="thread-matrix-layout"></a>
#### fragment layouts (`THREAD-MATRIX-LAYOUT`)

*Rule* · [Lean comment: `Core/Sync/MatrixLayout.lean` L19-L97](../../Core/Sync/MatrixLayout.lean#L19-L97)

Each lane of a warp holds fixed elements of the matrices of a warp-level matrix instruction. For `mma` and `mma.sp` the row and column of each fragment element follow the manual's formulas, and for `ldmatrix`, `stmatrix`, `movmatrix`, the sparse metadata and the sparse B fragments that only the manual's figures give they follow the figures. The registers of a lane hold their elements from the low bits up.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`MatrixMove.source`](../../Core/Sync/MatrixLayout.lean#L240-L251), [`transposeSource`](../../Core/Sync/MatrixLayout.lean#L253-L258), [`MmaSpec.perReg`](../../Core/Sync/MatrixLayout.lean#L260-L261), [`MmaSpec.fragA`](../../Core/Sync/MatrixLayout.lean#L263-L274), [`MmaSpec.fragB`](../../Core/Sync/MatrixLayout.lean#L276-L285), [`MmaSpec.fragCD`](../../Core/Sync/MatrixLayout.lean#L287-L295), [`MmaSpec.metaCols`](../../Core/Sync/MatrixLayout.lean#L297-L300), [`MmaSpec.metaLoc`](../../Core/Sync/MatrixLayout.lean#L302-L312), [`MmaSpec.sparseCol`](../../Core/Sync/MatrixLayout.lean#L314-L326)

<details>
<summary>Details for reviewers</summary>

- §9.7.16.5.1: "A warp executing mma.m8n8k4 with .f16 floating point type will compute 4 MMA
    operations of shape .m8n8k4"
- §9.7.16.5.1: "MMA computation 1 Threads with %laneid 0-3 (low group) and 16-19 (high group)"
- §9.7.16.5.1: "row = % laneid % 4 if % laneid < 16 ( % laneid % 4 ) + 4 otherwise col = i for ai
    where i = { 0 ,.., 3 }"
- §9.7.16.5.1: "row = X if % laneid < 16 X + 4 otherwise where X = ( % laneid & 0b1 ) + ( i & 0b10 )
    for ci where i = { 0 ,.., 7 } col = ( i & 0b100 ) + ( % laneid & 0b10 ) + ( i & 0b1 )"
- §9.7.16.5.2 to §9.7.16.5.13: "groupID = % laneid >> 2 threadID_in_group = % laneid % 4"
- §9.7.16.5.8: "row = groupID for ai where 0 <= i < 2 || 4 <= i < 6 groupID + 8 Otherwise col = (
    threadID_in_group * 2 ) + ( i & 0x1 ) for ai where i < 4 ( threadID_in_group * 2 ) + ( i & 0x1 )
    + 8 for ai where i >= 4"
- §9.7.16.5.8: "row = groupID for ci where i < 2 groupID + 8 for ci where i >= 2 col = (
    threadID_in_group * 2 ) + ( i & 0x1 ) for ci where i = { 0 ,.., 3 }"
- §9.7.16.5.10: "row = ( threadID_in_group * 4 ) + ( i & 0x3 ) for bi where i < 4 (
    threadID_in_group * 4 ) + ( i & 0x3 ) + 16 for bi where i >= 4 col = groupID"
- §9.7.16.5.14: "The registers in each thread hold a fragment of matrix as described in Matrix
    multiply-accumulate operation using mma instruction ."
- §9.7.16.5.15: "Each thread in a warp loads fragments of a row, with thread 0 receiving the first
    fragment in its register r , and so on."
- §9.7.16.5.15: "The eight addresses required for each matrix are provided by eight threads"
- §9.7.16.5.15: "Optional qualifier .trans indicates that the matrix is loaded in column-major
    format."
- §9.7.16.5.16: "Each element in the source operand r is of type .b32 and contains four 8 bit
    elements e0 , e1 , e2 , e3 with e0 and e3 containing the LSB and MSB respectively of register r
    ."
- §9.7.16.5.17: "Each thread in a warp holds a fragment of a column of the result matrix, with
    thread 0 holding the first fragment in register d , and so on."
- §9.7.16.6.2: "Tk: [m..n] present in cell [x][y..z] indicates that bits m through n (with m being
    higher) in the metadata operand of thread with %laneid=k contains the indices of the non-zero
    elements from the chunk [x][y]..[x][z] of matrix A."
- §9.7.16.6.2: "col = [ firstcol ... lastcol ] // As per the mapping of non-zero elements"
- §9.7.16.6.3: "Instruction mma.sp::ordered_metadata requires the indices in the sparsity metadata
    to be sorted in an increasing order starting from LSB, otherwise behavior is undefined."
- EXT-MATRIX-FIGURES
- EXT-MMA-SPARSE-FIGURES
- EXT-MMA-FRAGMENTS

**Applies:** The supported forms of THREAD-MATRIX and THREAD-MMA-SYNC

**Effect:** Element positions used by DEP-WARP-MATRIX and DEP-WARP-MMA. The notation is: lane `l` has `g = l / 4` (groupID) and `t = l % 4` (threadID_in_group). A register of an operand with elements of `w` bits holds `32 / w` elements (one `.f64` element per 64-bit register), and element `i` of a lane's fragment is at bits `i * w` of the concatenated registers, register 0 first: the manual numbers fragment elements from low to high. `MatrixMove.source m l r b` is the row (the lane that supplied its address) and the byte in that row of byte `b` of register `r` of lane `l`. Without `.trans`, lane `l` holds bytes `4t` to `4t + 3` of row `g` of each `.m8n8` matrix. With `.trans` the register holds the transposed matrix: the element in row `i` and column `j` of the figure is element `i` of memory row `j`. `transposeSource l b` is the lane and byte of the `movmatrix` source that byte `b` of lane `l`'s destination holds. `MmaSpec.fragA s l i`, `fragB` and `fragCD` give `(q, row, col)` of element `i` of lane `l`'s fragment, where `q` is the computation (0 to 3 for the four-MMA form, 0 otherwise). Every other shape follows one formula per operand, which agrees with every formula of §9.7.16.5.2 to §9.7.16.5.13: for A, register `r` of `e` elements has row `g + 8 (r mod 2)` and column `e t + (i mod e) + 4 e (r / 2)`; for B, register `r` has row `4 e r + e t + (i mod e)` and column `g`; for C and D, element `i` has row `g + 8 (i / 2)` and column `2 t + (i mod 2)`. The A operand of `mma.sp` holds the non-zero elements of the compressed `m × k/2` matrix in the layout of the dense shape with `k/2` columns, which is what the formulas of §9.7.16.6.2 give for `[firstcol ... lastcol]`. `MmaSpec.metaCols` is the number of columns of A one 4-bit metadata field covers, `MmaSpec.metaLoc` the lane and bit of the field of a row and chunk, and `MmaSpec.sparseCol` the column of A that a compressed element has under the field: for 16- and 8-bit types two 2-bit indices select two of four columns, for `.tf32` the field `0b0100` selects the first and `0b1110` the second of two columns, and for 4-bit types two 2-bit indices select two of four pairs of columns; the first compressed element of a chunk takes the index in the low bits.

</details>

<a id="ext-matrix-figures"></a>
##### the layouts and the row accesses of ldmatrix, stmatrix and movmatrix (`EXT-MATRIX-FIGURES`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/MatrixLayout.lean` L99-L162](../../Core/Sync/MatrixLayout.lean#L99-L162)

The model makes two readings of `ldmatrix`, `stmatrix` and `movmatrix`. (1) The fragment layouts are those of the manual's figures, a register holds its elements from the low bits up, `.trans` exchanges the rows and columns of the figure, and a 16-row matrix takes its addresses from 16 consecutive threads and its two registers from consecutive register positions. `MatrixMove.source` and `transposeSource`: for `.m8n8` lane `l` holds row `l / 4`, bytes `4 (l mod 4)` to `4 (l mod 4) + 3` (Figures 107 and 110); for `.m16n16` register `2 k + h` of lane `l` holds byte `4 (l mod 4) + b` of row `8 h + l / 4` of matrix `k` in its byte `b` (Figure 108), whose rows are supplied by threads `16 k` to `16 k + 15`; for `.m16n8` element `e` of lane `l` is in row `l / 4 + 8 (e / 2)` and column `2 (l mod 4) + e mod 2` (Figure 111); with `.trans` the element in row `i` and column `j` of the figure is element `i` of the memory row whose address is the `j`-th; the `movmatrix` source of lane `l` is row `l / 4`, columns `2 (l mod 4)` and `2 (l mod 4) + 1`, and its result is column `l / 4`, rows `2 (l mod 4)` and `2 (l mod 4) + 1` (Figures 112 and 113); the element with the smaller row or column index is in the low half of the register. (2) The 16 bytes of a matrix row of `ldmatrix` or `stmatrix` are read or written by the thread that supplies the row's address, as one weak access of that thread. `matrixMoveTmpl` gives each row-address thread one `.read` (`ldmatrix`) or `.write` (`stmatrix`) of 16 bytes at its address, and no other thread accesses memory.

Source:

- - §9.7.16.5.15 to §9.7.16.5.17, as quoted in THREAD-MATRIX-LAYOUT, and Figures 107 to 113 (images of the HTML manual) - §9.7.16.5.15 and §9.7.16.5.16, as quoted in THREAD-MATRIX

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** (1) The layouts are drawn in figures; the text says which thread receives the first fragment and how many elements a register holds, and that `.trans` loads in column-major format, without giving positions. The address table names eight threads per matrix, which does not cover the sixteen rows of an `.m16n16` matrix, and the text does not say which of the four registers of `.m16n16.x2` hold which matrix. (2) The text says that the instruction is a weak memory operation and that a group of four threads loads or stores 16 bytes, but not which thread's operation each access is, which decides the program order and the base causality edges the memory model gives it.

**Evidence:** (1) Manual: §9.7.16.5.15 to §9.7.16.5.17 and Figures 107 to 113, as above. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23): the layouts of `SM75_U32x{1,2,4}_LDSM_N`, `SM75_U16x{2,4,8}_LDSM_T`, `SM90_U32x{1,2,4}_STSM_N`, `SM90_U16x{2,4,8}_STSM_T`, `SM100_U8x8_LDSM_T`, `SM100_U8x16_LDSM_T` (with the byte regrouping their `copy` applies), `SM100_SU4_DU8x16_x1_LDSM_N`, `SM100_SU6_DU8x16_x1_LDSM_N` and `SM100_U8x{4,8,16}_STSM_T` agree with `MatrixMove.source` for every register byte (txverify-archive/core-coverage/probes/cutlass_check.py); `SM75_U32x1_MOVM_T` gives no independent `movmatrix` map. Hardware probe: txverify-archive/core-coverage/probes/matrix_move/matrix_move.cu covers every `ldmatrix`, `stmatrix` and `movmatrix` form above. It ran on a B200 on 2026-11-16 and agreed with the model in every form. (2) The manual's address table assigns the rows of each matrix to threads, as quoted in THREAD-MATRIX. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) describes the same assignment in the SrcLayout of `SM75_U32x{1,2,4}_LDSM_N` (include/cute/atom/copy_traits_sm75.hpp), where only the supplying threads have nonzero stride, and in the DstLayout of the `SM90_*_STSM_*` atoms; it says nothing about which thread performs the access. The value part (which lanes' addresses are used) is checked by the hardware probe txverify-archive/core-coverage/probes/matrix_move/matrix_move.cu, where non-supplying lanes point at a poison row. The attribution part is checked as far as a tool can see it by matrix_row_access.cu in the same directory, which runs under compute-sanitizer memcheck and expects the one invalid 16-byte access to be reported for the supplying thread. Both ran on a B200 on 2026-11-16 and agreed: memcheck reported one invalid 16-byte shared access, by the supplying thread 5, for `ldmatrix` and for `stmatrix`, and none for lanes 8 to 31.

**Effect:** If the hardware placed the elements otherwise, the register values that the model derives for `ldmatrix` and `movmatrix` and the memory contents it derives for `stmatrix` would differ from the hardware's. If the hardware attributed a row's access to another thread of the warp, an execution the model accepts could race with that thread's earlier or later accesses to the row. Disclosed by every kernel whose statement names `Op.matrix`: none.

</details>

<a id="ext-mma-sparse-figures"></a>
##### the sparse metadata layout (`EXT-MMA-SPARSE-FIGURES`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/MatrixLayout.lean` L164-L202](../../Core/Sync/MatrixLayout.lean#L164-L202)

The metadata of `mma.sp` is laid out as the manual's figures show, a 2-bit index in the low bits belongs to the first non-zero element of its chunk, and the B fragments of the sparse shapes that only figures give continue the formula of the dense shapes. `MmaSpec.metaLoc` and `MmaSpec.sparseCol`: with four fields per row (`.m16n8k16` of 16-bit types, `.m16n8k8` of `.tf32`) the thread of the selector in each group of four holds row `g` in bits 0 to 15 and row `g + 8` in bits 16 to 31, field `u` at bit `4 u` (Figures 122 and 130); with eight fields per row of 16- or 32-bit types (`.m16n8k32` of 16-bit types, `.m16n8k16` of `.tf32`) thread `2 f` of the group holds the first four fields of rows `g` and `g + 8` and thread `2 f + 1` the last four (Figures 125 and 128); with eight fields per row of 8- or 4-bit types thread `2 f` holds row `g` and thread `2 f + 1` row `g + 8`, field `u` at bit `4 u` (Figures 132 and 142); with sixteen fields per row thread `2 h + v` holds half `h` of row `g + 8 v` (Figures 139, 140, 149 and 150). The B fragments of `.m16n8k32` of 16-bit types, `.m16n8k16` of `.tf32`, `.m16n8k64` of 8-bit types and `.m16n8k128` of 4-bit types follow `MmaSpec.fragB` (Figures 124, 127, 135 to 138 and 145 to 148).

Source:

- - §9.7.16.6.1 and §9.7.16.6.2, as quoted in THREAD-MATRIX-LAYOUT, and Figures 115 to 150 (images of the HTML manual)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The metadata layouts and these B fragments are drawn only in figures; the text gives the meaningful index values, which for the ordered variant put the smaller index in the low bits, and the order of the non-zero elements in the fragment is not stated.

**Evidence:** Manual: §9.7.16.6.1 and §9.7.16.6.2 with Figures 115 to 150, as above. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) has no CuTe `mma.sp` atom for these shapes; its CUTLASS 2.x wrappers (include/cutlass/arch/mma_sparse_sm80.h) issue `mma.sp::ordered_metadata` with 2-bit indices and two selector values for `m16n8k32` of 16-bit types, the range the model allows, and keep the metadata placement in reorder code that was not evaluated. The hardware probe txverify-archive/core-coverage/probes/mma_fragments/ runs every sparse shape and type with every allowed selector, ordered and unordered metadata, and random bits in the metadata the model says is unused. It ran on a B200 on 2026-11-16 with two random seeds and agreed with the model in every sparse form.

**Effect:** If the hardware read the metadata otherwise, the columns of A that the model multiplies with B, and so the results it derives, would differ from the hardware's. Disclosed by every kernel whose statement names `MmaSpec.sparse`: none.

</details>

<a id="ext-mma-fragments"></a>
##### the fragment layouts of mma.sync, including the A columns of `mma.m16n8k256` (`EXT-MMA-FRAGMENTS`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/MatrixLayout.lean` L204-L237](../../Core/Sync/MatrixLayout.lean#L204-L237)

The model reads the A, B and C fragments of the dense `mma` shapes by the manual's formulas, with one exception. Elements 32 to 63 of the A fragment of `mma.m16n8k256` are in columns `32 t + (i & 0x1F)` of row `g + 8`, as in `mma.m16n8k128`. The manual's formula gives `32 t + i`. `MmaSpec.fragA` uses `32 t + (i & 0x1F) + 128 (r / 2)` for every element of `.b1` A.

Source:

- - §9.7.16.5.13: "( threadID_in_group * 32 ) + i for ai where i < 64 ( threadID_in_group * 32 ) + ( i & 0x1F ) + 128 for ai where i >= 64" - §9.7.16.5.12: "col = ( threadID_in_group * 32 ) + ( i & 0x1F ) for ai where i = { 0 , ..., 63 }"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** Read literally, the formula gives lane `t` columns `32 t + 32` to `32 t + 63` of row `g + 8`, which are the columns of lane `t + 1`'s first register, so two lanes would hold one element and columns 0 to 31 of row `g + 8` none.

**Evidence:** Manual: the two formulas quoted above. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23): the A, B and C layouts of the SM80 and SM90 `mma` atoms of 16-, 32-, 64-, 8-, 4- and 1-bit types agree with `MmaSpec.fragA`, `fragB` and `fragCD` (txverify-archive/core-coverage/probes/cutlass_check.py); the ALayout of `SM80_16x8x256_S32U1U1S32_TN_XORPOPC` (include/cute/atom/mma_traits_sm80.hpp), `((4,8),(32,2,2)):((512,1),(16,8,2048))`, puts element i of lane l in column `32 t + (i & 0x1F) + 128 (i / 64)`, which is this reading (txverify-archive/core-coverage/probes/cutlass_check.py). Read literally, the manual's formula leaves 512 of the 4096 positions of A held by no lane or by two. The hardware probe txverify-archive/core-coverage/probes/mma_fragments/ covers every dense `mma` shape and type and runs `m16n8k256` with `.and.popc` and `.xor.popc` against this reading. It ran on a B200 on 2026-11-16 with two random seeds and agreed with the model in every dense form.

**Effect:** If the hardware used another placement, the single-bit products the model derives for this shape would differ from the hardware's. Disclosed by every kernel whose statement names `Op.matrix`: none.

</details>

<a id="dep-warp-matrix"></a>
#### instances of the warp-level matrix instructions (`DEP-WARP-MATRIX`)

*Rule* · [Lean comment: `Core/Sync/MatrixExec.lean` L24-L71](../../Core/Sync/MatrixExec.lean#L24-L71)

In each lane of a warp, the n-th warp-level matrix event belongs to the n-th instance of the warp, which waits for all 32 lanes. A lane of a matrix load receives the bytes of the rows that its registers hold, a lane of a matrix store that supplies a row receives the bytes of that row from the registers that hold them, and a lane of `movmatrix` receives the transposed elements. A result that cannot be computed is ERR-WARP-MATRIX. A lane that exits before the instance and two lanes of the instance that execute different instructions are ERR-ALIGNED-MISMATCH.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`isMatrix`](../../Core/Sync/MatrixExec.lean#L74-L77), [`Execution.MatrixK`](../../Core/Sync/MatrixExec.lean#L83-L85), [`MatrixInstance`](../../Core/Sync/MatrixExec.lean#L89-L95), [`MatrixResult`](../../Core/Sync/MatrixExec.lean#L97-L100), [`OpenBytes`](../../Core/Sync/MatrixExec.lean#L102-L104), [`MatrixMove.storeByte`](../../Core/Sync/MatrixExec.lean#L106-L114), [`matrixMoveRecv`](../../Core/Sync/MatrixExec.lean#L116-L127), [`transposeRecv`](../../Core/Sync/MatrixExec.lean#L129-L133), [`matrixRecv`](../../Core/Sync/MatrixExec.lean#L293-L299), [`MatrixOk`](../../Core/Sync/MatrixExec.lean#L301-L309), [`matrixOk_of_none`](../../Core/Sync/MatrixExec.lean#L311-L317)

<details>
<summary>Details for reviewers</summary>

- §9.7.16.5.15: "The mandatory .sync qualifier indicates that ldmatrix causes the executing thread
    to wait until all threads in the warp execute the same ldmatrix instruction before resuming
    execution."
- §9.7.16.5.15: "For 4-bit or 6-bit data, 8-bit element will have 4 bits or 2 bits of padding
    respectively."
- §9.7.16.5.17: "Each thread in a warp holds a fragment of a column of the result matrix, with
    thread 0 holding the first fragment in register d , and so on."
- THREAD-MATRIX-LAYOUT

**Applies:** Instances of the forms with THREAD-MATRIX and THREAD-MMA-SYNC

**Premises:** A matrix event exists at a given per-thread ordinal.

**Effect:** Execution constraint in `Consistent.matrix`; the undefined behaviour of an instance is ERR-WARP-MATRIX. `MatrixK` numbers the matrix events of a thread. The instance of the `n`-th events in the warp of thread `g` (`MatrixInstance`) assigns each lane the bytes it contributes; it exists when every lane of the warp performs its `n`-th matrix event at the same source position with the same operation. A lane's received bytes are `matrixRecv` of the instance: for a matrix load the bytes of the rows at the positions `MatrixMove.source` gives, for a matrix store the bytes of the supplier's row from the registers `MatrixMove.source` maps to it (`MatrixMove.storeByte`), for `movmatrix` the bytes `transposeSource` gives, and for an MMA the bytes of DEP-WARP-MMA. The `.b8x16` loads from a 6-bit or 4-bit source format have open results (`OpenBytes`): each received byte is a byte of an 8-bit integer, because the text gives neither the position of a source element in its row nor the position of the padding in the 8-bit element. Every lane of the warp either takes part or has exited (`Execution.ExitedShort`). An exited lane, lanes of one instance at different source positions and lanes with different operations are undefined behaviour by ERR-ALIGNED-MISMATCH. An instance orders no memory operation: the rows are accessed by the threads' own reads and writes (THREAD-MATRIX). Its waiting is the need of each event (`KindNeeds`, DEP-ORDER): every lane's `n`-th matrix event, or its exit short of it, is a witness of the return of every event of the instance, an edge of the execution layer only, as for the masked warp collectives (DEP-WARP-INSTANCE). A lane's short exit fills its need so that the instance exists and ERR-ALIGNED-MISMATCH reports the undefined behaviour.

</details>

<a id="dep-warp-mma"></a>
#### the values of `mma` and `mma.sp` (`DEP-WARP-MMA`)

*Rule* · [Lean comment: `Core/Sync/MatrixExec.lean` L135-L193](../../Core/Sync/MatrixExec.lean#L135-L193)

Each lane of an `mma` or `mma.sp` instance receives its D elements, each the sum of the products of its A row and B column plus its C element, all read from the registers that hold them. Integer products are exact and their sum wraps modulo 2^32, or with `.satfinite` has a value only when no partial sum leaves the s32 range; single-bit products are the bit operation of the two bits. Floating results come only from a kernel assumption. The non-zero elements of a sparse A meet the B rows their metadata selects, and invalid metadata or an invalid selector is undefined behaviour.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`mmaElem`](../../Core/Sync/MatrixExec.lean#L196-L214), [`findFrag`](../../Core/Sync/MatrixExec.lean#L216-L220), [`operandElem`](../../Core/Sync/MatrixExec.lean#L222-L228), [`metaField`](../../Core/Sync/MatrixExec.lean#L230-L234), [`elemInt`](../../Core/Sync/MatrixExec.lean#L236-L240), [`mmaValue`](../../Core/Sync/MatrixExec.lean#L242-L257), [`mmaRecv`](../../Core/Sync/MatrixExec.lean#L259-L291)

<details>
<summary>Details for reviewers</summary>

- §9.7.16.5.14: "Perform a MxNxK matrix multiply and accumulate operation, D = A*B+C , where the A
    matrix is MxK , the B matrix is KxN , and the C and D matrices are MxN ."
- §9.7.16.5.14: "mma.xor.popc and mma.and.popc computes the XOR, AND respectively of a k-bit row of
    A with a k-bit column of B, then counts the number of set bits in the result ( popc ). This
    result is added to the corresponding element of C and written into D."
- §9.7.16.5.14: "The .satfinite qualifier indicates that on overflow, the accumulated value is
    limited to the range MIN_INT32 .. MAX_INT32"
- §9.7.16.5.14: "If .satfinite is not specified, the accumulated value is wrapped instead."
- §9.7.16.5.14: "The accumulation order, rounding and handling of subnormal inputs are unspecified."
- §9.7.16.5.14: "Precision of the element-wise multiplication and addition operation is identical to
    that of .f64 precision fused multiply-add."
- §9.7.16.6.1: "Values 0b0000 , 0b0101 , 0b1010 , 0b1111 are invalid values for metadata and will
    result in undefined behavior."
- §9.7.16.6.1: "0b1110 and 0b0100 are the only meaningful index values; any other values result in
    undefined behavior."
- §9.7.16.6.1: "Hence, the sparsity selector must be either 0 (threads T0, T1) or 1 (threads T2,
    T3); any other value results in undefined behavior."
- §9.7.16.6.1: "Hence, the sparsity selector in this case must be 0. Any other value of sparsity
    selector results in an undefined behavior."
- §9.7.16.6.3: "Instruction mma.sp::ordered_metadata requires the indices in the sparsity metadata
    to be sorted in an increasing order starting from LSB, otherwise behavior is undefined."
- THREAD-MATRIX-LAYOUT
- ASM-INTERFACE

**Applies:** Instances of the forms with THREAD-MMA-SYNC

**Premises:** The instance exists (DEP-WARP-MATRIX).

**Effect:** The bytes each lane receives (`matrixRecv`); a computation that fails is undefined behaviour (`MatrixUnsafe`, ERR-WARP-MATRIX). `mmaRecv` computes, for each element of the lane's D fragment (`MmaSpec.fragCD`), its row, column and computation, finds every A, B and C element it needs in the lane and register that hold it (`findFrag`, THREAD-MATRIX-LAYOUT) and reads it from that lane's bytes (`mmaElem`): a floating element is rebuilt from its bytes (THREAD-BYTES), and an integer element is the bits of its bytes or, for a 4-bit or 1-bit element, of its part of a byte. For `mma.sp` the `k/2` stored elements of the A row are paired with the B rows `MmaSpec.sparseCol` selects from the metadata field of their chunk (`metaField`), and the zeros of A contribute nothing. An integer element is signed or unsigned by its type (`elemInt`) and C is a signed 32-bit integer. With `.satfinite` the clamped sum depends on the unspecified accumulation order when a partial sum leaves the s32 range, so the model derives a value only when no partial sum does (as for `tcgen05.mma`, `TcMma.SaturationFree`), and otherwise there is no rule (stricter). The floating types, `.f64` included, have no Core arithmetic: the first assumption whose `matrixMmaRule` gives a value for the element types supplies it (ASM-INTERFACE), and without one the instance is undefined behaviour (`noRule`). The D elements are packed into the D registers two to a register for `.f16` and one otherwise, the lower element first.

</details>

### What counts as an error

Executions rejected as unsafe because the lanes of a warp may disagree on a barrier, an aligned instruction or a uniform guard, or because a participant exits before an aligned instruction.

<a id="err-aligned-mismatch"></a>
#### aligned participants execute the same instruction (`ERR-ALIGNED-MISMATCH`)

*Rule* · [Lean comment: `Core/Sync/Aligned.lean` L21-L129](../../Core/Sync/Aligned.lean#L21-L129)

The lanes of one warp execute their k-th aligned instruction of one class at one source position and with the same operands. The classes are the warp-collective `tcgen05` instructions, `barrier{.cta}`, `barrier.cluster`, `setmaxnreg` and the warp-level matrix instructions. A participant of an aligned instruction does not exit before it executes the instruction. The participants are the warp, the warpgroup for `setmaxnreg`, and every thread of the CTA for an aligned `barrier{.cta}` without a thread count. An execution that breaks either condition is unsafe.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Execution.ExitedShort`](../../Core/Sync/Aligned.lean#L132-L136), [`Kernel.alignedAt`](../../Core/Sync/Aligned.lean#L138-L142), [`Kernel.isAlignedCtaBar`](../../Core/Sync/Aligned.lean#L144-L148), [`tcStatic`](../../Core/Sync/Aligned.lean#L150-L155), [`AlignedClass`](../../Core/Sync/Aligned.lean#L157-L169), [`AlignedClass.member`](../../Core/Sync/Aligned.lean#L173-L180), [`AlignedClass.exitMember`](../../Core/Sync/Aligned.lean#L182-L186), [`AlignedClass.aligned`](../../Core/Sync/Aligned.lean#L188-L195), [`AlignedClass.operands`](../../Core/Sync/Aligned.lean#L197-L203), [`AlignedClass.Participants`](../../Core/Sync/Aligned.lean#L205-L210), [`AlignedClass.Divergent`](../../Core/Sync/Aligned.lean#L212-L219), [`AlignedClass.Exited`](../../Core/Sync/Aligned.lean#L221-L226), [`AlignedMismatch`](../../Core/Sync/Aligned.lean#L230-L233), [`alignedMismatch_iff`](../../Core/Sync/Aligned.lean#L235-L252), [`isTcColl_kind`](../../Core/Sync/Aligned.lean#L254-L255), [`isCluster_kind`](../../Core/Sync/Aligned.lean#L257-L259), [`isMatrix_kind`](../../Core/Sync/Aligned.lean#L261-L263), [`isRequest_kind`](../../Core/Sync/Aligned.lean#L265-L267), [`isAlignedCtaBar_kind`](../../Core/Sync/Aligned.lean#L269-L274), [`sameWarp_lane`](../../Core/Sync/Aligned.lean#L276-L286), [`AlignedClass.divergent_tc_iff`](../../Core/Sync/Aligned.lean#L290-L309), [`AlignedClass.exited_tc_iff`](../../Core/Sync/Aligned.lean#L311-L319), [`AlignedClass.divergent_bar_iff`](../../Core/Sync/Aligned.lean#L321-L336), [`AlignedClass.exited_bar_iff`](../../Core/Sync/Aligned.lean#L338-L348), [`AlignedClass.divergent_cluster_iff`](../../Core/Sync/Aligned.lean#L350-L366), [`AlignedClass.exited_cluster_iff`](../../Core/Sync/Aligned.lean#L368-L378), [`AlignedClass.divergent_setMaxReg_iff`](../../Core/Sync/Aligned.lean#L380-L394), [`AlignedClass.exited_setMaxReg_old`](../../Core/Sync/Aligned.lean#L396-L409), [`AlignedClass.divergent_matrix_old`](../../Core/Sync/Aligned.lean#L411-L433), [`AlignedClass.exited_matrix_old`](../../Core/Sync/Aligned.lean#L435-L445)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1: "Instruction barrier{.cta} has optional .aligned modifier. When specified, it indicates
    that all threads in CTA will execute the same barrier{.cta} instruction."
- §9.7.15.1 (bar.sync is barrier.sync.aligned)
- §9.7.15.1: "bar{.cta}.arrive is equivalent to barrier{.cta}.arrive.aligned ."
- §9.7.15.3: "The optional .aligned qualifier indicates that all threads in the warp must execute
    the same barrier.cluster instruction."
- §9.7.16.5.14: "The mandatory .aligned qualifier indicates that all threads in the warp must
    execute the same mma instruction."
- §9.7.16.5.14: "The behavior of mma instruction is undefined if all threads in the same warp do not
    use the same qualifiers, or if any thread in the warp has exited."
- §9.7.16.5.15: "The mandatory .aligned qualifier indicates that all threads in the warp must
    execute the same ldmatrix instruction."
- §9.7.16.5.15: "The behavior of ldmatrix is undefined if all threads do not use the same
    qualifiers, or if any thread in the warp has exited."
- §9.7.16.5.16: "The behavior of stmatrix is undefined if all threads do not use the same
    qualifiers, or if any thread in the warp has exited."
- §9.7.16.5.17: "The mandatory .aligned qualifier indicates that all threads in the warp must
    execute the same movmatrix instruction."
- §9.7.16.6.3: "The behavior of mma.sp/mma.sp::ordered_metadata instruction is undefined if all
    threads in the same warp do not use the same qualifiers, or if any thread in the warp has
    exited."
- §9.7.18.7.1: "The mandatory .aligned qualifier indicates that all threads in the warp must execute
    the same instruction."
- §9.7.18.7.1: "The behavior of the instruction is undefined if all the threads in the warp do not
    use the same values of nCols , or if any thread in the warp has exited."
- §9.7.18.8.3: "The behavior of tcgen05.ld is undefined if all threads do not use the same values of
    taddr , or if any thread in the warp has exited."
- §9.7.18.8.4: "The behavior of tcgen05.st is undefined if all threads do not use the same values of
    taddr , or if any thread in the warp has exited."
- §9.7.18.8.5: "The mandatory .aligned qualifier indicates that all threads in the warp must execute
    the same tcgen05.wait_operation instruction."
- §9.7.21.5: "The mandatory .aligned qualifier indicates that all threads in the warpgroup must
    execute the same setmaxnreg instruction."
- §9.7.21.5: "If a setmaxnreg instruction is not executed by all warps in the warpgroup , then the
    behavior is undefined."
- EXT-BAR-PARTICIPANTS

**Applies:** Warp-collective `tcgen05` events (allocation management, `ld`, `st`, the waits), `barrier{.cta}` events of either form, `barrier.cluster` events, `setmaxnreg` requests and warp-level matrix events

**Premises:** Each class numbers its events within a thread (`AlignedClass.member`); the exit clause of `barrier{.cta}` numbers the aligned barriers without a thread count (`AlignedClass.exitMember`). The exit clause counts the events of the class in the whole trace of the exiting thread (`Execution.ExitedShort`). A trace that the thread rules produce ends at its exit (THREAD-RUN), so there this count equals the count of the events before the exit. On a trace built by hand with events after the exit, the count can be larger and the clause can miss the exit.

**Effect:** Safety rejection (`AlignedMismatch`). Two lanes of a warp at their `k`-th event of a class, one of them aligned, at different source positions or with different operands (`AlignedClass.Divergent`), are undefined. So is a participant that exits with at most `k` events of the class while another participant executes its `k`-th aligned one (`AlignedClass.Exited`). The guard of an aligned instruction is ERR-NONUNIFORM-GUARD. Between different warps, the barrier name and thread count of `barrier{.cta}` and the direction and count of `setmaxnreg` are compared by ERR-BARRIER-MISMATCH and ERR-SETMAXNREG (EXT-BAR-PARTICIPANTS).

</details>

<a id="err-barrier-mismatch"></a>
#### divergent barrier collectives (`ERR-BARRIER-MISMATCH`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L367-L403](../../Core/Assembly/Safety.lean#L367-L403)

An execution is unsafe when two lanes of a warp at their k-th barrier instruction disagree on the barrier, the thread count or the form.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`BarArriveMismatch`](../../Core/Assembly/Safety.lean#L462-L469), [`BarMismatch`](../../Core/Assembly/Safety.lean#L471-L478)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier"
- §9.7.15.1: "All threads in warp (except for those have exited) must execute barrier{.cta}
    instruction in convergence."
- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count."
- EXT-BAR-PARTICIPANTS

**Applies:** Warp collective arrivals of either form

**Premises:** Lanes of a warp at their `k`-th barrier instruction disagree on the barrier, count or form (sync or arrive).

**Effect:** Safety rejection. Independent IDs and different generations are not compared. The source instruction of an aligned barrier and the exit of a participant before an aligned whole-CTA barrier are ERR-ALIGNED-MISMATCH.

</details>

<a id="ext-bar-participants"></a>
##### the participants of an aligned barrier or setmaxnreg (`EXT-BAR-PARTICIPANTS`)

*Interpretation (EXT)* · [Lean comment: `Core/Assembly/Safety.lean` L405-L459](../../Core/Assembly/Safety.lean#L405-L459)

The manual's "same instruction" sentences for an aligned `barrier{.cta}` and for `setmaxnreg` are read in two parts. (1) Between different warps, "the same" `barrier{.cta}` instruction means the same barrier name and thread count, and "the same" `setmaxnreg` instruction means the same direction and register count. The lanes of one warp execute one instruction at one source position. (2) For an aligned `bar.sync`, `bar.arrive` or `bar.red`, "all threads in CTA" means the threads that participate in the barrier generation, that is, the count's worth of warps that arrive at it. A thread that does not participate (for example a warp that has another role and uses another barrier or count) need not execute the barrier. For an aligned barrier without a thread count the participants are all threads of the CTA.

Source:

- - §9.7.15.1: "Instruction barrier{.cta} has optional .aligned modifier. When specified, it indicates that all threads in CTA will execute the same barrier{.cta} instruction." - §9.7.15.1: "In conditionally executed code, an aligned barrier{.cta} instruction should only be used if it is known that all threads in CTA evaluate the condition identically, otherwise behavior is undefined." - §9.7.15.1: "All threads in warp (except for those have exited) must execute barrier{.cta} instruction in convergence." - §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the same barrier name and thread count. One example mixes barrier{.cta}.sync and barrier{.cta}.arrive to implement producer/consumer models." - §9.7.15.1 (its producer/consumer example: `bar.arrive 0, 64` and `bar.sync 0, 64` executed by 64 threads of a larger CTA) - §9.7.21.5: "The same setmaxnreg instruction must be executed by all warps in a warpgroup ." - §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the executing thread to wait until all threads in the warp execute the same setmaxnreg instruction before resuming execution."

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** (1) The text does not say whether "the same instruction" is one position in the program or one barrier or request. Read as one position, warps of different roles, each running its own code, could not synchronize on a named barrier or adjust their registers together, and the text's producer/consumer example, in which different warps execute `barrier{.cta}.arrive` and `barrier{.cta}.sync` (two instructions) on one barrier, would be undefined. The text names the barrier name and thread count as what different warps must share. (2) Read literally, "all threads in CTA" would make `bar.sync b, n` with `n` below the CTA size undefined whenever some CTA thread executes none; the ISA's own example and the explicit participant count show that this is not meant, but the text does not restate the clause for the participants.

**Effect:** ERR-ALIGNED-MISMATCH checks that the lanes of one warp execute their aligned barrier at one source position, and that no participant of an aligned barrier without a thread count exits before it; the exit of a thread before a barrier with a thread count is not reported as undefined. The guard of a guarded aligned barrier is compared among the lanes of one warp (ERR-NONUNIFORM-GUARD). Between warps, ERR-BARRIER-MISMATCH and ERR-SETMAXNREG compare only the barrier and count or the direction and count. If "the same instruction" means one position, a program whose warps reach one barrier generation or one warpgroup request from different positions is undefined and is accepted. A divergence between a participant and a non-participant is not flagged. If the literal reading of "all threads in CTA" holds, such programs are undefined and are accepted. Disclosed by every kernel whose statement names `Op.barSync`, `Op.barSyncN`, `Op.barArrive` or `Op.setMaxReg`: BlockSum, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm.

</details>

<a id="err-cta-barrier"></a>
#### an arrival the CTA barrier resource cannot perform (`ERR-CTA-BARRIER`)

*Rule* · [Lean comment: `Core/Sync/CtaBarrierExecution.lean` L111-L141](../../Core/Sync/CtaBarrierExecution.lean#L111-L141)

An execution is unsafe when a warp arrives at a CTA barrier with a count that differs from the open generation's, or arrives twice in one generation.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`CtaBarFault`](../../Core/Sync/CtaBarrierExecution.lean#L144-L153)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count."
- §9.7.15.1: "Care must be taken to keep a warp from executing more barrier{.cta} instructions than
    intended ( barrier{.cta}.arrive followed by any other barrier{.cta} instruction to the same
    barrier) prior to the reset of the barrier."
- OBJ-CTA-BARRIER-SYNC

**Applies:** CTA barrier arrival events of both forms (`bar.sync`, `bar.arrive`) that are not in the history of their CTA

**Premises:** The recorded history of the CTA is accepted by its barrier resources, and the arrival's lanes execute the matching instruction with the recorded operands (`CtaBarSources`).

**Effect:** Safety rejection (part of Unsafe). An issued collective arrival that the resource cannot perform (`CtaBarrier.Error.isFault`) is not removed from the possible executions: its lanes stay at the barrier, unrecorded, and `CtaBarFault` rejects the execution. The faulting arrival is outside the history, which records every operation the resource performed before it. This covers an arrival whose count differs from the open generation's, whatever the forms (`bar.arrive 1, 64` meeting `bar.sync 1, 128`), and a warp that arrives twice in one generation (`bar.arrive` followed by another `barrier{.cta}` instruction on the same barrier before it completes, the case §9.7.15.1 warns about).

</details>

<a id="err-cluster-barrier"></a>
#### an operation the cluster barrier cannot perform (`ERR-CLUSTER-BARRIER`)

*Rule* · [Lean comment: `Core/Sync/ClusterBarrierExecution.lean` L96-L118](../../Core/Sync/ClusterBarrierExecution.lean#L96-L118)

An execution is unsafe when a thread arrives at the cluster barrier a second time before its phase completes.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`ClusterFault`](../../Core/Sync/ClusterBarrierExecution.lean#L121-L128)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.3 (barrier.cluster): "Each thread must arrive at the barrier only once before the barrier
    completes."
- OBJ-CLUSTER-BARRIER-SYNC

**Applies:** Cluster arrive and wait collectives of a whole warp that are not in the history of their cluster

**Premises:** The recorded history of the cluster is accepted by its barrier, and the collective's threads execute the matching instruction with the recorded operands (`ClusterSources`).

**Effect:** Safety rejection (part of Unsafe). An issued collective that the object cannot perform (`ClusterBarrier.Error.isFault`) stays pending and unrecorded, and `ClusterFault` rejects the execution: the faulting operation is outside the history, which records every operation the object performed before it, and nothing is removed from the possible executions.

</details>

<a id="err-nonuniform-guard"></a>
#### warp-uniform control flow (`ERR-NONUNIFORM-GUARD`)

*Rule* · [Lean comment: `Core/Sync/WarpUniform.lean` L14-L149](../../Core/Sync/WarpUniform.lean#L14-L149)

When two threads of one warp (of one warpgroup for `setmaxnreg`) execute the same guarded instruction that requires a uniform guard, namely `bra.uni`, `brx.idx.uni`, `shfl.sync`, `vote.sync`, `redux.sync`, `match.sync` or an `.aligned` instruction (`Op.uniform`), and neither execution is ordered before the other, the two threads must evaluate the guard identically. Two such executions of a `brx.idx.uni` must also read the same index. Otherwise the execution is unsafe. A kernel assumption can exempt a `bra.uni` that tests the result of an `mbarrier.try_wait` poll.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Visit`](../../Core/Sync/WarpUniform.lean#L228-L237) ([concept](#c-visit)), [`uniIndex`](../../Core/Sync/WarpUniform.lean#L239-L243), [`visit`](../../Core/Sync/WarpUniform.lean#L245-L252), [`Walk`](../../Core/Sync/WarpUniform.lean#L268-L278) ([concept](#c-walk)), [`Visit.events`](../../Core/Sync/WarpUniform.lean#L282-L284), [`Visit.Disagree`](../../Core/Sync/WarpUniform.lean#L254-L258), [`Visit.disagree_noIndex`](../../Core/Sync/WarpUniform.lean#L260-L263), [`DepBeforeNode`](../../Core/Sync/WarpUniform.lean#L286-L293), [`DepBefore`](../../Core/Sync/WarpUniform.lean#L295-L298) ([concept](#c-depbefore)), [`VisitBefore`](../../Core/Sync/WarpUniform.lean#L300-L305), [`PollAgreeExempt`](../../Core/Sync/WarpUniform.lean#L307-L319), [`not_pollAgreeExempt`](../../Core/Sync/WarpUniform.lean#L321-L328), [`Kernel.uniformScopeAt`](../../Core/Sync/WarpUniform.lean#L330-L334), [`SameUniformGroup`](../../Core/Sync/WarpUniform.lean#L336-L339) ([concept](#c-sameuniformgroup)), [`WarpDivergent`](../../Core/Sync/WarpUniform.lean#L341-L352) ([concept](#c-warpdivergent)), [`warpDivergent_noPoll`](../../Core/Sync/WarpUniform.lean#L354-L365), [`UniformScope`](../../Core/Sync/WarpUniform.lean#L208-L211) ([concept](program.md#c-uniformscope)), [`Op.uniformScope`](../../Core/Sync/WarpUniform.lean#L213-L217), [`Op.uniform`](../../Core/Sync/WarpUniform.lean#L219-L226) ([concept](program.md#c-op-uniform))

<details>
<summary>Details for reviewers</summary>

- §9.7.14.3: "bra.uni is guaranteed to be non-divergent, i.e. all active threads in a warp that are
    currently executing this instruction have identical values for the guard predicate and branch
    target"
- §9.7.14.4: "brx.idx.uni guarantees that the branch is non-divergent, i.e. all active threads in a
    warp that are currently executing this instruction have identical values for the guard predicate
    and the index argument."
- §9.7.15.1: "In conditionally executed code, an aligned barrier{.cta} instruction should only be
    used if it is known that all threads in CTA evaluate the condition identically, otherwise
    behavior is undefined"
- §9.7.15.1 (read per EXT-BAR-PARTICIPANTS)
- §9.7.15.3: "The optional .aligned qualifier indicates that all threads in the warp must execute
    the same barrier.cluster instruction. In conditionally executed code, an aligned barrier.cluster
    instruction should only be used if it is known that all threads in the warp evaluate the
    condition identically, otherwise behavior is undefined"
- §9.7.18.7.1 and §9.7.18.8 (tcgen05 `.sync.aligned`)
- §9.7.21.5: "The mandatory .aligned qualifier indicates that all threads in the warpgroup must
    execute the same setmaxnreg instruction. In conditionally executed code, setmaxnreg instruction
    should only be used if it is known that all threads in warpgroup evaluate the condition
    identically, otherwise the behavior is undefined."
- §9.7.10.6 (shfl.sync): "Value of SourceA[lane] is unpredictable for // inactive/predicated-off
    threads in warp"
- §9.7.10.6 (shfl.sync): "Note that results are undefined if a thread sources a register from an
    inactive thread or a thread that is not in membermask ."
- §9.7.15.10 (vote.sync): "vote.sync will cause executing thread to wait until all non-exited
    threads corresponding to membermask have executed vote.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.15.11 (match.sync): "match.sync will cause executing thread to wait until all non-exited
    threads from membermask have executed match.sync with the same qualifiers and same membermask
    value before resuming execution."
- §9.7.15.13 (redux.sync): "Perform reduction operation on the data from each predicated active
    thread in the thread group."
- §9.7.16.5.15 (ldmatrix): "In conditionally executed code, an ldmatrix instruction should only be
    used if it is known that all threads in the warp evaluate the condition identically, otherwise
    the behavior is undefined."
- §9.7.16.5.16, §9.7.16.5.17, §9.7.16.5.14 and §9.7.16.6.3 (stmatrix, movmatrix, mma and mma.sp
    likewise)
- §9.7.17.1 (warpgroup)
- §9.5: "For divergent control flow, the optimizing code generator automatically determines points
    of re-convergence"
- §3.2 (Independent Thread Scheduling): "A schedule optimizer determines how to group active threads
    from the same warp together into SIMT units"
- EXT-DEPENDENCY-ORDER

**Applies:** Guarded `bra.uni`, `shfl.sync`, `vote.sync`, `redux.sync`, `match.sync` and `.aligned` instructions, and every `brx.idx.uni`

**Premises:** Two distinct threads of the instruction's uniform scope (`SameUniformGroup`: one warp; one warpgroup for `setmaxnreg`, `Op.uniformScope`) execute such an instruction (the same position), and neither execution is ordered before the other by the execution-dependency order (`VisitBefore`, `DepBefore`, EXT-DEPENDENCY-ORDER): the two executions may coincide.

**Effect:** Safety rejection (part of Unsafe). The instructions that require a uniform guard are those that `Op.uniform` selects, with the `.aligned` and `.uni` qualifiers as decoded, and the threads whose guards must agree are those of `Op.uniformScope`, as each instruction's text states: the warpgroup for `setmaxnreg`, the warp for `bra.uni`, `brx.idx.uni`, `barrier.cluster` and the `tcgen05` forms, and for an aligned `barrier{.cta}` the warp here and the barrier's participants in ERR-BARRIER-MISMATCH (EXT-BAR-PARTICIPANTS). Every decoded `tcgen05` resource, load/store and wait form and `setmaxnreg` carries `.sync.aligned` in its syntax, and so does every warp-level matrix instruction (`Op.matrix`). `bar.warp.sync`, `elect.sync`, `shfl.sync` and the asynchronous `tcgen05` operations are not aligned. `bar.arrive` is `barrier.arrive.aligned` and is aligned like `bar.sync`. A guarded `shfl.sync` also requires a warp-uniform guard: a lane whose guard is false takes part in the instance without a source value (§9.7.10.6), which DEP-WARP-SHUFFLE does not represent, so lanes that may execute it together with different guards are unsafe. This is stricter than the text, which leaves only the value read from such a lane unpredictable. A guarded `vote.sync` requires a warp-uniform guard for the same reason: the text does not say whether a lane of the member mask whose guard is false contributes to or waits for the instance (DEP-WARP-VOTE does not represent such a lane), so lanes that may execute it together with different guards are unsafe (stricter). A guarded `redux.sync` or `match.sync` requires a warp-uniform guard for the same reason (DEP-WARP-INSTANCE does not represent a lane of the member mask whose guard is false). `activemask` waits for no other lane and has no uniformity requirement. The exemption applies at a position that a kernel assumption selects with `uniPoll` (ASM-INTERFACE) when its instruction is a `bra.uni` guarded by the predicate that the `mbarrier.try_wait` right before it writes, and when the records of both lanes right before it are polls of one mbarrier, whatever their parities (`PollAgreeExempt`). The kernel's assumption ASM-POLL-AGREE then carries the guarantee. With no site selected, the rule is the one without this exemption (`warpDivergent_noPoll`). `Walk` follows one thread through every step it takes, local or not, on a prefix of its trace, and records each step (`Visit`): the instruction's source position, the guard's value when the instruction is guarded and requires a uniform guard, the event the step performs, and for a `brx.idx.uni` the index it reads (`uniIndex`). Two records of one position disagree (`Visit.Disagree`) when both have a guard value and the values differ, or both have an index and the indices differ. The index is recorded whether or not the guard holds, which is stricter than the text when both guards are false; a record whose index cannot be read (an index register that was never written) has none, and that read is a fault of its own when the branch is taken (THREAD-REG). Where no `brx.idx.uni` is executed, no record has an index and the rule compares guards only (`Visit.disagree_noIndex`). Which lanes are "currently executing this instruction" together is not fixed by the program: re-convergence points are chosen by the code generator (§9.5), and with Independent Thread Scheduling a schedule optimizer groups the active threads of a warp at sub-warp granularity (§3.2). A program must therefore be safe for every grouping. Two executions of one position by two lanes of a warp may coincide unless the execution-dependency order orders them (EXT-DEPENDENCY-ORDER): an event the first lane performs at or after its execution precedes, in `DepBefore`, an event the second lane performs before its execution (`VisitBefore`), in either direction. `DepBefore` is the dependency order of DEP-ORDER (`DepStep`: witnesses before returns, returns before the events that depend on them, the stage order) together with program order between issue nodes (`DepBeforeNode`). The rule compares every pair that it does not order; any grouping the scheduler may form consists of pairs of this kind. Both lanes execute the same position, so a `bra.uni` has the same target in both: the guard is the only value to compare. A `brx.idx.uni` takes its target from the index, so the index is compared as well. A lane that skips an aligned collective altogether is checked by ERR-ALIGNED-MISMATCH or leaves the collective pending. An unguarded `bra.uni` or aligned instruction has no guard to disagree on; the `.uni` qualifier does not change what a thread does (THREAD-BRANCH).

</details>

<a id="ext-dependency-order"></a>
##### executions ordered by blocking collectives are not executed together (`EXT-DEPENDENCY-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Sync/WarpUniform.lean` L151-L205](../../Core/Sync/WarpUniform.lean#L151-L205)

Two executions of one position by two threads are not executed together when an event the first thread performs at or after its execution precedes, in the execution-dependency order, an event the second thread performs before its execution. The execution-dependency order is the dependency order of DEP-ORDER (from each witness of a return to the return, and from a return to the later events of its thread that depend on it) together with program order between issue nodes; base causality (`baseCausality`) is not part of it. In the model: `DepBeforeNode`, `DepBefore`, `VisitBefore`.

Source:

- - §9.7.14.3: "bra.uni is guaranteed to be non-divergent, i.e. all active threads in a warp that are currently executing this instruction have identical values for the guard predicate and branch target" - §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to wait until all threads in the membermask execute the elect instruction before resuming execution." - §9.7.10.6: "shfl.sync will cause executing thread to wait until all non-exited threads corresponding to membermask have executed shfl.sync with the same qualifiers and same membermask value before resuming execution." - §9.7.15.10 - §9.7.15.11 and §9.7.15.13 (`vote.sync`, `match.sync`, `redux.sync`, as quoted in DEP-WARP-INSTANCE) - §9.7.15.2: "bar.warp.sync will cause executing thread to wait until all threads corresponding to membermask have executed a bar.warp.sync with the same membermask value before resuming execution." - §9.7.15.1: "the barrier{.cta}.red and barrier{.cta}.sync instructions causes executing thread to wait for non-exited threads of all other warps participating in the barrier to arrive." - §9.7.15.3: "barrier.cluster.wait instruction causes the executing thread to wait for all non-exited threads of the cluster to perform barrier.cluster.arrive" - §9.7.15.3: "In addition, barrier.cluster instructions cause the executing thread to wait for all non-exited threads from its warp." - §9.7.18.7.1 and §9.7.18.8: "The mandatory .sync qualifier indicates that the instruction causes the executing thread to wait until all threads in the warp execute the same instruction before resuming execution." - §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the executing thread to wait until all threads in the warp execute the same setmaxnreg instruction before resuming execution." - §3.2: "A schedule optimizer determines how to group active threads from the same warp together into SIMT units"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The blocking sentences order each participant's return after the arrivals it waits for, so an execution after a lane's return follows, in time, an execution before another lane's arrival. The text defines this waiting; it does not define which executions the hardware groups into one SIMT unit (§3.2). That executions ordered by the dependency order are not "currently executing this instruction" together (§9.7.14.3) is the reading. The dependency order orders no memory access: `DepBefore` enters neither `baseCausality`, `stageCausality` nor any memory rule.

**Effect:** It is used only in `VisitBefore` (ERR-NONUNIFORM-GUARD). Executions it does not order are still compared. A successful poll orders the later events of its thread only when it is a canonical spin (`SpinExit`, DEP-CANONICAL-SPIN). Disclosed by every kernel whose statement names `Op.bra (uni := true)`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.

</details>

<a id="err-warp-matrix"></a>
#### an instance whose result cannot be computed (`ERR-WARP-MATRIX`)

*Rule* · [Lean comment: `Core/Sync/MatrixExec.lean` L319-L343](../../Core/Sync/MatrixExec.lean#L319-L343)

An execution is unsafe when a lane of an instance of a warp-level matrix instruction receives a result that cannot be computed.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`MatrixUnsafe`](../../Core/Sync/MatrixExec.lean#L345-L348), [`not_matrixUnsafe_of_none`](../../Core/Sync/MatrixExec.lean#L350-L356)

<details>
<summary>Details for reviewers</summary>

- DEP-WARP-MATRIX (the instance and the result of each lane)
- DEP-WARP-MMA (the quoted undefined behaviour of invalid sparse metadata and selectors)
- §9.7.16.6.1: "Values 0b0000 , 0b0101 , 0b1010 , 0b1111 are invalid values for metadata and will
    result in undefined behavior."
- §9.7.16.6.1: "Hence, the sparsity selector in this case must be 0. Any other value of sparsity
    selector results in an undefined behavior."
- modelling choice: a lane result that the model cannot compute (an unknown byte, a missing
    numerical rule) is undefined behaviour of the instance; the text states undefined behaviour
    only for invalid sparse metadata and selectors (§9.7.16.6.1, quoted above)

**Applies:** Instances of the forms with THREAD-MATRIX and THREAD-MMA-SYNC

**Premises:** The instance exists (DEP-WARP-MATRIX).

**Effect:** Safety rejection (part of Unsafe). A result that cannot be computed (an unknown byte, a missing numerical rule, invalid sparse metadata) is undefined behaviour of the instance.

</details>
