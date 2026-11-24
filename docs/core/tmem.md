# Tensor Memory

How the model treats Tensor Memory: how each CTA's allocator allocates and deallocates columns, how relinquishing the permit and cta_group::2 pairs of CTAs work, when an access is covered by an allocation, and what counts as an error. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [The allocator and its operations](#the-allocator-and-its-operations)
    - [`Tmem.Region`](#c-tmem-region)
    - [`Tmem.State`](#c-tmem-state)
    - [`Tmem.Request`](#c-tmem-request)
    - [`Tmem.Action`](#c-tmem-action)
    - [`Tmem.Error`](#c-tmem-error)
    - [`Tmem.Outcome`](#c-tmem-outcome)
    - [`Tmem.validColumns`](#c-tmem-validcolumns)
    - [`Tmem.available`](#c-tmem-available)
    - [`Tmem.perform`](#c-tmem-perform)
  - [CTA groups and pairs](#cta-groups-and-pairs)
    - [`CtaGroup`](#c-ctagroup)
    - [`CtaInCluster`](#c-ctaincluster)
    - [`Launch.ctaGroupRanks`](#c-launch-ctagroupranks)
    - [`Launch.ctaGroup`](#c-launch-ctagroup)
    - [`SameCtaGroup`](#c-samectagroup)
  - [Requests, records and histories](#requests-records-and-histories)
    - [`Tmem.Pair.WarpRequest`](#c-tmem-pair-warprequest)
    - [`Tmem.Pair.Requests`](#c-tmem-pair-requests)
    - [`Tmem.Pair.compatible`](#c-tmem-pair-compatible)
    - [`Tmem.Pair.WarpRequest.Valid`](#c-tmem-pair-warprequest-valid)
    - [`Tmem.Pair.Requests.Valid`](#c-tmem-pair-requests-valid)
    - [`Tmem.Pair.PairValid`](#c-tmem-pair-pairvalid)
    - [`Execution`](#c-execution)
    - [`Tmem.Pair.runRequests`](#c-tmem-pair-runrequests)
    - [`Tmem.Pair.HistoriesOk`](#c-tmem-pair-historiesok)
    - [`Tmem.Pair.Precedes`](#c-tmem-pair-precedes)
    - [`Tmem.Pair.WarpRequest.Before`](#c-tmem-pair-warprequest-before)
  - [Performing, completing and returning](#performing-completing-and-returning)
    - [`Tmem.Pair.Participates`](#c-tmem-pair-participates)
    - [`Tmem.Pair.Performed`](#c-tmem-pair-performed)
    - [`Tmem.Pair.Completed`](#c-tmem-pair-completed)
    - [`Tmem.Pair.Covered`](#c-tmem-pair-covered)
    - [`Tmem.Pair.Drained`](#c-tmem-pair-drained)
    - [`Tmem.Pair.MustWait`](#c-tmem-pair-mustwait)
    - [`Tmem.Pair.CompletionReady`](#c-tmem-pair-completionready)
  - [Coverage and lifetimes](#coverage-and-lifetimes)
    - [`Tmem.Pair.Covers`](#c-tmem-pair-covers)
    - [`Tmem.Pair.PairAllocBefore`](#c-tmem-pair-pairallocbefore)
    - [`Tmem.Pair.FreshAfter`](#c-tmem-pair-freshafter)
    - [`Tmem.Pair.OwnRelease`](#c-tmem-pair-ownrelease)
    - [`Tmem.Pair.ReleaseOf`](#c-tmem-pair-releaseof)
  - [Safety](#safety)
    - [`Tmem.Pair.ResourceUnsafe`](#c-tmem-pair-resourceunsafe)
    - [`Tmem.Pair.PendingReleaseAlloc`](#c-tmem-pair-pendingreleasealloc)
    - [`Tmem.Pair.Access`](#c-tmem-pair-access)
    - [`Tmem.Pair.AccessUnsafe`](#c-tmem-pair-accessunsafe)
    - [`Tmem.Pair.Released`](#c-tmem-pair-released)
    - [`Tmem.Pair.ReleaseUnsafe`](#c-tmem-pair-releaseunsafe)
- [Rules](#rules)
  - [What an allocation-management instruction does](#what-an-allocation-management-instruction-does)
    - [non-exclusive Tensor Memory allocation lifetimes](#obj-tmem-allocator) (`OBJ-TMEM-ALLOCATOR`)
      - [lane 0 stores the allocated address with a generic-proxy weak store](#ext-tcalloc-storer) (`EXT-TCALLOC-STORER`)
    - [collective resource operations of a CTA group](#obj-tmem-pair) (`OBJ-TMEM-PAIR`)
    - [warp instruction instances and allocator records](#obj-tmem-request) (`OBJ-TMEM-REQUEST`)
    - [actual warp participants of a resource operation](#obj-tmem-requests) (`OBJ-TMEM-REQUESTS`)
    - [the operations a CTA's allocator performs](#obj-tmem-history) (`OBJ-TMEM-HISTORY`)
    - [the column an allocation returns](#obj-tmem-alloc-result) (`OBJ-TMEM-ALLOC-RESULT`)
    - [actual participants and bytes of the allocation result](#mem-tmem-result-handoff) (`MEM-TMEM-RESULT-HANDOFF`)
      - [visibility of a warp's local allocation result](#ext-tmem-alloc-result-order) (`EXT-TMEM-ALLOC-RESULT-ORDER`)
    - [what an allocation-management instruction waits for](#dep-tmem-alloc-wait) (`DEP-TMEM-ALLOC-WAIT`)
  - [Which executions are allowed](#which-executions-are-allowed)
    - [the execution order of one CTA's allocator](#obj-tmem-order) (`OBJ-TMEM-ORDER`)
      - [a CTA's allocator performs its requests by their return, in an order that follows causality](#ext-tmem-alloc-order) (`EXT-TMEM-ALLOC-ORDER`)
    - [allocator histories and pairings belong to their CTAs](#obj-tmem-origin) (`OBJ-TMEM-ORIGIN`)
    - [performed halves, completed and pending resource operations](#obj-tmem-complete-operations) (`OBJ-TMEM-COMPLETE-OPERATIONS`)
    - [synchronous resource completion prefixes](#obj-tmem-completion-prefix) (`OBJ-TMEM-COMPLETION-PREFIX`)
    - [a paired allocation published through the peer warp](#obj-tmem-publication) (`OBJ-TMEM-PUBLICATION`)
      - [a paired allocation is complete when the peer warp's returns](#ext-pair-alloc-order) (`EXT-PAIR-ALLOC-ORDER`)
    - [allocation coverage and first release attempts](#obj-tmem-lifetime) (`OBJ-TMEM-LIFETIME`)
  - [What counts as an error](#what-counts-as-an-error)
    - [a fault of a CTA's Tensor Memory allocator](#err-tmem-resource) (`ERR-TMEM-RESOURCE`)
    - [allocation and completion of every Tensor Memory access](#err-tmem-access-lifetime) (`ERR-TMEM-ACCESS-LIFETIME`)
    - [no live allocations at kernel completion](#err-tmem-not-released) (`ERR-TMEM-NOT-RELEASED`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### The allocator and its operations

The state of one CTA's Tensor Memory allocator and the effect of each allocation-management operation on it.

<a id="c-tmem-region"></a>
#### `Tmem.Region`

*structure*

One live allocation of a CTA's Tensor Memory: its lifetime id, its first column and its
column count.

- `lifetime`: A fresh number for each successful allocation. It is proof metadata, not a PTX value.
- `base`: The first column of the allocation, the address that `tcgen05.alloc` returns.
- `columns`: The number of allocated columns.

[Lean source: `Core/Tmem/TmemObject.lean` L51-L60](../../Core/Tmem/TmemObject.lean#L51-L60)

<a id="c-tmem-state"></a>
#### `Tmem.State`

*structure*

The state of one CTA's Tensor Memory allocator (§9.7.18.7.1).

- `permit`: Whether the CTA still holds the right to allocate. `tcgen05.relinquish_alloc_permit` clears it.
- `previousColumns`: The column count of the previous allocation; later allocations may not request more.
- `nextLifetime`: The lifetime id that the next allocation receives.
- `live`: The live allocations, in allocation order.

[Lean source: `Core/Tmem/TmemObject.lean` L62-L73](../../Core/Tmem/TmemObject.lean#L62-L73)

<a id="c-tmem-request"></a>
#### `Tmem.Request`

*inductive*

An allocation-management instruction's operands: an allocation's column count, a release's
address and column count, or permit relinquishment.

- `alloc`
- `dealloc`
- `relinquish`

[Lean source: `Core/Tmem/TmemObject.lean` L75-L81](../../Core/Tmem/TmemObject.lean#L75-L81)

<a id="c-tmem-action"></a>
#### `Tmem.Action`

*inductive*

The transition that the allocator performs for one request: an allocation of `columns`
columns at the column `base` that the allocator selected, a deallocation, or relinquishment of
the permit.

- `alloc`: `base` is the allocation result chosen by the allocator.
- `dealloc`
- `relinquish`

[Lean source: `Core/Tmem/TmemObject.lean` L83-L91](../../Core/Tmem/TmemObject.lean#L83-L91)

<a id="c-tmem-error"></a>
#### `Tmem.Error`

*inductive*

An allocator fault, each of which the ISA makes undefined behaviour.

- `invalidColumns`: A column count other than 32, 64, 128, 256 or 512.
- `increasingRequest`: An allocation requests more columns than the previous allocation of the CTA.
- `relinquishedPermit`: An allocation after the CTA relinquished its allocation permit.
- `unmatchedRelease`: No live whole allocation matches this release.

[Lean source: `Core/Tmem/TmemObject.lean` L99-L109](../../Core/Tmem/TmemObject.lean#L99-L109)

<a id="c-tmem-outcome"></a>
#### `Tmem.Outcome`

*inductive*

The result of one allocator transition: the next state, a blocked allocation that cannot
complete in this state, or a fault.

- `done`
- `blocked`
- `fault`

[Lean source: `Core/Tmem/TmemObject.lean` L111-L117](../../Core/Tmem/TmemObject.lean#L111-L117)

<a id="c-tmem-validcolumns"></a>
#### `Tmem.validColumns`

*def*

Column counts of a non-exclusive allocation (Table 58; §9.7.18.7.1: "the operand nCols must be
a power of 2, in the range [32, 512]"). Used by the `tcgen05.alloc`/`dealloc` instruction rule and
by `perform`.

[Lean source: `Core/Tmem/TmemObject.lean` L119-L122](../../Core/Tmem/TmemObject.lean#L119-L122)

<a id="c-tmem-available"></a>
#### `Tmem.available`

*def*

Candidate result columns lie within the address space and avoid live regions.
The allocation size, rather than an extra alignment assumption on the returned
address, is checked by `validColumns`.

[Lean source: `Core/Tmem/TmemObject.lean` L128-L132](../../Core/Tmem/TmemObject.lean#L128-L132)

<a id="c-tmem-perform"></a>
#### `Tmem.perform`

*def*

The effect of one action on an allocator state. An allocation faults on an invalid column
count, after relinquishment of the permit, or when it requests more columns than the previous
allocation; it blocks when its selected range is not available, and otherwise adds a region with
a fresh lifetime id. A deallocation faults on an invalid column count or when no live region has
its address and column count, and otherwise removes that region. Relinquishment clears the
permit.

[Lean source: `Core/Tmem/TmemObject.lean` L134-L155](../../Core/Tmem/TmemObject.lean#L134-L155)

### CTA groups and pairs

The CTAs that take part in one operation: a single CTA for cta_group::1, an even/odd CTA pair for cta_group::2.

<a id="c-ctagroup"></a>
#### `CtaGroup`

*inductive*

The `.cta_group` qualifier: an aligned block of one or two cluster ranks.

- `one`
- `two`

[Lean source: `Core/Isa/Tc.lean` L86-L89](../../Core/Isa/Tc.lean#L86-L89)

<a id="c-ctaincluster"></a>
#### `CtaInCluster`

*def*

CTAs `issuer` and `cta` are CTAs of the grid in the same cluster.

[Lean source: `Core/Tmem/CtaPair.lean` L39-L41](../../Core/Tmem/CtaPair.lean#L39-L41)

<a id="c-launch-ctagroupranks"></a>
#### `Launch.ctaGroupRanks`

*def*

The cluster ranks of the CTA group of CTA `cta`: the aligned block of `group.size` ranks that
contains the rank of `cta` in its own cluster. A block has one rank for cta_group::1, and for
cta_group::2 an even rank followed by the next odd rank (a CTA pair, §9.7.18.5.1). The ranks are
relative to the cluster of `cta`, which is a CTA of the 3-D cluster model of the launch.

[Lean source: `Core/Tmem/CtaPair.lean` L43-L48](../../Core/Tmem/CtaPair.lean#L43-L48)

<a id="c-launch-ctagroup"></a>
#### `Launch.ctaGroup`

*def*

The CTAs of the CTA group of CTA `cta`, in rank order (the even-rank CTA of a pair first), or
none when a rank of the group has no CTA in the cluster of `cta`.

[Lean source: `Core/Tmem/CtaPair.lean` L50-L53](../../Core/Tmem/CtaPair.lean#L50-L53)

<a id="c-samectagroup"></a>
#### `SameCtaGroup`

*def*

CTAs `a` and `b` are in the same cluster and in the same CTA group of size `group.size`:
the cluster rank of `b` is one of the ranks of the group of `a`.

[Lean source: `Core/Tmem/CtaPair.lean` L55-L58](../../Core/Tmem/CtaPair.lean#L55-L58)

### Requests, records and histories

The warp instances of an allocation-management instruction, the records each CTA's allocator keeps, and the parts of an execution that hold them.

<a id="c-tmem-pair-warprequest"></a>
#### `Tmem.Pair.WarpRequest`

*structure*

One warp-collective allocation-management instruction instance (`tcgen05.alloc`,
`dealloc` or `relinquish_alloc_permit`): its CTA, warp, the trace position of each lane, the
source position, the destination of an allocation's address, and the request.

- `cta`
- `warp`
- `indices`
- `pc`
- `dst`
- `request`

[Lean source: `Core/Data/TmemPairTypes.lean` L32-L41](../../Core/Data/TmemPairTypes.lean#L32-L41)

<a id="c-tmem-pair-requests"></a>
#### `Tmem.Pair.Requests`

*structure*

One operation performed by a CTA's allocator: the CTA's warp request, its group, and the
action performed for it.

- `own`
- `group`
- `action`

[Lean source: `Core/Data/TmemPairTypes.lean` L46-L51](../../Core/Data/TmemPairTypes.lean#L46-L51)

<a id="c-tmem-pair-compatible"></a>
#### `Tmem.Pair.compatible`

*def*

The two requests of a cta_group::2 operation agree: both allocate the same column count,
both deallocate the same column count, or both relinquish the permit. The deallocation addresses
are not compared, since each CTA has its own allocation result.

[Lean source: `Core/Tmem/TmemPair.lean` L43-L49](../../Core/Tmem/TmemPair.lean#L43-L49)

<a id="c-tmem-pair-warprequest-valid"></a>
#### `Tmem.Pair.WarpRequest.Valid`

*def*

Warp request `w` is an actual instruction instance of group `group`: the CTA and warp exist
in the launch, every lane's event at its trace index is that instruction with the request's
operands, and the 32 lane events form one warp-collective instance.

[Lean source: `Core/Tmem/TmemPairRequests.lean` L41-L47](../../Core/Tmem/TmemPairRequests.lean#L41-L47)

<a id="c-tmem-pair-requests-valid"></a>
#### `Tmem.Pair.Requests.Valid`

*def*

Allocator record `r` is valid: the launch has valid clusters, its action performs its warp's
request, and that warp request is an actual instance of the record's group.

[Lean source: `Core/Tmem/TmemPairRequests.lean` L49-L52](../../Core/Tmem/TmemPairRequests.lean#L49-L52)

<a id="c-tmem-pair-pairvalid"></a>
#### `Tmem.Pair.PairValid`

*def*

The two warp requests of a cta_group::2 operation are valid: both are actual cta_group::2
instances, of the two distinct CTAs of one CTA pair with the even-ranked CTA's first, and their
requests agree (`compatible`).

[Lean source: `Core/Tmem/TmemPairRequests.lean` L54-L60](../../Core/Tmem/TmemPairRequests.lean#L54-L60)

<a id="c-execution"></a>
#### `Execution`

*structure*

One candidate execution of a kernel (MEM-EXECUTION): the thread traces, reads-from, the
asynchronous effects, and the histories of the synchronization objects.

- `tmemHistory`: Each CTA's Tensor Memory allocator history, indexed by the CTA's grid id.
- `tmemPairing`: The completed cta_group::2 operations: the even CTA's and the odd CTA's warp requests.
- `tmemPairBlocks`: Nondeterministic peer-wait choice of cta_group::2 dealloc/relinquish instances (DEP-TMEM-ALLOC-WAIT); other instances ignore it. Choices on issued requests are preserved by extension.

[Lean source: `Core/Data/Types.lean` L326-L365](../../Core/Data/Types.lean#L326-L365)

<a id="c-tmem-pair-runrequests"></a>
#### `Tmem.Pair.runRequests`

*def*

Replay one allocator's history. Faults are retained, so malformed programs do not disappear
by having no successful resource execution.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L58-L66](../../Core/Tmem/TmemPairHistory.lean#L58-L66)

<a id="c-tmem-pair-historiesok"></a>
#### `Tmem.Pair.HistoriesOk`

*def*

The allocator histories and pairings of an execution are well formed: each CTA's history
holds valid records of that CTA and its replay does not block, each pairing is valid and pairs
two recorded cta_group::2 requests, and no request is paired twice.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L96-L105](../../Core/Tmem/TmemPairHistory.lean#L96-L105)

<a id="c-tmem-pair-precedes"></a>
#### `Tmem.Pair.Precedes`

*def*

`i` is a lane event of an earlier record of CTA `cta`'s history than `j`.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L336-L340](../../Core/Tmem/TmemPairHistory.lean#L336-L340)

<a id="c-tmem-pair-warprequest-before"></a>
#### `Tmem.Pair.WarpRequest.Before`

*def*

Warp request `a` comes before `b` in the program order of one warp: same CTA and warp, and
every lane's event of `a` precedes that lane's event of `b`.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L49-L52](../../Core/Tmem/TmemPairHistory.lean#L49-L52)

### Performing, completing and returning

When a request is performed, when an operation is complete, and what an instruction waits for before it returns.

<a id="c-tmem-pair-participates"></a>
#### `Tmem.Pair.Participates`

*def*

`i` is a lane event of warp request `w`.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L178-L180](../../Core/Tmem/TmemPairHistory.lean#L178-L180)

<a id="c-tmem-pair-performed"></a>
#### `Tmem.Pair.Performed`

*def*

`i` is a lane event of a request that its CTA's allocator has performed.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L182-L184](../../Core/Tmem/TmemPairHistory.lean#L182-L184)

<a id="c-tmem-pair-completed"></a>
#### `Tmem.Pair.Completed`

*def*

The warp requests of a complete operation: a performed cta_group::1 request, or a pairing.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L186-L189](../../Core/Tmem/TmemPairHistory.lean#L186-L189)

<a id="c-tmem-pair-covered"></a>
#### `Tmem.Pair.Covered`

*def*

`i` is a lane event of a complete operation.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L191-L193](../../Core/Tmem/TmemPairHistory.lean#L191-L193)

<a id="c-tmem-pair-drained"></a>
#### `Tmem.Pair.Drained`

*def*

Every allocation-management event of the execution is covered: no request is pending.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L195-L197](../../Core/Tmem/TmemPairHistory.lean#L195-L197)

<a id="c-tmem-pair-mustwait"></a>
#### `Tmem.Pair.MustWait`

*def*

The return of `i` waits for its whole operation: an allocation, a cta_group::1 instruction,
or a cta_group::2 deallocation or relinquishment whose peer-wait choice is set.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L424-L430](../../Core/Tmem/TmemPairHistory.lean#L424-L430)

<a id="c-tmem-pair-completionready"></a>
#### `Tmem.Pair.CompletionReady`

*def*

Every earlier actual request of a warp of an operation is covered.

[Lean source: `Core/Tmem/TmemPairCompletion.lean` L40-L42](../../Core/Tmem/TmemPairCompletion.lean#L40-L42)

### Coverage and lifetimes

Which allocation covers an access to a Tensor Memory cell, which deallocations end that allocation, and when a later allocation starts a fresh lifetime.

<a id="c-tmem-pair-covers"></a>
#### `Tmem.Pair.Covers`

*def*

Record `r` is an allocation of CTA `owner` whose column range contains `col`, published to
`e`: lane 0's allocation event happens before `e`, or the record is paired and an event of the
peer's paired request happens before `e` (EXT-PAIR-ALLOC-ORDER).

[Lean source: `Core/Tmem/TmemPairLifetime.lean` L110-L116](../../Core/Tmem/TmemPairLifetime.lean#L110-L116)

<a id="c-tmem-pair-pairallocbefore"></a>
#### `Tmem.Pair.PairAllocBefore`

*def*

EXT-PAIR-ALLOC-ORDER: the request of record `r` is paired with a request of the peer CTA, and
an event of that request happens before `e`.

[Lean source: `Core/Tmem/TmemPairLifetime.lean` L66-L70](../../Core/Tmem/TmemPairLifetime.lean#L66-L70)

<a id="c-tmem-pair-freshafter"></a>
#### `Tmem.Pair.FreshAfter`

*def*

Release attempt `d` is followed by a fresh lifetime of the cell for access `e`: some
allocation covers the cell for `e`, and `d` happens before that allocation's event.

[Lean source: `Core/Tmem/TmemPairLifetime.lean` L134-L137](../../Core/Tmem/TmemPairLifetime.lean#L134-L137)

<a id="c-tmem-pair-ownrelease"></a>
#### `Tmem.Pair.OwnRelease`

*def*

A release attempt of the allocation of record `r` by its own CTA: the first matching
deallocation in a lane of its warp after it, or a matching deallocation by another warp of its
CTA. It need not yet have been performed.

[Lean source: `Core/Tmem/TmemPairLifetime.lean` L139-L149](../../Core/Tmem/TmemPairLifetime.lean#L139-L149)

<a id="c-tmem-pair-releaseof"></a>
#### `Tmem.Pair.ReleaseOf`

*def*

A release attempt of the allocation of `r`: its own, or that of the peer CTA's record of a
paired operation.

[Lean source: `Core/Tmem/TmemPairLifetime.lean` L151-L155](../../Core/Tmem/TmemPairLifetime.lean#L151-L155)

### Safety

The executions that are rejected as unsafe because of Tensor Memory.

<a id="c-tmem-pair-resourceunsafe"></a>
#### `Tmem.Pair.ResourceUnsafe`

*def*

An allocator fault: the replay of some CTA's history faults, or an allocation in some CTA's
history follows a paired cta_group::2 deallocation whose peer request does not causally precede
it (`PendingReleaseAlloc`).

[Lean source: `Core/Tmem/TmemPairHistory.lean` L145-L150](../../Core/Tmem/TmemPairHistory.lean#L145-L150)

<a id="c-tmem-pair-pendingreleasealloc"></a>
#### `Tmem.Pair.PendingReleaseAlloc`

*def*

In CTA `cta`'s history an allocation follows a paired cta_group::2 deallocation whose peer
request does not causally precede it.

[Lean source: `Core/Tmem/TmemPairHistory.lean` L137-L143](../../Core/Tmem/TmemPairHistory.lean#L137-L143)

<a id="c-tmem-pair-access"></a>
#### `Tmem.Pair.Access`

*def*

Event `e` accesses Tensor Memory cell `cell`: an MMA its written and accumulator cells, a
load or store the cells of its registers, a copy the cells of its copied words.

[Lean source: `Core/Tmem/TmemPairAccess.lean` L56-L60](../../Core/Tmem/TmemPairAccess.lean#L56-L60)

<a id="c-tmem-pair-accessunsafe"></a>
#### `Tmem.Pair.AccessUnsafe`

*def*

Some Tensor Memory access is unallocated or may still be in flight at a release attempt.

[Lean source: `Core/Tmem/TmemPairAccess.lean` L72-L73](../../Core/Tmem/TmemPairAccess.lean#L72-L73)

<a id="c-tmem-pair-released"></a>
#### `Tmem.Pair.Released`

*def*

Every CTA's allocator history that replays without fault ends with no live allocation.

[Lean source: `Core/Tmem/TmemPairRelease.lean` L38-L40](../../Core/Tmem/TmemPairRelease.lean#L38-L40)

<a id="c-tmem-pair-releaseunsafe"></a>
#### `Tmem.Pair.ReleaseUnsafe`

*def*

A finished execution in which some CTA still holds Tensor Memory: all threads have exited,
all allocation-management operations are complete, and some allocator still has a live
allocation.

[Lean source: `Core/Tmem/TmemPairRelease.lean` L42-L46](../../Core/Tmem/TmemPairRelease.lean#L42-L46)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### What an allocation-management instruction does

The allocator of one CTA, the warps that issue each operation, the column an allocation returns and what an instruction waits for.

<a id="obj-tmem-allocator"></a>
#### non-exclusive Tensor Memory allocation lifetimes (`OBJ-TMEM-ALLOCATOR`)

*Rule* · [Lean comment: `Core/Tmem/TmemObject.lean` L10-L48](../../Core/Tmem/TmemObject.lean#L10-L48)

Each CTA's Tensor Memory allocator holds a list of live allocations in a 512-column address space; an allocation completes only with a range of free columns inside that space, and a deallocation removes the live allocation with its address and column count. A `Request` is what the instruction names (its operands), and an `Action` is the transition the allocator performs for it. `Action.alloc` adds the column the allocator selects when the allocation completes, and it adds no extra PTX operand. Each successful allocation gets a fresh logical lifetime id, including reuse of the same returned address. An allocator fault occurs when a column count is not 32, 64, 128, 256 or 512, when an allocation requests more columns than the previous allocation of the CTA, when an allocation follows relinquishment of the permit, or when a deallocation matches no live allocation.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Tmem.Region`](../../Core/Tmem/TmemObject.lean#L51-L60) ([concept](#c-tmem-region)), [`Tmem.State`](../../Core/Tmem/TmemObject.lean#L62-L73) ([concept](#c-tmem-state)), [`Tmem.Request`](../../Core/Tmem/TmemObject.lean#L75-L81) ([concept](#c-tmem-request)), [`Tmem.Action`](../../Core/Tmem/TmemObject.lean#L83-L91) ([concept](#c-tmem-action)), [`Tmem.Action.request`](../../Core/Tmem/TmemObject.lean#L93-L97), [`Tmem.Error`](../../Core/Tmem/TmemObject.lean#L99-L109) ([concept](#c-tmem-error)), [`Tmem.Outcome`](../../Core/Tmem/TmemObject.lean#L111-L117) ([concept](#c-tmem-outcome)), [`Tmem.validColumns`](../../Core/Tmem/TmemObject.lean#L119-L122) ([concept](#c-tmem-validcolumns)), [`Tmem.disjoint`](../../Core/Tmem/TmemObject.lean#L124-L126), [`Tmem.available`](../../Core/Tmem/TmemObject.lean#L128-L132) ([concept](#c-tmem-available)), [`Tmem.perform`](../../Core/Tmem/TmemObject.lean#L134-L155) ([concept](#c-tmem-perform))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.1
- §9.7.18.7.1, Table 58

**Applies:** A CTA's non-exclusive 512-column Tensor Memory address space; whole-allocation releases

**Premises:** Allocation request sizes are valid, non-increasing and made before relinquishing the permit. A successful allocation selects an available range; a release identifies a live allocation of the same size.

**Effect:** Local object transitions replayed by OBJ-TMEM-HISTORY. Physical resource progress is a separate obligation. `blocked` says that this candidate cannot complete in the current local resource state; it does not assert that no other candidate is available and promises no physical progress.

</details>

<a id="ext-tcalloc-storer"></a>
##### lane 0 stores the allocated address with a generic-proxy weak store (`EXT-TCALLOC-STORER`)

*Interpretation (EXT)* · [Lean comment: `Core/Tc/TcThread.lean` L143-L185](../../Core/Tc/TcThread.lean#L143-L185)

Of the threads of a warp that execute `tcgen05.alloc`, only lane 0 stores the returned Tensor Memory address to the shared `dst`, with one weak 32-bit generic-proxy store after its own allocation event. The store is an ordinary thread write. Reads of it are ordered only by the existing rules (MEM-MODEL-CAUSALITY `modelCausality`, MEM-READ-AXIOMS `Hidden`, the conflicting-access checks ERR-DATA-RACE and ERR-MIXED-SIZE).

Source:

- - §9.7.18.7.1: "The store operation in tcgen05.alloc is treated as a weak memory operation in the Memory Consistency Model" - §8.6: "Unless otherwise specified, memory operations as defined in Operation types use generic method of memory access, i.e. a generic proxy ." - §9.7.18.6.5 (only the shared-memory accesses of `tcgen05.mma` and `tcgen05.cp` are performed in the async proxy)

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text says that the instruction has a store and that it is weak. It does not say which thread of the warp performs it (one lane, every lane, or the executing thread of each lane). It names no proxy for this store. The model chooses lane 0, so that the store is one event ordered after that lane's allocation by program order. It chooses the generic proxy, the §8.6 default for an operation whose proxy is not otherwise specified.

**Effect:** If the hardware store is performed by another lane, by every lane or through another proxy, a read of the address that the model orders after the store through lane 0's program order, or through synchronization that starts at lane 0, may not be ordered after it on hardware, and the value read is then not determined. The model does not report that. A program in which every lane reads the address only after the whole allocating warp has synchronized does not depend on which lane writes. Disclosed by every kernel whose statement names `Op.tcAlloc`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

</details>

<a id="obj-tmem-pair"></a>
#### collective resource operations of a CTA group (`OBJ-TMEM-PAIR`)

*Rule* · [Lean comment: `Core/Tmem/TmemPair.lean` L10-L40](../../Core/Tmem/TmemPair.lean#L10-L40)

The two warp requests of a cta_group::2 allocation-management operation, one in each CTA of the pair, are of the same kind, and for an allocation or a deallocation they name the same column count. The Tensor Memory addresses of the two deallocations may differ. Each CTA's allocator performs its own warp's request, at its own address and lifetime, in the execution order within that CTA (OBJ-TMEM-ORDER), and the operation completes when the allocators of both CTAs have performed it.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.compatible`](../../Core/Tmem/TmemPair.lean#L43-L49) ([concept](#c-tmem-pair-compatible))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5 (collective issue, potentially blocking deallocation)
- §9.7.18.7.1: "When .cta_group::1 is specified, one warp from the CTA must perform the allocation
    and de-allocation. When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."

**Applies:** Non-exclusive allocations, whole-allocation releases and permit relinquishment of a CTA group: one CTA for cta_group::1, an even/odd CTA pair for cta_group::2

**Premises:** An execution adapter supplies actual warp requests of every CTA of the group and proves their agreement. Local resource validity is checked by Tmem.perform.

**Effect:** Request agreement; OBJ-TMEM-HISTORY and OBJ-TMEM-ORIGIN connect allocator records and pairings to executions.

</details>

<a id="obj-tmem-request"></a>
#### warp instruction instances and allocator records (`OBJ-TMEM-REQUEST`)

*Rule* · [Lean comment: `Core/Data/TmemPairTypes.lean` L11-L30](../../Core/Data/TmemPairTypes.lean#L11-L30)

A Tensor Memory allocation-management instruction is recorded as one warp request, which names the CTA, warp, the trace position of each lane and the request. The allocator of each CTA records the requests it served with the action it took, and the two warp requests of a `cta_group::2` operation are paired separately.

Source:

- 

Direction: `representation` (the entry defines an encoding)

Lean definitions: [`Tmem.Pair.WarpRequest`](../../Core/Data/TmemPairTypes.lean#L32-L41) ([concept](#c-tmem-pair-warprequest)), [`Tmem.Pair.WarpRequest.event`](../../Core/Data/TmemPairTypes.lean#L43-L44), [`Tmem.Pair.Requests`](../../Core/Data/TmemPairTypes.lean#L46-L51) ([concept](#c-tmem-pair-requests))

<details>
<summary>Details for reviewers</summary>

- none (representation)

**Applies:** Allocator records of one CTA and the pairing of the two warp requests of a cta_group::2 operation

**Premises:** None; actual participants and operation agreement are checked by OBJ-TMEM-REQUESTS and OBJ-TMEM-ORIGIN.

**Effect:** Data only.

</details>

<a id="obj-tmem-requests"></a>
#### actual warp participants of a resource operation (`OBJ-TMEM-REQUESTS`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairRequests.lean` L11-L39](../../Core/Tmem/TmemPairRequests.lean#L11-L39)

Each allocation-management operation that an allocator records is issued by one full warp of the CTA, whose 32 lanes execute one warp-collective instance of the same instruction with the same operands, and the record performs that request. The two warps of a cta_group::2 operation are in the two distinct CTAs of one CTA pair of a valid cluster launch, the even-ranked CTA first, and their requests agree. Each side of a pair keeps its own source position, warp index, local address and trace indices.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Tmem.Pair.WarpRequest.Valid`](../../Core/Tmem/TmemPairRequests.lean#L41-L47) ([concept](#c-tmem-pair-warprequest-valid)), [`Tmem.Pair.Requests.Valid`](../../Core/Tmem/TmemPairRequests.lean#L49-L52) ([concept](#c-tmem-pair-requests-valid)), [`Tmem.Pair.PairValid`](../../Core/Tmem/TmemPairRequests.lean#L54-L60) ([concept](#c-tmem-pair-pairvalid))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5 (one warp per peer CTA)
- §9.7.18.7.1 (.sync/.aligned and operands)

**Applies:** Actual allocation-management events of one complete warp per CTA of the group

**Premises:** Each warp's 32 lane instances exist, are the same warp-collective instance (DEP-TC-COLLECTIVE), agree on source instruction and request, and belong to that CTA. An allocator record's action performs its warp's request. A pairing's two warp requests are of distinct peer CTAs of one CTA pair in a valid cluster launch, the first of the even CTA, with compatible requests.

**Effect:** An execution-adapter component.

</details>

<a id="obj-tmem-history"></a>
#### the operations a CTA's allocator performs (`OBJ-TMEM-HISTORY`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L12-L47](../../Core/Tmem/TmemPairHistory.lean#L12-L47)

Each CTA's allocator has a finite history of the operations it performed, one record per performed warp request, each with actual lane events. Replaying the history from an empty allocator through the allocator transitions gives the CTA's Tensor Memory allocation state, or the first blocked allocation or fault. A CTA's history holds the operations its allocator performed. Pending requests and the pairing of a cta_group::2 operation are represented separately (OBJ-TMEM-COMPLETE-OPERATIONS). The history order is the execution order of OBJ-TMEM-ORDER: it contains causality order between the requests of the CTA, and requests that causality does not order may appear in either order, so a fault in either order is reported. No global order on memory events and no order between two CTAs' allocators is imposed.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Tmem.Pair.WarpRequest.Before`](../../Core/Tmem/TmemPairHistory.lean#L49-L52) ([concept](#c-tmem-pair-warprequest-before)), [`Tmem.Pair.RequestHistory`](../../Core/Tmem/TmemPairHistory.lean#L54-L56), [`Tmem.Pair.runRequests`](../../Core/Tmem/TmemPairHistory.lean#L58-L66) ([concept](#c-tmem-pair-runrequests))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5
- §9.7.18.6.1 (synchronous allocation management)
- §9.7.18.7.1: "When .cta_group::1 is specified, one warp from the CTA must perform the allocation
    and de-allocation. When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."

**Applies:** The finite history of each CTA's allocator: the requests of its warps it performed, in its execution order; different operations may be performed by different warps

**Premises:** Each record has actual matching lane events. Each allocator begins empty.

**Effect:** RequestHistory checks event provenance; runRequests replays one allocator's resource effects.

</details>

<a id="obj-tmem-alloc-result"></a>
#### the column an allocation returns (`OBJ-TMEM-ALLOC-RESULT`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L342-L365](../../Core/Tmem/TmemPairHistory.lean#L342-L365)

The Tensor Memory address that an allocating warp writes to shared memory is the column that its CTA's allocator selected when it performed the allocation.

Source:

- 

Direction: `equal` (the entry claims to follow its cited text)

Lean definitions: [`Tmem.Pair.ResultOk`](../../Core/Tmem/TmemPairHistory.lean#L367-L373)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.7.1: "tcgen05.alloc is a blocking instruction which dynamically allocates the specified
    number of columns in the Tensor Memory and writes the address of the allocated Tensor Memory
    into shared memory at the location specified by address operand dst ."
- §9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not available
    and unblocks as soon as the requested amount of Tensor Memory becomes available for allocation."

**Applies:** Allocations of either cta_group performed by their CTA's allocator

**Premises:** A performed allocation is recorded with the column its CTA's allocator selected; OBJ-TMEM-ORIGIN checks that the columns are available where it is performed. The store of the address is lane 0's second event of the instruction (THREAD-TC).

**Effect:** Consistency constraint. An allocation that has not been performed has no column: its request event names only the column count, so a pending allocation may wait while the columns are held, and the column is selected when it is performed.

</details>

<a id="mem-tmem-result-handoff"></a>
#### actual participants and bytes of the allocation result (`MEM-TMEM-RESULT-HANDOFF`)

*Rule* · [Lean comment: `Core/Tmem/AllocResult.lean` L10-L28](../../Core/Tmem/AllocResult.lean#L10-L28)

The local handoff relates the allocation instruction's representative result store to an ordinary load of the same byte by one of the instruction's participants.

Source:

- - EXT-TMEM-ALLOC-RESULT-ORDER

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.AllocResult`](../../Core/Tmem/AllocResult.lean#L64-L75), [`Tmem.Pair.AllocResultBefore`](../../Core/Tmem/AllocResult.lean#L77-L82)

<details>
<summary>Details for reviewers</summary>

**Applies:** Ordinary shared-memory loads by a lane of an allocating warp.

**Premises:** Matching warp lane events name the same allocation instance. The representative four-byte store and the later load cover the byte.

**Effect:** Supplies the local result-write node of DEP-ORDER and the byte edge of MEM-MODEL-CAUSALITY.

</details>

<a id="ext-tmem-alloc-result-order"></a>
##### visibility of a warp's local allocation result (`EXT-TMEM-ALLOC-RESULT-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Tmem/AllocResult.lean` L32-L61](../../Core/Tmem/AllocResult.lean#L32-L61)

The weak allocation result write precedes a subsequent ordinary read of the same byte by a lane participating in that allocation.

Source:

- - §9.7.18.6.1: "maintain same-address ordering" - §9.7.18.7.1: "tcgen05.alloc is a blocking instruction" - §9.7.18.7.1: "writes the address of the allocated Tensor Memory into shared memory" - §9.7.18.7.1 (Example 1): "tcgen05.alloc.cta_group::1.sync.aligned.shared::cta.b32 [sMemAddr1], 32; ld.shared.b32 taddr, [sMemAddr1];"

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Applies:** The allocating warp's local shared write and its participating lanes' later ordinary reads, for both CTA group sizes.

**Premises:** The leader and reading lane issue the same allocation instance, identified by matching collective ordinals and operands in one warp. The leader's next event writes the four-byte result. The reading lane has a later ordinary read covering a byte of that result.

**Effect:** The result write precedes the read at the overlapping byte in `modelCausality`. A nonleader's return depends on the actual local result write. The leader can emit the write once the resource operation is ready.

**Why it is not spec text:** The manual gives a blocking warp instruction, its same-address behavior, and an immediate readback example. It does not express cross-lane ordering for a trace representation that splits the warp instruction from a single representative weak store. The readback example motivates a local byte edge rather than a warp-wide memory fence. Disclosed by every kernel whose statement names `Op.tcAlloc`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

</details>

<a id="dep-tmem-alloc-wait"></a>
#### what an allocation-management instruction waits for (`DEP-TMEM-ALLOC-WAIT`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L375-L422](../../Core/Tmem/TmemPairHistory.lean#L375-L422)

No lane returns from an allocation-management instruction before its CTA's allocator has performed its warp's request. An allocation and every cta_group::1 instruction also wait until their operation is complete, and a cta_group::2 deallocation or relinquishment waits for the peer CTA's half exactly when the execution chooses that it waits. A nonleader in an allocating warp also waits for its local allocation result store.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.MustWait`](../../Core/Tmem/TmemPairHistory.lean#L424-L430) ([concept](#c-tmem-pair-mustwait))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5 Table 55 (::1): "Issue from a single warp in the current CTA would initiate the
    allocation management instruction."
- §9.7.18.5 Table 55 (::2): "the first warp to perform the operation could block until the the
    second warp in the Peer CTA also performs the operation"
- §9.7.18.6.1 (synchronous allocation management)
- §9.7.18.7.1: "tcgen05.alloc is a blocking instruction"
- §9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not available
    and unblocks as soon as the requested amount of Tensor Memory becomes available for
    allocation."
- §9.7.18.7.1: "tcgen05.dealloc is a potentially blocking instruction which deallocates the Tensor
    Memory specified by the Tensor Memory address taddr"
- §9.7.18.7.1: "tcgen05.dealloc may block to collectively performs the deallocation with the other
    peer CTA ’s warp"
- EXT-TMEM-ALLOC-ORDER
- EXT-TMEM-ALLOC-RESULT-ORDER

**Applies:** Allocation-management events of either cta_group that have a later event of their thread (they returned)

**Premises:** An instruction returns only after its CTA's allocator has performed its warp's request (`Performed`). An allocation, and every cta_group::1 instruction, returns only after its operation is complete. A cta_group::2 deallocation or relinquishment waits for the peer CTA's half, and so for the pairing, exactly when Execution.tmemPairBlocks chooses so; the choice has no effect on cta_group::1 instructions. An allocating warp's nonleaders also have the local result-store node as a return dependency.

**Effect:** The needs of an allocation-management event (`KindNeeds`, DEP-ORDER): the lanes of its warp, `Performed`, and when `MustWait` holds `Covered`, the lanes of the peer warp of a `cta_group::2` operation, and for an allocation the lanes of each release that last freed a column of the returned range (the reuse witness of the "unblocks as soon as" sentence). These edges belong to the execution layer. The allocation-result byte edge is supplied separately by EXT-TMEM-ALLOC-RESULT-ORDER. Existing choices are immutable under execution extension.

</details>

### Which executions are allowed

The order of each allocator's history, completion of operations, and the coverage of accesses by allocations.

<a id="obj-tmem-order"></a>
#### the execution order of one CTA's allocator (`OBJ-TMEM-ORDER`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L199-L231](../../Core/Tmem/TmemPairHistory.lean#L199-L231)

The order of the records in a CTA's allocator history is the order of that CTA's Tensor Memory allocator object, and it must agree with causality: when a lane of one request causally precedes a lane of another request of the same CTA, the first request is earlier in the history. `Precedes cta i j` says that `i` is a lane event of an earlier record of the history of CTA `cta` than `j`.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.Precedes`](../../Core/Tmem/TmemPairHistory.lean#L336-L340) ([concept](#c-tmem-pair-precedes))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."
- §9.7.18.7.1: "Instruction tcgen05.relinquish_alloc_permit specifies that the CTA of the executing
    thread is relinquishing the right to allocate Tensor Memory . So, it is illegal for a CTA to
    perform tcgen05.alloc after any of its constituent threads execute
    tcgen05.relinquish_alloc_permit ."
- §8.9.5 (base causality order)
- EXT-TMEM-ALLOC-ORDER

**Applies:** The records of one CTA's history `X.tmemHistory cta` and their lane events

**Effect:** The order of the object `.tmem cta` (MEM-OBJECT-ORDER-CAUSALITY `ObjectOrder`, on the return nodes of the lanes), so `Consistent.object` (ObjectCoherent) makes each history agree with causality; the object is not part of the dependency axiom (`OrderObject.Enabling`, DEP-ORDER).

</details>

<a id="ext-tmem-alloc-order"></a>
##### a CTA's allocator performs its requests by their return, in an order that follows causality (`EXT-TMEM-ALLOC-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L233-L334](../../Core/Tmem/TmemPairHistory.lean#L233-L334)

Each CTA's allocator performs the requests of its warps one at a time, in one order, its history `tmemHistory cta`, and that order contains causality. It performs a warp's request before any lane of the warp returns from the instruction (`Performed`, DEP-TMEM-ALLOC-WAIT). When a lane of request `y` causally precedes (`stageCausality`, through `baseCausality`) a lane of request `x` of the same CTA, `y` is earlier in the history (`Precedes`, `ObjectCoherent`). For a `.cta_group::2` operation each CTA's allocator performs its own CTA's request, its half, at its own position and before its own warp returns, whether or not that warp waits for the peer warp, and the operation is complete when both halves are performed and paired (`tmemPairing`). No order is imposed between the two allocators of a pair.

Source:

- - §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the execution order within the CTA." - §9.7.18.7.1: "it is illegal for a CTA to perform tcgen05.alloc after any of its constituent threads execute tcgen05.relinquish_alloc_permit" - §9.7.18.7.1: "tcgen05.dealloc is a potentially blocking instruction which deallocates the Tensor Memory specified by the Tensor Memory address taddr" - §9.7.18.7.1, with .cta_group::2: "tcgen05.dealloc may block to collectively performs the deallocation with the other peer CTA ’s warp" - §9.7.18.6.1 (alloc, dealloc and relinquish_alloc_permit are synchronous instructions): "inherently ordered with respect to other tcgen05 operations in the same order" - §9.7.18.5 Table 55 (::1): "Issue from a single warp in the current CTA would initiate the allocation management instruction." - §9.7.18.5 Table 55 (::2): "Issue from two warps, one in each of the current CTA and its Peer CTA , in order to collectively perform the operation, i.e., the first warp to perform the operation could block until the the second warp in the Peer CTA also performs the operation" - §8.9.5

Direction: `reading` (the entry relies on an interpretation or a named external fact). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The quoted rules speak of the execution order of the allocation-management instructions of a CTA, which the memory model does not define. The model reads it as the order in which the CTA's allocator performs them, and reads it to contain base causality order. For `.cta_group::1` a synchronous instruction that deallocates (or relinquishes the permit) has done so when it returns. For `.cta_group::2` the text says that the first warp performs the operation and may then block until the peer warp performs it. It does not say when the issuing CTA's own half takes effect in its allocator if the warp returns without waiting. The model reads "the first warp to perform the operation" as its CTA's allocator performing that CTA's half before the warp returns. This reading stays separate from EXT-OBJECT-ORDER. The manual states the allocator's order as "the execution order within the CTA" and never states that the operations of the other three synchronization objects form one order, so no single manual sentence supports both readings. The readings also rest on different premises (an allocator performs a request before its warp returns, which no other object does), and kernels that name `Op.mbarInit` or `Op.barSync` but no `Op.tcAlloc` do not rely on this one.

**Effect:** The model reports every such allocation as unsafe (`PendingReleaseAlloc`, part of `ResourceUnsafe`, ERR-TMEM-RESOURCE): an allocation after a paired `.cta_group::2` deallocation in its CTA's history, in either CTA of the pair, is unsafe unless a lane of the peer request causally precedes a lane of the allocation (`baseCausality` from that lane; the lane has then returned, so the peer half has been performed). That rule is stricter, because the text does not determine whether those columns can be allocated at that point. Disclosed by every kernel whose statement names `Op.tcAlloc`, `Op.tcDealloc` or `Op.tcRelinquish`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

</details>

<a id="obj-tmem-origin"></a>
#### allocator histories and pairings belong to their CTAs (`OBJ-TMEM-ORIGIN`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L68-L94](../../Core/Tmem/TmemPairHistory.lean#L68-L94)

Each CTA's allocator history holds valid requests of that CTA, and its replay never blocks, so every allocation returns free columns; each pairing joins two recorded cta_group::2 requests of the two CTAs of a pair, and each request is paired at most once. A history whose replay faults, and an allocation after a paired deallocation that the peer CTA's request does not causally precede, are ERR-TMEM-RESOURCE.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Tmem.Pair.HistoriesOk`](../../Core/Tmem/TmemPairHistory.lean#L96-L105) ([concept](#c-tmem-pair-historiesok))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5.1 (even/odd CTA pair)
- §9.7.18.5 Table 55 (::2): "the first warp to perform the operation could block until the the
    second warp in the Peer CTA also performs the operation"
- §9.7.18.7.1 (resource operations): "The tcgen05.alloc blocks if the requested amount of Tensor
    Memory is not available and unblocks as soon as the requested amount of Tensor Memory becomes
    available for allocation."
- EXT-TMEM-ALLOC-ORDER

**Applies:** Execution.tmemHistory, indexed by CTA, and Execution.tmemPairing

**Premises:** Every history has valid actual requests of its own CTA and records only operations its allocator can perform. Every pairing pairs two valid recorded cta_group::2 requests of the two CTAs of one CTA pair, and a request (identified by its lane-0 event) is paired at most once.

**Effect:** HistoriesOk is a consistency field.

</details>

<a id="obj-tmem-complete-operations"></a>
#### performed halves, completed and pending resource operations (`OBJ-TMEM-COMPLETE-OPERATIONS`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L152-L176](../../Core/Tmem/TmemPairHistory.lean#L152-L176)

A cta_group::1 operation is complete when its CTA's allocator has performed it, and a cta_group::2 operation is complete when its two requests are paired. A complete execution has every issued allocation-management event in a complete operation, so no request stays pending at kernel completion.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.Participates`](../../Core/Tmem/TmemPairHistory.lean#L178-L180) ([concept](#c-tmem-pair-participates)), [`Tmem.Pair.Performed`](../../Core/Tmem/TmemPairHistory.lean#L182-L184) ([concept](#c-tmem-pair-performed)), [`Tmem.Pair.Completed`](../../Core/Tmem/TmemPairHistory.lean#L186-L189) ([concept](#c-tmem-pair-completed)), [`Tmem.Pair.Covered`](../../Core/Tmem/TmemPairHistory.lean#L191-L193) ([concept](#c-tmem-pair-covered)), [`Tmem.Pair.Drained`](../../Core/Tmem/TmemPairHistory.lean#L195-L197) ([concept](#c-tmem-pair-drained))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.5 (collective issue)
- §9.7.18.7.1 (blocking allocation and collective resource effects)

**Applies:** Actual allocation-management events, allocator histories and pairings

**Premises:** A lane event is performed when its CTA's allocator has performed its warp's request. A cta_group::1 operation is complete when its CTA's allocator has performed it. A cta_group::2 operation is complete when its two requests are paired, which requires both CTAs' allocators to have performed them (HistoriesOk). A covered event is a participating lane of a complete operation. Complete executions must cover all issued requests.

**Effect:** Drained is part of Complete. What a returning instruction must have performed or completed is DEP-TMEM-ALLOC-WAIT.

</details>

<a id="obj-tmem-completion-prefix"></a>
#### synchronous resource completion prefixes (`OBJ-TMEM-COMPLETION-PREFIX`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairCompletion.lean` L11-L37](../../Core/Tmem/TmemPairCompletion.lean#L11-L37)

An allocation-management operation is complete only when every earlier request, in program order, of each of its warps belongs to a complete operation.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.CompletionReady`](../../Core/Tmem/TmemPairCompletion.lean#L40-L42) ([concept](#c-tmem-pair-completionready)), [`Tmem.Pair.CompletionClosed`](../../Core/Tmem/TmemPairCompletion.lean#L44-L46)

<details>
<summary>Details for reviewers</summary>

- §9.7.18.6.1 (synchronous allocation management)
- §9.7.18.5 and §9.7.18.7.1 (collective resource effects and optional peer blocking)

**Applies:** Actual full warp requests: the completion of an operation (a cta_group::1 record or a pairing).

**Premises:** Every earlier request has valid actual participants; WarpRequest.Before orders every lane of the same warp.

**Effect:** CompletionClosed is a Consistent field enforcing resource completion prefixes. Peer-wait choices and MustWait remain unchanged; source advancement alone is not completion. No memory visibility, access-completion or final drain conclusion is asserted.

</details>

<a id="obj-tmem-publication"></a>
#### a paired allocation published through the peer warp (`OBJ-TMEM-PUBLICATION`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairLifetime.lean` L12-L31](../../Core/Tmem/TmemPairLifetime.lean#L12-L31)

An allocation whose request is paired with a cta_group::2 allocation of the peer CTA is published to an event when an event of the peer CTA's paired request happens before that event. This publication adds no edge to base causality order (`baseCausality`).

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Tmem.Pair.PairAllocBefore`](../../Core/Tmem/TmemPairLifetime.lean#L66-L70) ([concept](#c-tmem-pair-pairallocbefore))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.7.1 (collective `cta_group::2` allocation)
- EXT-PAIR-ALLOC-ORDER

**Applies:** Allocations of a CTA whose request is paired (`Execution.tmemPairing`) with a `tcgen05.alloc.cta_group::2` request of the peer CTA

**Premises:** An event of the paired peer request happens before the access.

**Effect:** `PairAllocBefore` is the peer route of the one coverage relation `Covers` (OBJ-TMEM-LIFETIME), which every Tensor Memory rule uses.

</details>

<a id="ext-pair-alloc-order"></a>
##### a paired allocation is complete when the peer warp's returns (`EXT-PAIR-ALLOC-ORDER`)

*Interpretation (EXT)* · [Lean comment: `Core/Tmem/TmemPairLifetime.lean` L33-L63](../../Core/Tmem/TmemPairLifetime.lean#L33-L63)

When one warp of each CTA of a pair performs a paired `tcgen05.alloc.cta_group::2`, the model takes the allocation of each CTA to be complete, and usable by the Tensor Memory accesses of either CTA, before the instruction returns in the peer warp. The allocation of a CTA therefore covers an access when an event of the peer warp's paired allocation happens before the access.

Source:

- - §9.7.18.7.1: "When .cta_group::2 is specified, one warp from each of the peer CTAs must collectively perform the allocation and de-allocation." - §9.7.18.7.1: "The mandatory .sync qualifier indicates that the instruction causes the executing thread to wait until all threads in the warp execute the same instruction before resuming execution."

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH)). This is an interpretation (EXT): a reading the model adopts beyond what the PTX text states.

<details>
<summary>Details for reviewers</summary>

**Why it is not spec text:** The text makes the two warps perform the allocation collectively. It does not state that the peer CTA's half has completed when the instruction returns in a warp, nor that the peer's allocation is then ordered before the warp's later Tensor Memory accesses of the peer's cells. Without the reading, coverage requires publication from the cell's own CTA's allocation event. The peer needs of the pair (DEP-TMEM-ALLOC-WAIT) enter the dependency order (DEP-ORDER) and add nothing to `baseCausality`.

**Effect:** In the model, a CTA's allocation record whose request is paired (`Execution.tmemPairing`) with a request of the peer CTA covers an access when an event of the peer warp's allocation happens before the access (`PairAllocBefore`, a disjunct of `Covers`). Every use of coverage takes this route: the allocated-before-access conjunct and the release conjunct of `AccessSafe` (ERR-TMEM-ACCESS-LIFETIME), the fresh-lifetime check (`FreshAfter`) and the source-liveness check (`TcMma.SourceLive`). A record covering an access only through its peer is still subject to the release check. Disclosed by every kernel whose statement names `Op.tcAlloc (group := CtaGroup.two)`: FlashAttn4Fwd, Fp16Gemm8192.

</details>

<a id="obj-tmem-lifetime"></a>
#### allocation coverage and first release attempts (`OBJ-TMEM-LIFETIME`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairLifetime.lean` L72-L108](../../Core/Tmem/TmemPairLifetime.lean#L72-L108)

An allocation covers a column of its own CTA within its range for every event that the allocation event happens before, or, for an allocation paired with a cta_group::2 allocation of the peer CTA, that an event of the peer's paired request happens before. A later allocation of the same cell starts a fresh lifetime for an access when a release attempt happens before it and it covers the access. A release attempt of an allocation is the first matching deallocation after it in a lane of the allocating warp, any matching deallocation by another warp of its CTA, or, for a paired cta_group::2 allocation, a release attempt of the peer CTA's allocation of the same operation.

Source:

- 

Direction: `trust` (a trusted fact supplies a guarantee: a kernel's own, explicitly declared assumption, or a fact about the toolchain or the launch that holds for every kernel (EXT-ISA, EXT-LAUNCH))

Lean definitions: [`Tmem.Pair.Covers`](../../Core/Tmem/TmemPairLifetime.lean#L110-L116) ([concept](#c-tmem-pair-covers)), [`Tmem.Pair.Covers.own`](../../Core/Tmem/TmemPairLifetime.lean#L118-L124), [`Tmem.Pair.Covers.paired`](../../Core/Tmem/TmemPairLifetime.lean#L126-L132), [`Tmem.Pair.FreshAfter`](../../Core/Tmem/TmemPairLifetime.lean#L134-L137) ([concept](#c-tmem-pair-freshafter)), [`Tmem.Pair.OwnRelease`](../../Core/Tmem/TmemPairLifetime.lean#L139-L149) ([concept](#c-tmem-pair-ownrelease)), [`Tmem.Pair.ReleaseOf`](../../Core/Tmem/TmemPairLifetime.lean#L151-L155) ([concept](#c-tmem-pair-releaseof))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.1.2 (allocation before access)
- §9.7.18.7.1 (collective release and repeated allocations)
- §9.7.18.5 Table 55: "Issue from a single warp in the current CTA would initiate the allocation
    management instruction."
- OBJ-TMEM-PUBLICATION
- EXT-PAIR-ALLOC-ORDER

**Applies:** Allocations of either cta_group performed by their CTA's allocator, and whole-allocation release attempts

**Premises:** Each CTA has its own column range. Coverage is at the accessed cell's physical CTA, which need not be the accessor's for a group-2 operation, and requires publication to the access from the allocation event or, for a paired allocation, from the peer's paired request (EXT-PAIR-ALLOC-ORDER). This is the one coverage relation of the model. A release attempt of an allocation is the first matching attempt after it in a lane of its warp, a matching deallocation by a thread of another warp of its CTA (any warp may issue the release), or, for a paired cta_group::2 allocation, a release attempt of the peer CTA's allocation of the same operation.

**Effect:** These relations connect allocator histories to access safety and source-lifetime checks. Memory contents are published by MEM-MODEL-CAUSALITY and asynchronous completion by DEP-TC-COMPLETION-CLOSURE.

</details>

### What counts as an error

Executions that are rejected as unsafe because of Tensor Memory allocation, access or release.

<a id="err-tmem-resource"></a>
#### a fault of a CTA's Tensor Memory allocator (`ERR-TMEM-RESOURCE`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairHistory.lean` L107-L128](../../Core/Tmem/TmemPairHistory.lean#L107-L128)

An execution is unsafe when the replay of some CTA's allocator history faults, or when a CTA's allocator performs an allocation after a paired cta_group::2 deallocation and no lane of the peer CTA's request of that deallocation causally precedes a lane of the allocation.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`Tmem.Pair.PeerBefore`](../../Core/Tmem/TmemPairHistory.lean#L130-L135), [`Tmem.Pair.PendingReleaseAlloc`](../../Core/Tmem/TmemPairHistory.lean#L137-L143) ([concept](#c-tmem-pair-pendingreleasealloc)), [`Tmem.Pair.ResourceUnsafe`](../../Core/Tmem/TmemPairHistory.lean#L145-L150) ([concept](#c-tmem-pair-resourceunsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.7.1 (resource operations): "tcgen05.dealloc may block to collectively performs the
    deallocation with the other peer CTA ’s warp"
- OBJ-TMEM-ALLOCATOR (the faults of the allocator)
- OBJ-TMEM-ORIGIN
- EXT-TMEM-ALLOC-ORDER

**Applies:** Execution.tmemHistory, indexed by CTA, and Execution.tmemPairing

**Premises:** The histories and pairings are those of OBJ-TMEM-ORIGIN.

**Effect:** Safety rejection (part of Unsafe). ResourceUnsafe is a replay fault in some CTA's history, or PendingReleaseAlloc in some CTA's history.

</details>

<a id="err-tmem-access-lifetime"></a>
#### allocation and completion of every Tensor Memory access (`ERR-TMEM-ACCESS-LIFETIME`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairAccess.lean` L11-L53](../../Core/Tmem/TmemPairAccess.lean#L11-L53)

Every Tensor Memory access must touch cells that a completed allocation of the cell's CTA covers for it, through the allocation's own event or its paired peer allocation. For every allocation that covers the access and every release attempt of that allocation, the access must complete before the release attempt, or a fresh allocation of the cell must lie between them; an execution that breaks either condition is unsafe.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.Access`](../../Core/Tmem/TmemPairAccess.lean#L56-L60) ([concept](#c-tmem-pair-access)), [`Tmem.Pair.AccessSafe`](../../Core/Tmem/TmemPairAccess.lean#L62-L70), [`Tmem.Pair.AccessUnsafe`](../../Core/Tmem/TmemPairAccess.lean#L72-L73) ([concept](#c-tmem-pair-accessunsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.1.2 (Tensor Memory is allocated before use)
- §9.7.18.7.1: "taddr must point to a previous Tensor Memory allocation"
- §9.7.18.6.4 (completion before cross-thread synchronization)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER
- OBJ-TMEM-PUBLICATION
- EXT-PAIR-ALLOC-ORDER

**Applies:** Every MMA destination write and potential accumulator read, and every Tensor Memory load and store register, copied word and word a shift reads or writes, of either CTA group

**Premises:** Each access names its physical cell. A completed allocation of that cell's CTA covers it and is published to the access. Every release attempt of every covering allocation is checked, even if no joint release has completed. The release attempts of an allocation are, in each lane of its warp, the first matching deallocation after it, every matching deallocation by another warp of its CTA, and the same release attempts of the peer CTA's allocation when the allocation is paired. For each of them, the access must have completed before it (an MMA or copy by an observed commit, a load by its thread's `wait::ld`, a store by its thread's `wait::st`), that completion ordered before the release by a fenced chain or, under EXT-TCACQUIRE, by causality, or a fresh allocation must separate the access from that lifetime. The text has the peer warps synchronize their accesses before they attempt a collective deallocation.

**Effect:** AccessUnsafe enters Unsafe. Coverage is `Tmem.Pair.Covers` (OBJ-TMEM-LIFETIME): an allocation paired with a `cta_group::2` allocation of the peer CTA also covers the events that the peer warp's allocation happens before (OBJ-TMEM-PUBLICATION, EXT-PAIR-ALLOC-ORDER), both in the allocated-before-access check and in the release check, so a record covering an access only through its peer is still released after the access completes. This is the only check that a Tensor Memory access is allocated. The direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.

</details>

<a id="err-tmem-not-released"></a>
#### no live allocations at kernel completion (`ERR-TMEM-NOT-RELEASED`)

*Rule* · [Lean comment: `Core/Tmem/TmemPairRelease.lean` L12-L32](../../Core/Tmem/TmemPairRelease.lean#L12-L32)

When every launched thread has exited or belongs to a canceled CLC task, and every issued allocation-management operation is complete, an execution is unsafe if the replay of some CTA's allocator history ends without fault in a state that still holds a live allocation. Only `tcgen05.dealloc` releases an allocation.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Tmem.Pair.Exited`](../../Core/Tmem/TmemPairRelease.lean#L34-L36), [`Tmem.Pair.Released`](../../Core/Tmem/TmemPairRelease.lean#L38-L40) ([concept](#c-tmem-pair-released)), [`Tmem.Pair.ReleaseUnsafe`](../../Core/Tmem/TmemPairRelease.lean#L42-L46) ([concept](#c-tmem-pair-releaseunsafe))

<details>
<summary>Details for reviewers</summary>

- §9.7.18.1.2
- §9.7.18.7.1 (all allocated Tensor Memory must be explicitly deallocated before kernel exit)

**Applies:** Allocator histories of non-exclusive resource operations of either cta_group

**Premises:** Every launched thread has exited (canceled CLC tasks have no thread execution), and every issued allocation-management operation is complete (Drained). Resource replay is checked independently.

**Effect:** ReleaseUnsafe is a safety predicate of the final allocator history (`Unsafe`).

</details>
