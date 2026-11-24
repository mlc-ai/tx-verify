-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairRequests
public import Core.Memory.Order

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-! ## OBJ-TMEM-HISTORY — the operations a CTA's allocator performs
Statement: Each CTA's allocator has a finite history of the operations it performed, one record per
  performed warp request, each with actual lane events. Replaying the history from an empty
  allocator through the allocator transitions gives the CTA's Tensor Memory allocation state, or the
  first blocked allocation or fault. A CTA's history holds the operations its allocator performed.
  Pending requests and the pairing of a cta_group::2 operation are represented separately
  (OBJ-TMEM-COMPLETE-OPERATIONS). The history order is the execution order of OBJ-TMEM-ORDER: it
  contains causality order between the requests of the CTA, and requests that causality does not
  order may appear in either order, so a fault in either order is reported. No global order on
  memory events and no order between two CTAs' allocators is imposed.

Defs: Tmem.Pair.WarpRequest.Before, Tmem.Pair.RequestHistory, Tmem.Pair.runRequests

Source:
- §9.7.18.5
- §9.7.18.6.1 (synchronous allocation management)
- §9.7.18.7.1: "When .cta_group::1 is specified, one warp from the CTA must perform the allocation
    and de-allocation. When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."

Direction: stricter

Applies: The finite history of each CTA's allocator: the requests of its warps it performed, in its
  execution order; different operations may be performed by different warps

Premises: Each record has actual matching lane events. Each allocator begins empty.

Effect: RequestHistory checks event provenance; runRequests replays one allocator's resource
  effects.

Review: Per-warp program order and the absence of a repeated request are proved in
  `Lemmas/Tmem/TmemPairOrder.lean`. Program order within a warp and the absence of a repeated
  request also follow from the history order. `WarpRequest.Before` is the program order of one warp,
  used by OBJ-TMEM-COMPLETION-PREFIX.
-/
/-- Warp request `a` comes before `b` in the program order of one warp: same CTA and warp, and
every lane's event of `a` precedes that lane's event of `b`. -/
def WarpRequest.Before (a b : WarpRequest) : Prop :=
  a.cta = b.cta ∧ a.warp = b.warp ∧ ∀ lane, a.indices lane < b.indices lane

/-- Every record of an allocator history is valid (`Requests.Valid`). -/
def RequestHistory (L : Launch) (X : Execution) (history : List Requests) : Prop :=
  ∀ r ∈ history, r.Valid L X

/-- Replay one allocator's history. Faults are retained, so malformed programs do not disappear
by having no successful resource execution. -/
def runRequests (s : Tmem.State) : List Requests → Tmem.Outcome
  | [] => .done s
  | r :: rest =>
    match Tmem.perform s r.action with
    | .done next => runRequests next rest
    | .blocked => .blocked
    | .fault reason => .fault reason

/-! ## OBJ-TMEM-ORIGIN — allocator histories and pairings belong to their CTAs
Statement: Each CTA's allocator history holds valid requests of that CTA, and its replay never
  blocks, so every allocation returns free columns; each pairing joins two recorded cta_group::2
  requests of the two CTAs of a pair, and each request is paired at most once. A history whose
  replay faults, and an allocation after a paired deallocation that the peer CTA's request does not
  causally precede, are ERR-TMEM-RESOURCE.

Defs: Tmem.Pair.HistoriesOk

Source:
- §9.7.18.5.1 (even/odd CTA pair)
- §9.7.18.5 Table 55 (::2): "the first warp to perform the operation could block until the the
    second warp in the Peer CTA also performs the operation"
- §9.7.18.7.1 (resource operations): "The tcgen05.alloc blocks if the requested amount of Tensor
    Memory is not available and unblocks as soon as the requested amount of Tensor Memory becomes
    available for allocation."
- EXT-TMEM-ALLOC-ORDER

Direction: stricter

Applies: Execution.tmemHistory, indexed by CTA, and Execution.tmemPairing

Premises: Every history has valid actual requests of its own CTA and records only operations its
  allocator can perform. Every pairing pairs two valid recorded cta_group::2 requests of the two
  CTAs of one CTA pair, and a request (identified by its lane-0 event) is paired at most once.

Effect: HistoriesOk is a consistency field.
-/
/-- The allocator histories and pairings of an execution are well formed: each CTA's history
holds valid records of that CTA and its replay does not block, each pairing is valid and pairs
two recorded cta_group::2 requests, and no request is paired twice. -/
def HistoriesOk (L : Launch) (X : Execution) : Prop :=
  (∀ cta, RequestHistory L X (X.tmemHistory cta) ∧ (∀ r ∈ X.tmemHistory cta, r.own.cta = cta) ∧
    runRequests {} (X.tmemHistory cta) ≠ .blocked) ∧
  (∀ q ∈ X.tmemPairing, PairValid L X q ∧
    (∃ r ∈ X.tmemHistory q.1.cta, r.own = q.1 ∧ r.group = .two) ∧
    ∃ r ∈ X.tmemHistory q.2.cta, r.own = q.2 ∧ r.group = .two) ∧
  X.tmemPairing.Pairwise fun q q' => q.1.event L 0 ≠ q'.1.event L 0 ∧ q.2.event L 0 ≠ q'.2.event L 0

/-! ## ERR-TMEM-RESOURCE — a fault of a CTA's Tensor Memory allocator
Statement: An execution is unsafe when the replay of some CTA's allocator history faults, or when a
  CTA's allocator performs an allocation after a paired cta_group::2 deallocation and no lane of the
  peer CTA's request of that deallocation causally precedes a lane of the allocation.

Defs: Tmem.Pair.PeerBefore, Tmem.Pair.PendingReleaseAlloc, Tmem.Pair.ResourceUnsafe

Source:
- §9.7.18.7.1 (resource operations): "tcgen05.dealloc may block to collectively performs the
    deallocation with the other peer CTA ’s warp"
- OBJ-TMEM-ALLOCATOR (the faults of the allocator)
- OBJ-TMEM-ORIGIN
- EXT-TMEM-ALLOC-ORDER

Direction: stricter

Applies: Execution.tmemHistory, indexed by CTA, and Execution.tmemPairing

Premises: The histories and pairings are those of OBJ-TMEM-ORIGIN.

Effect: Safety rejection (part of Unsafe). ResourceUnsafe is a replay fault in some CTA's history,
  or PendingReleaseAlloc in some CTA's history.
-/
/-- A lane of the request paired with `w` causally precedes (`baseCausality`) a lane of `a`. An
allocation-management event does not synchronize, so that lane has continued past its
instruction: the peer request has returned, and so has been performed. -/
def PeerBefore (L : Launch) (X : Execution) (w a : WarpRequest) : Prop :=
  ∃ q ∈ X.tmemPairing, ∃ p, ((q.1 = w ∧ q.2 = p) ∨ (q.2 = w ∧ q.1 = p)) ∧
    ∃ lane lane', baseCausality L X (p.event L lane) (a.event L lane')

/-- In CTA `cta`'s history an allocation follows a paired cta_group::2 deallocation whose peer
request does not causally precede it. -/
def PendingReleaseAlloc (L : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∃ (k l : Nat) (d a : Requests), (X.tmemHistory cta)[k]? = some d ∧
    (X.tmemHistory cta)[l]? = some a ∧ k < l ∧ d.group = .two ∧
    (∃ base n, d.action = .dealloc base n) ∧ (∃ n base, a.action = .alloc n base) ∧
    (∃ q ∈ X.tmemPairing, q.1 = d.own ∨ q.2 = d.own) ∧ ¬ PeerBefore L X d.own a.own

/-- An allocator fault: the replay of some CTA's history faults, or an allocation in some CTA's
history follows a paired cta_group::2 deallocation whose peer request does not causally precede
it (`PendingReleaseAlloc`). -/
def ResourceUnsafe (L : Launch) (X : Execution) : Prop :=
  ∃ cta, (∃ reason, runRequests {} (X.tmemHistory cta) = .fault reason) ∨
    PendingReleaseAlloc L X cta

/-! ## OBJ-TMEM-COMPLETE-OPERATIONS — performed halves, completed and pending resource operations
Statement: A cta_group::1 operation is complete when its CTA's allocator has performed it, and a
  cta_group::2 operation is complete when its two requests are paired. A complete execution has
  every issued allocation-management event in a complete operation, so no request stays pending at
  kernel completion.

Defs: Tmem.Pair.Participates, Tmem.Pair.Performed, Tmem.Pair.Completed, Tmem.Pair.Covered,
  Tmem.Pair.Drained

Source:
- §9.7.18.5 (collective issue)
- §9.7.18.7.1 (blocking allocation and collective resource effects)

Direction: reading

Applies: Actual allocation-management events, allocator histories and pairings

Premises: A lane event is performed when its CTA's allocator has performed its warp's request. A
  cta_group::1 operation is complete when its CTA's allocator has performed it. A cta_group::2
  operation is complete when its two requests are paired, which requires both CTAs' allocators to
  have performed them (HistoriesOk). A covered event is a participating lane of a complete
  operation. Complete executions must cover all issued requests.

Effect: Drained is part of Complete. What a returning instruction must have performed or completed
  is DEP-TMEM-ALLOC-WAIT.
-/
/-- `i` is a lane event of warp request `w`. -/
def Participates (L : Launch) (w : WarpRequest) (i : EvId) : Prop :=
  ∃ lane, w.event L lane = i

/-- `i` is a lane event of a request that its CTA's allocator has performed. -/
def Performed (L : Launch) (X : Execution) (i : EvId) : Prop :=
  ∃ cta, ∃ r ∈ X.tmemHistory cta, Participates L r.own i

/-- The warp requests of a complete operation: a performed cta_group::1 request, or a pairing. -/
def Completed (X : Execution) (ws : List WarpRequest) : Prop :=
  (∃ cta r, r ∈ X.tmemHistory cta ∧ r.group = .one ∧ ws = [r.own]) ∨
    ∃ q ∈ X.tmemPairing, ws = [q.1, q.2]

/-- `i` is a lane event of a complete operation. -/
def Covered (L : Launch) (X : Execution) (i : EvId) : Prop :=
  ∃ ws, Completed X ws ∧ ∃ w ∈ ws, Participates L w i

/-- Every allocation-management event of the execution is covered: no request is pending. -/
def Drained (L : Launch) (X : Execution) : Prop :=
  ∀ i pc group dst request, X.get i = some ⟨pc, .tc (.resource group dst request)⟩ → Covered L X i

/-! ## OBJ-TMEM-ORDER — the execution order of one CTA's allocator
Statement: The order of the records in a CTA's allocator history is the order of that CTA's Tensor
  Memory allocator object, and it must agree with causality: when a lane of one request causally
  precedes a lane of another request of the same CTA, the first request is earlier in the history.
  `Precedes cta i j` says that `i` is a lane event of an earlier record of the history of CTA `cta`
  than `j`.

Defs: Tmem.Pair.Precedes

Source:
- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."
- §9.7.18.7.1: "Instruction tcgen05.relinquish_alloc_permit specifies that the CTA of the executing
    thread is relinquishing the right to allocate Tensor Memory . So, it is illegal for a CTA to
    perform tcgen05.alloc after any of its constituent threads execute
    tcgen05.relinquish_alloc_permit ."
- §8.9.5 (base causality order)
- EXT-TMEM-ALLOC-ORDER

Direction: reading

Applies: The records of one CTA's history `X.tmemHistory cta` and their lane events

Premises: none

Effect: The order of the object `.tmem cta` (MEM-OBJECT-ORDER-CAUSALITY `ObjectOrder`, on the return
  nodes of the lanes), so `Consistent.object` (ObjectCoherent) makes each history agree with
  causality; the object is not part of the dependency axiom (`OrderObject.Enabling`, DEP-ORDER).

Review: The allocator order is combined with causality only. The executions in which an enabling
  path that is not causality (a relaxed mbarrier arrival observed by another warp) leads from the
  return of one request to a request recorded earlier in the same history therefore remain, and a
  fault in either order of such requests is reported.

### EXT-TMEM-ALLOC-ORDER — a CTA's allocator performs its requests by their return, in an order
  that follows causality

Statement: Each CTA's allocator performs the requests of its warps one at a time, in one order, its
  history `tmemHistory cta`, and that order contains causality. It performs a warp's request before
  any lane of the warp returns from the instruction (`Performed`, DEP-TMEM-ALLOC-WAIT). When a
  lane of request `y` causally precedes (`stageCausality`, through `baseCausality`) a lane of
  request `x` of the same CTA, `y` is earlier in the history (`Precedes`, `ObjectCoherent`). For a
  `.cta_group::2` operation each CTA's allocator performs its own CTA's request, its half, at its
  own position and before its own warp returns, whether or not that warp waits for the peer warp,
  and the operation is complete when both halves are performed and paired (`tmemPairing`). No order
  is imposed between the two allocators of a pair.

Source:
- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."
- §9.7.18.7.1: "it is illegal for a CTA to perform tcgen05.alloc after any of its constituent
    threads execute tcgen05.relinquish_alloc_permit"
- §9.7.18.7.1: "tcgen05.dealloc is a potentially blocking instruction which deallocates the Tensor
    Memory specified by the Tensor Memory address taddr"
- §9.7.18.7.1, with .cta_group::2: "tcgen05.dealloc may block to collectively performs the
    deallocation with the other peer CTA ’s warp"
- §9.7.18.6.1 (alloc, dealloc and relinquish_alloc_permit are synchronous instructions): "inherently
    ordered with respect to other tcgen05 operations in the same order"
- §9.7.18.5 Table 55 (::1): "Issue from a single warp in the current CTA would initiate the
    allocation management instruction."
- §9.7.18.5 Table 55 (::2): "Issue from two warps, one in each of the current CTA and its Peer CTA ,
    in order to collectively perform the operation, i.e., the first warp to perform the operation
    could block until the the second warp in the Peer CTA also performs the operation"
- §8.9.5

Why it is not spec text: The quoted rules speak of the execution order of the allocation-management
  instructions of a CTA, which the memory model does not define. The model reads it as the order in
  which the CTA's allocator performs them, and reads it to contain base causality order. For
  `.cta_group::1` a synchronous instruction that deallocates (or relinquishes the permit) has done
  so when it returns. For `.cta_group::2` the text says that the first warp performs the operation
  and may then block until the peer warp performs it. It does not say when the issuing CTA's own
  half takes effect in its allocator if the warp returns without waiting. The model reads "the first
  warp to perform the operation" as its CTA's allocator performing that CTA's half before the warp
  returns.
  This reading stays separate from EXT-OBJECT-ORDER. The manual states the allocator's order as "the
  execution order within the CTA" and never states that the operations of the other three
  synchronization objects form one order, so no single manual sentence supports both readings. The
  readings also rest on different premises (an allocator performs a request before its warp
  returns, which no other object does), and kernels that name `Op.mbarInit` or `Op.barSync` but no
  `Op.tcAlloc` do not rely on this one.

Direction: reading

Effect: The model reports every such allocation as unsafe (`PendingReleaseAlloc`, part of
  `ResourceUnsafe`, ERR-TMEM-RESOURCE): an allocation after a paired `.cta_group::2`
  deallocation in its CTA's history, in either CTA of the pair, is unsafe unless a lane of the peer
  request causally precedes a lane of the allocation (`baseCausality` from that lane; the lane has
  then returned, so the peer half has been performed). That rule is stricter, because the text does
  not determine whether those columns can be allocated at that point. Disclosed by every kernel
  whose statement names `Op.tcAlloc`, `Op.tcDealloc` or `Op.tcRelinquish`: FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

Review: The program-order consequence is proved in `Lemmas/Tmem/TmemPairOrder.lean`, and the
  consequence of (2) is `recorded_of_before` in `Lemmas/Tmem/TmemPairHistory.lean`. The reading
  removes (1) executions whose allocator history disagrees with causality, and (2) executions in
  which a lane has returned from a deallocation or relinquishment whose request its CTA's allocator
  has not performed. Requests that causality does not order may be performed in either order, so
  both histories are possible executions; `Unsafe` quantifies over every consistent execution, so a
  column increase or an allocation after relinquishing the permit in either order is reported. A
  lane event in two records would precede itself, and program order is part of causality order, so
  no lane event is recorded twice and the requests of one warp are performed in its program order;
  with (2), a request of a warp is performed only after every earlier request of the warp. Argument
  (not a Lean proof) that (2) hides no unsafe behaviour of a run in which a half is performed after
  its warp returned: take such a run, with its issue, return and record points in time order, and
  move each such record of a deallocation or relinquishment to the return of its instruction
  (allocations are not affected: their return waits for their completion). The events, reads,
  synchronization records, pairings and allocation records are unchanged, and so are
  `baseCausality`, `stageCausality`, the needs of the lanes (DEP-ORDER: the warp's lanes are needs
  through `TcK`), the allocation coverage `Covers`, the release attempts `ReleaseOf` (events,
  pairings and allocation records) and every unsafety predicate except the replay checks. The moved
  records keep the history in time order, so it still contains causality. The replay with
  deallocations and relinquishments performed earlier is never blocked where it was not
  (`Tmem.perform`: deallocation and relinquishment never block, an earlier deallocation only frees
  columns, and an allocation after a relinquishment faults and does not block), a fault of the
  original replay remains a fault or is preceded by one, and a deallocation record only moves
  earlier, so `PendingReleaseAlloc` is kept: `ResourceUnsafe` is kept. The final live allocations of
  a fault-free replay do not depend on the order, so `ReleaseUnsafe` is kept. The reading decides
  the `.cta_group::2` case only. Under the other reading, in which a half that returned without
  waiting takes effect only when the peer half is performed, its columns stay allocated after the
  return. The two readings differ for an allocation that the CTA's allocator performs after that
  half and before the peer half is performed: whether it succeeds or waits, and which column it
  returns. On prefixes: an execution in which the deallocation is not yet paired is not reported; an
  extension that records its pairing is reported unless the peer request causally precedes the
  allocation, and a deallocation that is never paired leaves every maximal extension without
  `Drained`, so `Correct.progress` fails. A program in which the peer request causally precedes the
  allocation is therefore not rejected through an intermediate prefix; a program without that
  ordering is rejected even when the peer half happens to be performed first. The rule closes the
  difference that the issuing CTA's allocator can observe. It is not a proof that a program
  `Correct` under the model is correct under the other reading. The other points at which the
  readings could differ are covered by existing rules, checked by inspection (not a Lean proof): an
  allocation after relinquishing the permit faults once the relinquishment is performed
  (OBJ-TMEM-ALLOCATOR); the release check before exit needs every operation complete (`Drained`,
  ERR-TMEM-NOT-RELEASED); Tensor Memory accesses are checked against release attempts, whether or
  not the release is performed (OBJ-TMEM-LIFETIME, ERR-TMEM-ACCESS-LIFETIME); the peer CTA's
  allocations are checked on its own history by the same rule; and both peer-wait choices of the
  returning half are represented (DEP-TMEM-ALLOC-WAIT).
-/
/-- `i` is a lane event of an earlier record of CTA `cta`'s history than `j`. -/
def Precedes (L : Launch) (X : Execution) (cta : Nat) (i j : EvId) : Prop :=
  ∃ (k l : Nat) (x y : Requests),
    (X.tmemHistory cta)[k]? = some x ∧ (X.tmemHistory cta)[l]? = some y ∧ k < l ∧
    Participates L x.own i ∧ Participates L y.own j

/-! ## OBJ-TMEM-ALLOC-RESULT — the column an allocation returns
Statement: The Tensor Memory address that an allocating warp writes to shared memory is the column
  that its CTA's allocator selected when it performed the allocation.

Defs: Tmem.Pair.ResultOk

Source:
- §9.7.18.7.1: "tcgen05.alloc is a blocking instruction which dynamically allocates the specified
    number of columns in the Tensor Memory and writes the address of the allocated Tensor Memory
    into shared memory at the location specified by address operand dst ."
- §9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not available
    and unblocks as soon as the requested amount of Tensor Memory becomes available for allocation."

Direction: equal

Applies: Allocations of either cta_group performed by their CTA's allocator

Premises: A performed allocation is recorded with the column its CTA's allocator selected;
  OBJ-TMEM-ORIGIN checks that the columns are available where it is performed. The store of
  the address is lane 0's second event of the instruction (THREAD-TC).

Effect: Consistency constraint. An allocation that has not been performed has no column: its request
  event names only the column count, so a pending allocation may wait while the columns are held,
  and the column is selected when it is performed.
-/
/-- The event after lane 0's allocation event `i` is its address store, which holds the column
of the record of `i`. -/
def ResultOk (L : Launch) (X : Execution) : Prop :=
  ∀ i pc group dst n, X.get i = some ⟨pc, .tc (.resource group dst (.alloc n))⟩ →
    ∀ cta r base, r ∈ X.tmemHistory cta → r.own.event L 0 = i → r.action = .alloc n base →
      ∀ pc' a bs, X.get (i.1, i.2 + 1) = some ⟨pc', .wr a bs⟩ →
      bs = (Value.bits 32 (BitVec.ofNat 64 base)).toBytes

/-! ## DEP-TMEM-ALLOC-WAIT — what an allocation-management instruction waits for
Statement: No lane returns from an allocation-management instruction before its CTA's allocator has
  performed its warp's request. An allocation and every cta_group::1 instruction also wait until
  their operation is complete, and a cta_group::2 deallocation or relinquishment waits for the peer
  CTA's half exactly when the execution chooses that it waits. A nonleader in an allocating warp
  also waits for its local allocation result store.

Defs: Tmem.Pair.MustWait

Source:
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

Direction: reading

Applies: Allocation-management events of either cta_group that have a later event of their thread
  (they returned)

Premises: An instruction returns only after its CTA's allocator has performed its warp's request
  (`Performed`). An allocation, and every cta_group::1 instruction, returns only after its operation
  is complete. A cta_group::2 deallocation or relinquishment waits for the peer CTA's half, and so
  for the pairing, exactly when Execution.tmemPairBlocks chooses so; the choice has no effect on
  cta_group::1 instructions. An allocating warp's nonleaders also have the local result-store node
  as a return dependency.

Effect: The needs of an allocation-management event (`KindNeeds`, DEP-ORDER): the lanes of
  its warp, `Performed`, and when `MustWait` holds `Covered`, the lanes of the peer warp of a
  `cta_group::2` operation, and for an allocation the lanes of each release that last freed a
  column of the returned range (the reuse witness of the "unblocks as soon as" sentence). These
  edges belong to the execution layer. The allocation-result byte edge is supplied separately
  by EXT-TMEM-ALLOC-RESULT-ORDER. Existing choices are immutable under execution extension.

Review: The per-lane peer-wait choices may conservatively expose different blocking delays within a
  warp. Collective membership and aligned operands are checked by Requests.Valid and PairValid.
  Access completion before attempted deallocation must still be checked independently.
-/
/-- The return of `i` waits for its whole operation: an allocation, a cta_group::1 instruction,
or a cta_group::2 deallocation or relinquishment whose peer-wait choice is set. -/
def MustWait (X : Execution) (i : EvId) : Prop :=
  ∃ pc group dst request, X.get i = some ⟨pc, .tc (.resource group dst request)⟩ ∧
    match request with
    | .alloc .. => True
    | .dealloc .. | .relinquish => group = .one ∨ X.tmemPairBlocks i = true

end
end PTX.Tmem.Pair
