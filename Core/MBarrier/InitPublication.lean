-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.WaitOrder

@[expose] public section

namespace PTX
noncomputable section

/-! ## OBJ-MBAR-INIT-PUBLICATION — restricted publication of mbarrier initialization
Statement: An mbarrier initialization is published to a later operation when it happens before
  that operation, or when its thread follows it with `fence.mbarrier_init.release.cluster` and a
  `barrier.cluster.arrive`, and a `barrier.cluster.wait` that observed this arrival happens before
  that operation. The second route publishes the initialization and no other operation of its
  thread, and it places the initialization before every operation of the object whose issue the
  wait causally precedes.

Defs: InitFenceSync, InitFencePublished, InitPublished, InitFenceOrdered

Source:
- §9.7.15.4: "When .op_restrict is .mbarrier_init , the synchronizing effect of the fence only
    applies to the prior mbarrier.init operations executed by the same thread on mbarrier objects in
    .shared::cta state space."
- §9.7.15.4 (example): "Release local barrier state via generic proxy. mbarrier.init [bar];
    fence.mbarrier_init.release.cluster; barrier.cluster.arrive.relaxed;"
- §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation."
- §9.7.15.3: "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no
    memory ordering and visibility guarantees provided for the memory accesses performed prior to
    barrier.cluster.arrive ."
- §9.7.15.3: "If the optional .acquire qualifier is absent for barrier.cluster.wait , .acquire is
    assumed by default."
- §8.8: "Any memory synchronization established by a release pattern only affects operations
    occurring in program order before the first instruction in that pattern."
- §8.9.5 (base causality order)
- EXT-OBJECT-ORDER
- EXT-ASYNC-OBJECT
- EXT-INIT-FENCE-ARRIVE

Direction: reading

Applies: A shared::cta mbarrier initialization, followed in its thread by
  fence.mbarrier_init.release.cluster and then by a cluster arrival of either qualifier

Premises: The initialization of `m` (in the thread's own CTA), the fence and the arrival are in one
  thread, in that program order; a cluster wait observed the arrival (the cluster barrier's
  history records the wait for the phase the arrival belongs to, `ClusterBarrier.ArrivalOf` and
  `ClusterBarrier.WaitOf`); causality orders the wait before the use, or before
  the issue of the operation of `m`'s history.

Effect: Initialization publication checks in safety (`InitPublished`) and an execution constraint
  (Consistent.initFence), separate from baseCausality and modelCausality: the init is not composed
  with the program order before it, nor with any memory access; the async proxy fence is its own
  instruction (MEM-MODEL-CAUSALITY). `InitFenceSync` is the restricted synchronization: from the
  initialization to the wait. It enters neither `baseCausality` nor `stageCausality`, since both are
  closed under program order on the left (§8.9.5: "For some operation Z, X precedes Z in program
  order and Z precedes Y in base causality order"). The fence orders the initializations before it
  (§9.7.15.4) and no other operation of the thread. `InitFenceOrdered` is the order of one object
  agreeing with this synchronization, as `ObjectCoherent` and `AsyncObjectOrdered` are for causality
  (EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT): the operation, or the asynchronous update issued after the
  wait, comes after the initialization. The object history separately selects the initialization of
  the actual lifetime.

### EXT-INIT-FENCE-ARRIVE — a relaxed cluster arrival carries the init fence's release

Statement: The sequence `mbarrier.init`, `fence.mbarrier_init.release.cluster`,
  `barrier.cluster.arrive` publishes the initialization to the threads that wait for the arrival,
  also when the arrival is `.relaxed`. The fence and the relaxed arrival together order the
  thread's prior initializations before the waiters' later operations, and they order no other
  prior access of the thread. This is the synchronization `InitFenceSync`.

Source:
- §8.9.4: "A barrier.cluster.arrive operation synchronizes with a barrier.cluster.wait operation."
- §9.7.15.3: "The optional .relaxed qualifier on barrier.cluster.arrive specifies that there are no
    memory ordering and visibility guarantees provided for the memory accesses performed prior to
    barrier.cluster.arrive ."
- §9.7.15.4: "When .op_restrict is .mbarrier_init , the synchronizing effect of the fence only
    applies to the prior mbarrier.init operations executed by the same thread on mbarrier objects in
    .shared::cta state space."
- §9.7.15.4 (example): "Release local barrier state via generic proxy. mbarrier.init [bar];
    fence.mbarrier_init.release.cluster; barrier.cluster.arrive.relaxed;"

Why it is not spec text: Three passages bear on this sequence, and the text does not say how
  they combine. §8.9.4 states without condition that "A barrier.cluster.arrive operation
  synchronizes with a barrier.cluster.wait operation."; with base causality (§8.9.5) that alone
  would order every operation the arriving thread performed before the arrival before the wait's
  causal successors. The `.relaxed` sentence of §9.7.15.3 states the opposite for a relaxed
  arrival: "there are no memory ordering and visibility guarantees provided for the memory accesses
  performed prior to barrier.cluster.arrive", so it alone would order none of them.
  `fence.mbarrier_init` states that "the synchronizing effect of the fence only applies to the prior
  mbarrier.init operations executed by the same thread", and its example publishes the
  initialization by exactly this sequence. The reading picks the initializations only: the
  relaxed arrival orders no prior access by itself, the fence makes it order the thread's prior
  initializations, and nothing else.

Direction: reading

Effect: Wider than the text by the reading only: if the example does not order the initialization
  before the users after a peer's wait, a user's arrival or a copy's complete-tx may reach the
  object before its initialization (undefined behaviour, §9.7.15.16), which the model does not
  report. The init fence's release is not applied to any other operation of the thread. Disclosed by
  every kernel whose statement names `Op.fenceMbarInit`: FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192.
-/

/-- The restricted synchronization of an initialization: the shared::cta initialization
`init` of `m`, a `fence.mbarrier_init` and a cluster arrival (either qualifier) follow each other
in one thread, and the cluster wait `w` waited for the phase of the arrival in the cluster
barrier's history. -/
def InitFenceSync (L : Launch) (X : Execution) (m : Loc) (init w : EvId) : Prop :=
  ∃ count fence arrival pc pca release aligned pcw alignedw,
    X.MbInit init m count ∧ m.space = .shared ∧ m.cta = init.1 / L.block ∧
    X.get fence = some ⟨pc, .fenceMbarInit⟩ ∧
    init.1 = fence.1 ∧ init.2 < fence.2 ∧ fence.1 = arrival.1 ∧ fence.2 < arrival.2 ∧
    X.get arrival = some ⟨pca, .cluster (.arrive release aligned)⟩ ∧
    X.get w = some ⟨pcw, .cluster (.wait alignedw)⟩ ∧
    ∃ c phase, ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt c) (X.clusters c) arrival phase
        release ∧ ClusterBarrier.WaitOf L.block (L.clusterSizeAt c) (X.clusters c) w phase

/-- The initialization `init` of `m` is published to `user` through the init fence: the wait of
an `InitFenceSync` for it happens before `user`. -/
def InitFencePublished (L : Launch) (X : Execution) (init user : EvId) (m : Loc) : Prop :=
  ∃ w, InitFenceSync L X m init w ∧ baseCausality L X w user

/-- The initialization `init` of `m` is published to `user`: it happens before `user`, or it is
published through the init fence and a cluster barrier (`InitFencePublished`). -/
def InitPublished (L : Launch) (X : Execution) (init user : EvId) (m : Loc) : Prop :=
  baseCausality L X init user ∨ InitFencePublished L X init user m

/-- An operation of `m` whose issue the wait of an `InitFenceSync` causally precedes is not
before the initialization in `m`'s history. -/
def InitFenceOrdered (L : Launch) (X : Execution) : Prop :=
  ∀ m init w (y : AsyncCopy.Ref), InitFenceSync L X m init w →
    Relation.TransGen (stageCausality L X) (.thread w, true) (.thread y.issuer, false) →
    ¬ MBarrier.Before (X.objects m) y (.thread init)

/-! ## ERR-MBAR-UNINITIALIZED — every mbarrier operation uses an initialized object
Statement: An execution is unsafe when an instruction other than `mbarrier.init` names an mbarrier
  object as an operand and no initialization of that object is published to its issue. This covers
  the thread's own mbarrier operations, the asynchronous operations that complete on an mbarrier,
  the targets of `tcgen05.commit` and the response mbarriers of a CLC request.

Defs: MbarUninit

Source:
- §9.7.15.16: "Performing any mbarrier operation except mbarrier.init on an uninitialized mbarrier
    object results in undefined behavior."
- §9.7.15.16.13: "Performing any mbarrier operation except mbarrier.init on a memory location that
    does not contain a valid mbarrier object , results in undefined behavior."
- §9.7.10.28.4.1 (generic-proxy mbarrier operand)
- §9.7.10.28.5.3 (generic-proxy mbarrier operand)
- §9.7.18.12.1 (generic-proxy mbarrier operand)
- OBJ-MBAR-INIT-PUBLICATION

Direction: stricter

Applies: Every event that names an mbarrier operand (`Execution.UsesMbar`) and is not its
  initialization: arrivals, polls, invalidations, linear copies and tensor loads with mbarrier
  completion, `cp.async.mbarrier.arrive`, every target of a `tcgen05.commit`, and the response
  mbarrier of every target CTA of a CLC request

Premises: An initialization of the object is published to the issue (`InitPublished`: it happens
  before the issue, or it is published through `fence.mbarrier_init` and a cluster barrier).

Effect: Safety rejection. The exact lifetime of each operation that reaches the object history is
  ERR-OBJECT-LIFETIME (`ObjectPublished`). The storage of the object is ERR-UNALLOCATED-ACCESS.

Review: The check is made at the issue of an instruction, also for an asynchronous operation that
  reaches the object later. This is stricter than the text, which constrains the operation on the
  object: an initialization that is ordered before the completion and after the issue is rejected.
  An asynchronous operation whose completion never reaches the object, such as a pending copy or an
  undelivered commit, is still checked. The publication goes through the generic proxy, so no
  async-proxy fence is needed.
-/

/-- Some event names an mbarrier object as an operand, is not an initialization of it, and no
initialization of that object is published to it. -/
def MbarUninit (L : Launch) (X : Execution) : Prop :=
  ∃ e m, X.UsesMbar e m ∧ (∀ count, ¬ X.MbInit e m count) ∧
    ¬ ∃ i count, X.MbInit i m count ∧ InitPublished L X i e m

end
end PTX
