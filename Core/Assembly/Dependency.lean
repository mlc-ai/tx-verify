-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.WaitOrder
public import Core.Sync.MatrixExec
public import Core.Sync.Aligned
public import Core.Assembly.PollShape
public import Core.Tmem.AllocResult

@[expose] public section

/-!
# The dependency order (execution layer)

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## DEP-ORDER — a thread resumes only after what its instruction waits for
Statement: A blocking instruction returns only when every need of its wait condition is filled, and
  every later event of its thread comes after the return; where the manual says "non-exited", a
  participant's exit fills its need. A poll returns at once, and when it reports a completed phase
  and is a canonical spin, the events after the spin's exit come after the return. Each return comes
  after the events that fill its needs, and the dependency order these edges form, together with the
  order of any one synchronization object, has no cycle.

Defs: Resume, TcKind.resume, Kind.resume, Need, needsIf, warpLane, warpLanes, maskNeeds, tcNeeds,
  ctaBarWarpNeeds, CtaBarCounted, ctaBarNeeds, clusterWarpNeeds, ClusterCounted, clusterNeeds,
  ReuseRelease, Tmem.Pair.AllocResultFill, Tmem.Pair.allocResultNeeds,
  Tmem.Pair.AllocResultFill.written, Tmem.Pair.allocResultNeeds_node,
  Tmem.Pair.allocResultNeeds_transport, resourceNeeds, groupNeeds,
  pollNeeds, KindNeeds, kindNeeds_free, Needs, Ready,
  Witness, Returned, SpinExit, Resumes, DepStep, DependencyOk, Witness.of_need,
  Resumes.of_blocking, DepStep.of_witness, DepStep.of_resumes, maskNeeds_mem,
  ctaBarCounted_witnessed, covered_witnessed, allocResult_witnessed

Source:
- §9.7.15.10: "vote.sync will cause executing thread to wait until all non-exited threads
    corresponding to membermask have executed vote.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.10.6 (shfl.sync): "wait until all non-exited threads corresponding to membermask have
    executed shfl.sync with the same qualifiers and same membermask value before resuming execution"
- §9.7.15.11: "match.sync will cause executing thread to wait until all non-exited threads from
    membermask have executed match.sync with the same qualifiers and same membermask value before
    resuming execution."
- §9.7.15.13: "redux.sync will cause the executing thread to wait until all non-exited threads
    corresponding to membermask have executed redux.sync with the same qualifiers and same
    membermask value before resuming execution."
- §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to
    wait until all threads in the membermask execute the elect instruction before resuming
    execution."
- §9.7.15.2 (bar.warp.sync)
- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier."
- §9.7.15.1 (bar.sync waits for the non-exited threads of all other warps participating)
- §9.7.14.7: "Barriers exclusively waiting on arrivals from exited threads are always released."
- §9.7.15.3 (barrier.cluster: the warp rendezvous and the wait for all non-exited threads)
- §9.7.16.5.15: "The mandatory .sync qualifier indicates that ldmatrix causes the executing thread
    to wait until all threads in the warp execute the same ldmatrix instruction before resuming
    execution."
- §9.7.16.5.17: "The mandatory .sync qualifier indicates that movmatrix causes the executing thread
    to wait until all threads in the warp execute the same movmatrix instruction before resuming
    execution."
- §9.7.16.5.14 (mma), §9.7.16.5.16 (stmatrix), §9.7.16.6.3 (mma.sp)
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- §9.7.18.8.5 (.sync): "causes the executing thread to wait until all threads in the warp execute
    the same tcgen05.wait_operation instruction before resuming execution"
- §9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not available
    and unblocks as soon as the requested amount of Tensor Memory becomes available for
    allocation."
- §9.7.18.7.1: "When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "tcgen05.dealloc may block to collectively performs the deallocation with the other
    peer CTA ’s warp"
- §9.7.10.28.6.2 (cp.async.bulk.wait_group)
- §9.7.10.28.3.3 (cp.async.wait_group)
- §9.7.15.16.19: "If the phase is not complete, the executing thread may be suspended."
- §9.7.15.16.19: "Suspended thread resumes execution when the specified phase completes OR before
    the phase completes following a system-dependent time limit."
- §9.7.15.16.19: "mbarrier.test_wait is a non-blocking instruction which tests for the completion
    of the phase."
- EXT-TMEM-ALLOC-RESULT-ORDER
- EXT-ENABLES-OBJECT
- EXT-STAGE-ORDER
- EXT-WARP-INSTANCE
- EXT-SETMAXNREG-EFFECTIVE (the wait for the CTA's register pool is not a need)

Direction: reading

Applies: every event kind (`Kind.resume` and `KindNeeds` are total)

Premises: none

Effect: `Consistent.dependency`. Used by Maximal and FairRun through Consistent, by
  ERR-NONUNIFORM-GUARD (the dependency order of EXT-DEPENDENCY-ORDER) and by ERR-SHARED-LIFETIME.
  Not used by `baseCausality`, `stageCausality`, `ObservationCausal`, `ObjectCoherent` or any memory
  axiom. `Kind.resume` classifies every kind: free (the thread goes on at once; loads, stores,
  atomics, issues of asynchronous operations, fences, queries), blocking with the completed instance
  recorded (vote, ballot, redux, match, shfl, elect, `bar.warp.sync`, the warp-level matrix
  instructions: the event exists only when its needs are filled), blocking at the arrival
  (`bar.sync`, `bar.arrive`, `barrier.cluster`, the group waits, setmaxnreg, the `.sync` tcgen05
  instructions: the event exists at the arrival and returns when the next event of its thread
  exists), and observing (the mbarrier polls). `KindNeeds` lists the needs of each kind:
  - `shfl.sync`, `vote.sync` (both forms), `redux.sync`, `match.sync`: for each lane of the member
    mask, its event of the same instance with the same qualifiers, or its exit before it
    (`MaskWait`, DEP-WARP-INSTANCE).
  - `elect.sync`, `bar.warp.sync`: for each lane of the mask, its event of the instance (its label).
  - warp-level matrix instructions: for each of the 32 lanes, its event of the same ordinal, or its
    exit short of it (the instance then exists and ERR-ALIGNED-MISMATCH reports the undefined
    behaviour).
  - setmaxnreg: for each of the 32 lanes, the same request (`SetMaxNReg.SameRequest`).
  - `tcgen05.ld`, `tcgen05.st` and their waits: for each lane of the warp, its warp-collective
    tcgen05 event of the same ordinal (`Execution.TcK`).
  - Tensor Memory allocation management: the lanes as above; the allocator has performed the
    request (`Tmem.Pair.Performed`); when the instruction waits for its operation
    (`Tmem.Pair.MustWait`), the operation is complete (`Tmem.Pair.Covered`), for a `cta_group::2`
    instruction the peer warp's lanes are needs, and for an allocation the lanes of every release
    that last freed a column of the returned range are needs (`ReuseRelease`). For nonleader
    lanes of an allocation, the actual result store of the local leader is also a need
    (`Tmem.Pair.AllocResultFill`, EXT-TMEM-ALLOC-RESULT-ORDER).
  - `bar.sync`, `bar.arrive`: for each lane of the warp, its arrival in the event's record, or its
    exit recorded before that record; for `bar.sync`, also the release of its generation, and every
    arrival of the generation and every exit recorded up to the release (`CtaBarCounted`).
  - `barrier.cluster.arrive`, `barrier.cluster.wait`: for each lane of the warp, its event in the
    same record, or its exit recorded before it; for a wait, also every arrival of the phase it
    waits for and every exit of the cluster recorded before its record (`ClusterCounted`).
  - `cp.async.bulk.wait_group{.read}`, `cp.async.wait_group`: the stages `GroupWaitStages` of every
    covered operation (DEP-ASYNC-STAGE-ORDER).
  - a successful poll: each counter update of the phase it observed (`MbarObserved`); a failed
    poll has no need.
  `Returned` says which events must be ready, `Witness` which nodes fill a need, and `Resumes`
  which events follow a return: every later event of the thread of a blocking event, and, for a
  successful poll of a canonical spin, every later event of its thread (`SpinExit`); a poll whose
  result is not read, and a failed poll, are followed by nothing. `DependencyOk.acyclic` excludes
  a cycle of `DepStep` with the order of one object of `OrderObject.Enabling`.

Review: The dependency order decides which executions can exist and complete. It is never part of
  base causality, causality, coherence or any rule about the values that reads return: after a
  `vote.sync` in each of two lanes, a weak store of one lane may be read by a load of the other lane
  before the vote (K2 and K3 in `Tests/Progress/DependencyLitmus.lean`). The edges are orders the
  hardware respects: the waiting sentences above (a return comes after its witnesses), the thread
  executing no later instruction before the return, a spin left only through the branch on its
  successful poll, the stage order (EXT-STAGE-ORDER) and one object's order (EXT-OBJECT-ORDER).
  Where a need is a condition on an object history (a CTA barrier generation released, a Tensor
  Memory operation complete), the records that make it true are needs beside it:
  `ctaBarCounted_witnessed` and `covered_witnessed`. Every exit recorded up to a release is a need
  of a `bar.sync`, also an exit of a warp that arrived: each such exit precedes the release in the
  barrier's order. The completeness checks (one oracle per family transcribed from its sentence,
  three examples per kind, the name scan of `tests/test_dependency.py` and the mutation run) are in
  `Tests/Progress/DependencyCoverage.lean`.

### EXT-ENABLES-OBJECT — an event that exists because of a return is not placed before its witness

Statement: An event that exists only because a thread resumed from a blocking instruction, or
  follows the exit of a canonical spin whose successful poll observed a record, is never placed
  before a witness of that return in the order of a synchronization object. Program order alone,
  as after a single poll whose result no instruction reads, creates no dependency; every other use
  of a poll result is unsafe (ERR-POLL-SHAPE).

Source:
- §9.7.15.16.8 (atomic phase transition)
- §9.7.15.16.19 (a poll returns at once with whether the phase completed)
- the waiting sentences quoted in DEP-ORDER

Why it is not spec text: The instruction descriptions state what a thread waits for. They do not
  state that the order of a synchronization object agrees with these waits. The reading is the
  physical dependency: an operation cannot be performed before the observation or the return that
  it needed.

Direction: reading

Effect: Executions in which an event that exists only because of a return is placed before a
  witness of that return in one object's order are removed from `Consistent`
  (`DependencyOk.acyclic`); if hardware allows them, the model excludes executions that may occur.
  The load buffering through two mbarriers with single relaxed polls (K1 in
  `Tests/Progress/DependencyLitmus.lean`) stays allowed, while the same shape with canonical spins
  is excluded. Disclosed by every kernel whose statement names `Op.mbarInit`, `Op.mbarArrive`,
  `Op.mbarWait`, `Op.barSync`, `Op.barSyncN`, `Op.barArrive` or `Op.cluster`: BlockSum,
  FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.
-/

/-- When an event of a thread lets the thread go on (execution layer). -/
inductive Resume where
  /-- The thread goes on at once. Its result, if any, is computed from the thread's state or is a
  memory read decided by the memory layer. -/
  | free
  /-- The thread goes on only after its needs are filled, and every later event of the thread
  depends on the return. `completed` is true when the event records the completed instance, and
  false when it records the arrival and the return is the existence of the next event. -/
  | blocking (completed : Bool)
  /-- The instruction returns at once with a result that may report an observation (a poll). -/
  | observing
  deriving DecidableEq, Repr

/-- The resume class of every `tcgen05` kind (no wildcard). -/
def TcKind.resume : TcKind → Resume
  | .resource .. | .ld .. | .st .. | .waitLd | .waitSt => .blocking false
  | .mma .. | .commit _ | .cp _ | .shift _ | .fenceBefore | .fenceAfter => .free

/-- The resume class of every event kind (no wildcard). -/
def Kind.resume : Kind → Resume
  | .warpBar .. | .elect .. => .blocking true
  | .shfl .. | .vote .. | .voteMode .. | .redux .. | .match_ .. | .matrix .. => .blocking true
  | .setMaxReg .. => .blocking false
  | .bar .. => .blocking false
  | .cluster _ => .blocking false
  | .bulkWait .. | .asyncWait _ => .blocking false
  | .wait .. => .observing
  | .rd .. | .nc .. | .wr .. | .rmw .. => .free
  | .clcQuery .. => .free
  | .clcIssue .. | .tensorIssue .. | .tensorStore .. | .copy _ | .bulkPrefetch _
  | .tensorPrefetch .. | .asyncArrive .. => .free
  | .bulkCommit | .asyncCommit => .free
  | .activemask _ | .sreg .. | .exit | .ub _ => .free
  | .mbInit .. | .mbInval _ | .fence .. | .fenceProxy .. | .fenceMbarInit | .arrive .. => .free
  | .tc k => k.resume

/-- One thing a blocking return waits for. -/
inductive Need where
  /-- A present node with this property: a participant's matching event, the exit of a
  participant, a record of an object history, or an asynchronous stage. -/
  | node (fills : AsyncCopy.Ref → Prop)
  /-- A condition on an object history; the records that make it true are `node` needs beside
  it. -/
  | cond (holds : Prop)

open Classical in
/-- The needs `ns` when `P` holds, and none otherwise. -/
def needsIf (P : Prop) (ns : List Need) : List Need := if P then ns else []

/-- Lane `l` of the warp of thread `g`. -/
def warpLane (g l : Nat) : Nat := g - laneOf L g + l

/-- The threads of the warp of thread `g`. -/
def warpLanes (g : Nat) : List Nat := (List.range (warpSize L g)).map (warpLane L g)

/-- The needs of a masked warp collective of class `c` (DEP-WARP-INSTANCE): for each lane of the
member mask, its event of the instance with the same qualifiers, or its exit before it. -/
def maskNeeds {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (e : EvId) :
    List Need :=
  match (X.get e).bind fun ev => c ev.kind with
  | some p => ((List.range 32).filter fun l => p.mask.testBit l).map fun l =>
      .node fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧ MaskWait L c X (warpLane L e.1 l, j) e
  | none => []

/-- The needs of a warp-collective `tcgen05` event: each lane's event of the same ordinal. -/
def tcNeeds (X : Execution) (e : EvId) : List Need :=
  (warpLanes L e.1).map fun h => .node fun x =>
    ∃ j, x = .thread (h, j) ∧ X.TcK (h, j) (((X.tr e.1).take e.2).countP isTcColl)

/-- The warp needs of a CTA barrier arrival: for each lane of the warp, its arrival in the record
of `e`, or its exit recorded before that record. -/
def ctaBarWarpNeeds (X : Execution) (e : EvId) : List Need :=
  (warpLanes L e.1).map fun h => .node fun x =>
    ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y, (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧
      x = .thread y ∧ y.1 = h ∧
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧ (X.barriers (e.1 / L.block))[j]? =
        some (CtaBarrier.Record.exit g y))

/-- `y` is a record reference counted by the release of the generation of the `bar.sync` `e`: an
arrival of that generation, or an exit recorded up to the release. -/
def CtaBarCounted (X : Execution) (e y : EvId) : Prop :=
  ∃ key ic, CtaBarK L X e key ∧
    CtaBarrier.CompletesAt L.block (X.barriers (e.1 / L.block)) ic (key % 16) (key / 16) ∧
    ∃ i, ∃ r : CtaBarrier.Record EvId, (X.barriers (e.1 / L.block))[i]? = some r ∧ y ∈ r.refs ∧
      i ≤ ic ∧
      ((∃ w count lanes s, r = .arrival (key % 16) w count lanes ∧
          CtaBarrier.At L.block (X.barriers (e.1 / L.block)) i s ∧
          (s.slots (key % 16)).generation = key / 16) ∨
        ∃ g, r = CtaBarrier.Record.exit g y)

/-- The needs of a CTA barrier arrival of mode `mode`. -/
def ctaBarNeeds (X : Execution) (e : EvId) (mode : BarMode) : List Need :=
  ctaBarWarpNeeds L X e ++ match mode with
    | .sync => .cond (∃ key, CtaBarK L X e key ∧ CtaBarDone L X (e.1 / L.block) key) ::
        ((X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs).flatMap fun y =>
          needsIf (CtaBarCounted L X e y) [.node (· = .thread y)]
    | .arrive => []

/-- The warp needs of a cluster barrier operation: for each lane of the warp, its event in the
record of `e`, or its exit recorded before that record. -/
def clusterWarpNeeds (X : Execution) (e : EvId) : List Need :=
  (warpLanes L e.1).map fun h => .node fun x =>
    ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
      (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
      x = .thread y ∧ y.1 = h ∧
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧ (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? =
        some (ClusterBarrier.Record.exit g y))

/-- `y` is counted by the completion of the phase that the cluster wait `e` waits for: an arrival
of that phase, or an exit of the cluster recorded before the record of `e`. -/
def ClusterCounted (X : Execution) (e y : EvId) : Prop :=
  (∃ phase release,
    ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1 / L.block)))
      (X.clusters (L.clusterOfCta (e.1 / L.block))) e phase ∧
    ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1 / L.block)))
      (X.clusters (L.clusterOfCta (e.1 / L.block))) y phase release) ∨
  ∃ (i j : Nat), ∃ r : ClusterBarrier.Record EvId, ∃ g : Nat,
    (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
    (∃ cta w lanes, r = ClusterBarrier.Record.wait cta w lanes) ∧ j < i ∧
    (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? = some (ClusterBarrier.Record.exit g y)

/-- The needs of a cluster barrier operation. -/
def clusterNeeds (X : Execution) (e : EvId) (op : ClusterOp) : List Need :=
  clusterWarpNeeds L X e ++ match op with
    | .wait _ =>
      ((X.clusters (L.clusterOfCta (e.1 / L.block))).flatMap ClusterBarrier.Record.refs).flatMap
        fun y => needsIf (ClusterCounted L X e y) [.node (· = .thread y)]
    | .arrive .. => []

/-- The `j`-th record of the allocator history of the CTA of `e` is a release that last freed a
column of the range the allocation `e` returned: no later release before the allocation frees that
column. -/
def ReuseRelease (X : Execution) (e : EvId) (j : Nat) : Prop :=
  ∃ i r d n base b' n', (X.tmemHistory (e.1 / L.block))[i]? = some r ∧
    Tmem.Pair.Participates L r.own e ∧ r.action = .alloc n base ∧
    (X.tmemHistory (e.1 / L.block))[j]? = some d ∧ j < i ∧ d.action = .dealloc b' n' ∧
    ∃ col, base ≤ col ∧ col < base + n ∧ b' ≤ col ∧ col < b' + n' ∧
      ∀ k d' b'' n'', j < k → k < i → (X.tmemHistory (e.1 / L.block))[k]? = some d' →
        d'.action = .dealloc b'' n'' → ¬ (b'' ≤ col ∧ col < b'' + n'')

namespace Tmem.Pair

/-- The node supplying the local result of the participant's allocation. -/
def AllocResultFill (L : Launch) (X : Execution) (i : EvId) : AsyncCopy.Ref → Prop
  | .thread store => ∃ dst, AllocResult L X store i dst
  | .async .. => False

/-- A nonleader allocation waits for its leader's result store. The leader reaches that store
without waiting for the store itself. -/
def allocResultNeeds (L : Launch) (X : Execution) (i : EvId) : Tmem.Request → List Need
  | .alloc _ => if laneOf L i.1 = 0 then [] else [.node (AllocResultFill L X i)]
  | _ => []

/-- The extra return need identifies the local result store. -/
theorem allocResultNeeds_node {X : Execution} {i : EvId} {request : Tmem.Request} {n : Need}
    (h : n ∈ allocResultNeeds L X i request) :
    n = .node (AllocResultFill L X i) := by
  cases request <;> simp only [allocResultNeeds] at h
  case alloc =>
    split at h
    · exact (List.not_mem_nil h).elim
    · exact List.mem_singleton.mp h
  all_goals exact (List.not_mem_nil h).elim

/-- A need for the allocation result has the same shape in any execution. -/
theorem allocResultNeeds_transport {X Y : Execution} {i : EvId} {request : Tmem.Request}
    {n : Need} (h : n ∈ allocResultNeeds L X i request) :
    Need.node (AllocResultFill L Y i) ∈ allocResultNeeds L Y i request := by
  cases request <;> simp only [allocResultNeeds] at h ⊢
  case alloc =>
    split at h
    · exact (List.not_mem_nil h).elim
    · rename_i hl
      simp [hl]
  all_goals exact (List.not_mem_nil h).elim

/-- A fill of this need is a thread's four-byte store. -/
theorem AllocResultFill.written {X : Execution} {i : EvId} {x : AsyncCopy.Ref}
    (h : AllocResultFill L X i x) :
    ∃ store site dst bytes, x = .thread store ∧
      X.get store = some ⟨site, .wr { loc := dst, size := 4 } bytes⟩ := by
  cases x with
  | async => exact h.elim
  | thread store =>
    obtain ⟨dst, _, _, _, _, _, site, _, _, _, bytes, _, _, _, _, _, he⟩ := h
    exact ⟨store, site, dst, bytes, rfl, he⟩

end Tmem.Pair

/-- The needs of a Tensor Memory allocation-management event. -/
def resourceNeeds (X : Execution) (e : EvId) (group : CtaGroup) (request : Tmem.Request) :
    List Need :=
  (tcNeeds L X e ++ .cond (Tmem.Pair.Performed L X e) ::
    needsIf (Tmem.Pair.MustWait X e)
      (.cond (Tmem.Pair.Covered L X e) ::
        (match group with
          | .two => (List.finRange 32).map fun l => .node fun x =>
              ∃ q ∈ X.tmemPairing, (Tmem.Pair.Participates L q.1 e ∧ x = .thread (q.2.event L l)) ∨
                (Tmem.Pair.Participates L q.2 e ∧ x = .thread (q.1.event L l))
          | .one => []) ++
        match request with
        | .alloc _ => (List.range (X.tmemHistory (e.1 / L.block)).length).flatMap fun j =>
            needsIf (ReuseRelease L X e j) ((List.finRange 32).map fun l => .node fun x =>
              ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧ x = .thread (d.own.event L l))
        | _ => [])) ++ Tmem.Pair.allocResultNeeds L X e request

/-- The needs of a group wait of kind `k`: the stages `GroupWaitStages` of every operation it
covers (DEP-ASYNC-STAGE-ORDER). -/
def groupNeeds (X : Execution) (e : EvId) (k : GroupWait) : List Need :=
  (List.range e.2).flatMap fun j => needsIf (GroupWaitsFor X k (e.1, j) e)
    ((GroupWaitStages X (e.1, j) k).map fun p => .node (· = .async (e.1, j) p))

/-- The needs of a successful poll: each counter update of the phase it observed. -/
def pollNeeds (X : Execution) (e : EvId) (m : Loc) : List Need :=
  (X.objects m).flatMap fun r => needsIf (MbarObserved X r.id (.thread e)) [.node (· = r.id)]

/-- The needs of event `e` of kind `k` (no wildcard). A free kind has no needs
(`kindNeeds_free`). -/
def KindNeeds (X : Execution) : Kind → EvId → List Need
  | .shfl .., e => maskNeeds L shflClass X e
  | .vote .., e | .voteMode .., e => maskNeeds L voteClass X e
  | .redux .., e => maskNeeds L reduxClass X e
  | .match_ .., e => maskNeeds L matchClass X e
  | .elect mask inst _, e => ((List.range 32).filter fun l => mask.testBit l).map fun l =>
      .node fun x => ∃ j pc leader, x = .thread (warpLane L e.1 l, j) ∧
        X.get (warpLane L e.1 l, j) = some ⟨pc, .elect mask inst leader⟩
  | .warpBar mask inst, e => ((List.range 32).filter fun l => mask.testBit l).map fun l =>
      .node fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
        X.WarpBar (warpLane L e.1 l, j) mask inst
  | .matrix .., e => (List.range 32).map fun l => .node fun x =>
      ∃ j, x = .thread (warpLane L e.1 l, j) ∧
        (X.MatrixK (warpLane L e.1 l, j) (((X.tr e.1).take e.2).countP isMatrix) ∨
          X.ExitedShort isMatrix (warpLane L e.1 l, j) (((X.tr e.1).take e.2).countP isMatrix))
  | .setMaxReg .., e => (List.range 32).map fun l => .node fun x =>
      ∃ j, x = .thread (warpLane L e.1 l, j) ∧ SetMaxNReg.SameRequest L X e (warpLane L e.1 l, j)
  | .bar _ _ mode, e => ctaBarNeeds L X e mode
  | .cluster op, e => clusterNeeds L X e op
  | .bulkWait mode _, e => groupNeeds X e (.bulk mode)
  | .asyncWait _, e => groupNeeds X e .cpAsync
  | .wait m _ ok _ _, e => if ok then pollNeeds X e m else []
  | .tc (.resource group _ request), e => resourceNeeds L X e group request
  | .tc (.ld ..), e | .tc (.st ..), e | .tc .waitLd, e | .tc .waitSt, e => tcNeeds L X e
  | .tc (.mma ..), _ | .tc (.commit _), _ | .tc (.cp _), _ | .tc (.shift _), _
  | .tc .fenceBefore, _ | .tc .fenceAfter, _ => []
  | .rd .., _ | .nc .., _ | .wr .., _ | .rmw .., _ | .clcQuery .., _ | .clcIssue .., _
  | .tensorIssue .., _ | .tensorStore .., _ | .copy _, _ | .bulkPrefetch _, _
  | .tensorPrefetch .., _ | .asyncArrive .., _ | .bulkCommit, _ | .asyncCommit, _
  | .activemask _, _ | .sreg .., _ | .exit, _ | .ub _, _ | .mbInit .., _ | .mbInval _, _
  | .fence .., _ | .fenceProxy .., _ | .fenceMbarInit, _ | .arrive .., _ => []

/-- A free kind has no needs. -/
theorem kindNeeds_free (X : Execution) (k : Kind) (e : EvId) (h : k.resume = .free) :
    KindNeeds L X k e = [] := by
  cases k with
  | tc t => cases t <;> simp_all [Kind.resume, TcKind.resume, KindNeeds]
  | _ => simp_all [Kind.resume, KindNeeds]

/-- The needs of event `e`. -/
def Needs (X : Execution) (e : EvId) : List Need :=
  match X.get e with
  | none => []
  | some ev => KindNeeds L X ev.kind e

/-- Every need of `e` is filled. -/
def Ready (X : Execution) (e : EvId) : Prop :=
  ∀ n ∈ Needs L X e, match n with
    | .node fills => ∃ x, X.RefPresent x ∧ fills x
    | .cond holds => holds

/-- `x` fills a need of `e`: a witness of `e`'s return or result. -/
def Witness (X : Execution) (x : AsyncCopy.Ref) (e : EvId) : Prop :=
  ∃ fills, Need.node fills ∈ Needs L X e ∧ X.RefPresent x ∧ fills x

/-- The event has returned: a completed-instance event exists, an arrival-style event has a later
event in its thread, and a successful poll exists. -/
def Returned (X : Execution) (e : EvId) : Prop :=
  match X.get e with
  | some ⟨_, .wait _ _ ok _ _⟩ => ok = true
  | some ev => match ev.kind.resume with
    | .blocking true => True
    | .blocking false => e.2 + 1 < (X.tr e.1).length
    | _ => False
  | none => False

/-- `w` is a successful poll of a canonical spin of `K` and `f` is a later event of its thread
(DEP-CANONICAL-SPIN). -/
def SpinExit (K : Kernel) (X : Execution) (w f : EvId) : Prop :=
  ∃ pc exit m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ ∧ K.CanonicalSpin pc exit ∧
    TraceBefore X w f

/-- The thread event `f` depends on the return of `w`: `w` is blocking and `f` follows it, or `w`
is the successful poll of a canonical spin and `f` follows it. -/
def Resumes (K : Kernel) (X : Execution) (w f : EvId) : Prop :=
  TraceBefore X w f ∧ match ((X.get w).map fun ev => ev.kind.resume : Option Resume) with
    | some (Resume.blocking _) => True
    | some Resume.observing => SpinExit K X w f
    | _ => False

/-- One step of the dependency order on nodes (execution layer): the stage order, the issue of an
asynchronous operation before its stages, a witness before the return it fills, and a return
before the events that depend on it. -/
def DepStep (K : Kernel) (X : Execution) :
    AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | (e, b), (f, b') =>
    StageOrder X (e, b) (f, b') ∨ IssueStage X (e, b) (f, b') ∨
    (b = false ∧ b' = true ∧ ∃ j, f = .thread j ∧ Witness L X e j) ∨
    (b = true ∧ b' = false ∧ ∃ w j, e = .thread w ∧ f = .thread j ∧ Resumes K X w j)

/-- DEP-ORDER: every returned event is ready, and the dependency order together with the
order of any single object of `OrderObject.Enabling` has no cycle. -/
structure DependencyOk (K : Kernel) (X : Execution) : Prop where
  ready : ∀ e, Returned X e → Ready L X e
  acyclic : ∀ o, o.Enabling → ∀ n,
    ¬ Relation.TransGen (fun a c => DepStep L K X a c ∨ ObjectOrder L X o a c) n n

/-- A present node that fills a need of `e` is a witness of `e`. -/
theorem Witness.of_need {X : Execution} {e : EvId} {x : AsyncCopy.Ref}
    {fills : AsyncCopy.Ref → Prop} (hn : Need.node fills ∈ Needs L X e) (hx : X.RefPresent x)
    (hf : fills x) : Witness L X x e :=
  ⟨fills, hn, hx, hf⟩

/-- Every later event of the thread of a blocking event depends on its return. -/
theorem Resumes.of_blocking {K : Kernel} {X : Execution} {w f : EvId} {ev : Event} {b : Bool}
    (hw : X.get w = some ev) (hb : ev.kind.resume = .blocking b) (hf : TraceBefore X w f) :
    Resumes K X w f := by
  refine ⟨hf, ?_⟩
  simp [hw, hb]

/-- A witness of `e` precedes the return of `e` in the dependency order. -/
theorem DepStep.of_witness {K : Kernel} {X : Execution} {x : AsyncCopy.Ref} {e : EvId}
    (h : Witness L X x e) : DepStep L K X (x, false) (.thread e, true) :=
  .inr (.inr (.inl ⟨rfl, rfl, e, rfl, h⟩))

/-- The return of `w` precedes the issue of an event that depends on it. -/
theorem DepStep.of_resumes {K : Kernel} {X : Execution} {w f : EvId} (h : Resumes K X w f) :
    DepStep L K X (.thread w, true) (.thread f, false) :=
  .inr (.inr (.inr ⟨rfl, rfl, w, f, rfl, rfl, h⟩))

/-- The need of lane `l` of a masked collective of class `c`: when `e` is an event of the class
whose member mask names `l`, the event of lane `l` of the same instance, or its exit before it, is
a need of `e` (`MaskWait`). -/
theorem maskNeeds_mem {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (e : EvId)
    {ev : Event} {p : WarpPart Q V} (he : X.get e = some ev) (hc : c ev.kind = some p) {l : Nat}
    (hl : l < 32) (hm : p.mask.testBit l = true) :
    Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
      MaskWait L c X (warpLane L e.1 l, j) e) ∈ maskNeeds L c X e := by
  simp only [maskNeeds, he, Option.bind_some, hc, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨l, ⟨hl, hm⟩, rfl⟩

/-- The history condition of a `bar.sync` is witnessed: when its generation is released, every
reference that `CtaBarCounted` names is a need of it. -/
theorem ctaBarCounted_witnessed (X : Execution) (e y : EvId) {pc id : Nat}
    {count : Option Nat} (he : X.get e = some ⟨pc, .bar id count .sync⟩)
    (hy : y ∈ (X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs)
    (hc : CtaBarCounted L X e y) : Need.node (· = .thread y) ∈ Needs L X e := by
  classical
  simp only [Needs, he, KindNeeds, ctaBarNeeds, needsIf, List.mem_append, List.mem_cons,
    List.mem_flatMap]
  exact .inr (.inr ⟨y, List.mem_flatMap.mp hy, by simp [hc]⟩)

/-- The allocation result store is a return dependency of every participating nonleader. -/
theorem allocResult_witnessed (X : Execution) (e : EvId)
    {pc : Nat} {group : CtaGroup} {dst : Option Loc} {count : Nat}
    (he : X.get e = some ⟨pc, .tc (.resource group dst (.alloc count))⟩)
    (hlane : laneOf L e.1 ≠ 0) :
    Need.node (Tmem.Pair.AllocResultFill L X e) ∈ Needs L X e := by
  simp only [Needs, he, KindNeeds, resourceNeeds, List.mem_append]
  exact .inr (by simp [Tmem.Pair.allocResultNeeds, hlane])

/-- The history condition of a waiting `cta_group::2` allocation-management event is witnessed:
the lanes of the peer request of its pairing are needs of it. -/
theorem covered_witnessed (X : Execution) (e : EvId) {pc : Nat} {dst : Option Loc}
    {request : Tmem.Request} (he : X.get e = some ⟨pc, .tc (.resource .two dst request)⟩)
    (hw : Tmem.Pair.MustWait X e) (l : Fin 32) :
    Need.node (fun x => ∃ q ∈ X.tmemPairing,
      (Tmem.Pair.Participates L q.1 e ∧ x = .thread (q.2.event L l)) ∨
        (Tmem.Pair.Participates L q.2 e ∧ x = .thread (q.1.event L l))) ∈ Needs L X e := by
  classical
  simp only [Needs, he, KindNeeds, resourceNeeds, needsIf]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hw)]
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩

end

end PTX
