-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency

@[expose] public section

namespace PTX

/-! ## ERR-SHARED-LIFETIME — shared memory exists for every use and outlives its completion
Statement: A use of a CTA's shared memory by an instruction of another CTA must be preceded, in
  lifetime order, by an instruction of the owning CTA, which shows that the owner has started. If
  every thread of the owning CTA has exited, the use must have occurred and its completion must
  precede the exit of one of the owner's threads.

Defs: CommitNext, not_commitNext, TensorStore.Selected, TensorStore.ReadsDrainedBeforeExit,
  StoreReadsBeforeExit, LifetimeStep, lifetimeStep_noAssumedOrder, LifetimeOrder,
  CompletedBefore, CompletedBefore.of_storeReadsBeforeExit, StageUses, SharedUse,
  PeerSharedStarted, CtaExited, SharedFinished, SharedLifetimeUnsafe

Source:
- §2.2.2: "The executing CTA has to make sure that the shared memory of the peer CTA exists before
    communicating with it via shared memory and the peer CTA hasn’t exited before completing the
    shared memory operation."
- §5.1.7: "The shared ( .shared ) state space is a memory that is owned by an executing CTA"
- §9.7.15.18 (the response written to each target CTA): "The behavior of instruction with
    .multicast::cluster::all qualifier is undefined if any CTA in the cluster is exited."
- §9.7.10.28.1.2: "When the current phase of the mbarrier object is complete, it implies that all
    asynchronous operations tracked by this phase are complete"
- §9.7.10.28.6.2: "wait until only N or fewer of the most recent bulk async-groups are pending and
    all the prior bulk async-groups committed by the executing threads are complete"
- MEM-OBJECT-ORDER-CAUSALITY (`stageCausality`, `ObjectOrder`, ObjectCoherent)
- DEP-ORDER (`DepStep`, `Witness`, `DependencyOk`)
- EXT-ENABLES-OBJECT

Direction: reading

Applies: Every use of a CTA's shared memory (`SharedUse`), whether that CTA is the issuer's or
  another one: thread instructions and performed asynchronous stages that access it or operate on an
  mbarrier object in it, and, performed or not, the stage that completes an issued asynchronous
  operation's use of it

Premises: For a CTA other than the issuer's, an instruction of that CTA precedes the issuing
  instruction in `LifetimeOrder`. If the owning CTA has exited, the use has occurred and its
  completion precedes at least one of the owner's exit instructions (`SharedFinished`).

Effect: Unsafe rejects missing lifetime evidence. The rule is a safety check that is valid with
  any order: it only reads the orders it uses (`LifetimeOrder`, `CompletedBefore`) and adds no edge
  to any order, so it lives with the other Unsafe items in the assembly layer. The direction is
  `reading` because the second order of `LifetimeOrder` rests on EXT-ENABLES-OBJECT; the first order
  and the completion requirement are stricter than the text. §2.2.2 and §5.1.7 state one rule for
  every shared memory operation, whichever instruction performs it and whichever CTA owns the
  memory. The table of uses (`SharedUse`, with `StageUses` for the stages that complete an
  operation, which are the `AsyncCopy.FinalStage` table of DEP-ASYNC-STAGE-ORDER) is the only
  kind-specific part: Columns: Operation; Stage that completes its use of CTA `c`; `c`. Rows:
  - thread instruction — Stage that completes its use of CTA `c`: the instruction; `c`: the CTA of a
    shared location it accesses or of an mbarrier it operates on
  - `tcgen05.commit` — Stage that completes its use of CTA `c`: the issuing instruction; `c`: each
    CTA of the issuer's CTA group (§9.7.18.5)
  - any performed asynchronous stage — Stage that completes its use of CTA `c`: the stage; `c`: the
    CTA of a shared location it accesses or of an mbarrier it updates
  - tensor load — Stage that completes its use of CTA `c`: each data write (`.write (.load ..)`);
    `c`: the destination CTA
  - tensor load — Stage that completes its use of CTA `c`: its notification (`.notify .load`); `c`:
    the mbarrier's CTA
  - tensor store — Stage that completes its use of CTA `c`: its source reads' completion
    (`.readsDone`); `c`: the source CTA
  - linear copy completed through an mbarrier — Stage that completes its use of CTA `c`: its
    notification (`.notify .copy`); `c`: the CTA of its shared source or destination and the
    mbarrier's CTA
  - linear copy completed through an async-group (`.bulk_group`, `cp.async`) — Stage that completes
    its use of CTA `c`: its write (`.write .copy`); `c`: the CTA of its shared source or destination
  - `cp.async.mbarrier.arrive` — Stage that completes its use of CTA `c`: its arrive-on
    (`.arriveOn`, a performed stage that updates the mbarrier, as in the row above)
  - CLC request — Stage that completes its use of CTA `c`: its notification at `c` (`.notify (.cta
    c)`); `c`: each target CTA
  - `tcgen05.mma`, `tcgen05.cp` — Stage that completes its use of CTA `c`: its completion
    (`.mmaDone`); `c`: the CTAs holding its operands (`lowCta`, `highCta`; the copy's CTA)
  - `tcgen05.commit` — Stage that completes its use of CTA `c`: its arrival at rank `r` (`.tcNotify
    r`); `c`: the target mbarrier's CTA
  The completing stage of an asynchronous operation comes after its other stages in `StageOrder`, so
  when it is finished every performed stage of the operation is; a stage that never occurs (an
  out-of-bounds read of a tensor store) is no access.
  "Before" in §2.2.2 is read as one of two orders of issue/completion nodes, each acyclic in every
  consistent execution, and never joined with each other (`LifetimeOrder`):
  - base causality, a `stageCausality` path: program order and synchronizes-with between thread
    instructions (`baseCausality`, §8.9.5), the release complete-tx of a copy observed by an acquire
    wait, and the stages of one asynchronous operation. It has no cycle by ObjectCoherent.
  - dependency, a path of `DepStep` together with the order of one object of `OrderObject.Enabling`:
    a later instruction reached only because a spinning wait succeeded or a blocking instruction
    returned, a stage that exists only because its operation was issued or its previous stage
    completed, a return that needed the updates or participants it observed, and the atomic order of
    that one object. It has no cycle by `DependencyOk.acyclic` (EXT-ENABLES-OBJECT).

Review: The load buffering shape is Litmus C in `Tests/Memory/WaitOrderLitmusWitness.lean`, and
  `not_completedBefore` there shows that `LifetimeOrder` has no path from one arrival to the other.
  An observation is never followed by an unguarded program-order step, and the orders of two objects
  are never chained. Both compositions occur in load buffering through two mbarriers with single
  relaxed polls, a consistent execution in which each arrival would then precede the other;
  `LifetimeOrder` has no such path.
  Columns: Edge; Lean; PTX ISA 9.5; Basis. Rows:
  - an executed owner-CTA instruction → the issue of the access — Lean: `PeerSharedStarted`; PTX ISA
    9.5: §2.2.2 ("make sure that the shared memory of the peer CTA exists before communicating");
    Basis: reading: an instruction of the owner that completed shows that the owner CTA, and with it
    its shared memory (§5.1.7), exists
  - base causality path — Lean: `LifetimeOrder` (1st), `stageCausality`; PTX ISA 9.5: §8.9.5, and
    the sources of each `stageCausality` edge in MEM-OBJECT-ORDER-CAUSALITY; Basis: stated edges;
    their use as the order of §2.2.2 is a reading
  - dependency path with one object's order — Lean: `LifetimeOrder` (2nd), `DepStep`, `ObjectOrder`,
    `OrderObject.Enabling`; PTX ISA 9.5: the sources of each `DepStep` edge in DEP-ORDER;
    §9.7.15.16.8 (atomic phase transition); Basis: reading EXT-ENABLES-OBJECT
  - completion of an asynchronous stage → the return of a wait observing it — Lean:
    `CompletedBefore` (2nd), `Witness`; PTX ISA 9.5: §9.7.10.28.1.2 (a completed phase implies its
    tracked operations are complete), §9.7.10.28.6.2 (bulk-group wait); Basis: stated: an
    asynchronous stage is observed only through a phase or group whose completion includes it, so
    the observing return follows its completion; the path continues in the dependency order only
  - access completion → one owner thread's exit — Lean: `SharedFinished`; PTX ISA 9.5: §2.2.2 ("the
    peer CTA hasn’t exited before completing the shared memory operation"); Basis: stated; one owner
    exit suffices, as the CTA has not exited while one of its threads has not
  - - completion of the arrive-on of a `tcgen05.commit` at a site a kernel assumption selects with
    `commitInOrder` (ASM-INTERFACE) → start of the arrive-on, at the same rank, of the issuing
    thread's next commit — Lean: `LifetimeStep` (3rd), `CommitNext`; PTX ISA 9.5: none (§9.7.18.12.1
    orders a commit's arrive-on after the operations it tracks, "all prior async-tcgen05 operations
    initiated by the executing thread", and an earlier commit is not one of them); Basis: trust. The
    edge enters only the dependency order of `LifetimeOrder` and `CompletedBefore`. It is not part
    of `DepStep` or `DependencyOk`: it lets a lifetime proof use the next commit's arrive-on; the
    constraint that the selected arrive-on is performed whenever the next one is is the `wf` of the
    assumption (ASM-COMMIT-ORDER, `Assumption.commitPerformedAt`); with no site selected the edge is
    empty (`lifetimeStep_noAssumedOrder`)
  - selected tensor store's source read completion → its issuing thread's subsequent exit —
    Lean: `StoreReadsBeforeExit`, `LifetimeStep`; basis: per-kernel trust selected by
    `Assumption.storeReadsBeforeExit`. `TensorStore.ReadsDrainedBeforeExit` requires the read
    completion to have occurred. A kernel uses it as an execution constraint and establishes it
    when proving extensions. The edge is available for lifetime reasoning and says nothing about
    completion of the global writes or visibility of shared writes to the store.
  The startup witness is one actual instruction of the owner CTA. A partial execution with an owner
  thread still live does not need a future exit witness. Memory value publication is the separate
  visibility requirement of MEM-MODEL-CAUSALITY and MEM-READS-FROM.
-/

/-- The arrive-on at rank `r` of a `tcgen05.commit` at a site an assumption selects with
`commitInOrder`, and the arrive-on at the same rank of the next commit of the same thread; both
performed. -/
def CommitNext (A : List Assumption) (X : Execution) : AsyncCopy.Ref → AsyncCopy.Ref → Prop
  | .async i (.tcNotify r), .async j (.tcNotify r') =>
    r = r' ∧ i.1 = j.1 ∧ i.2 < j.2 ∧ X.RefPresent (.async i (.tcNotify r)) ∧
      X.RefPresent (.async j (.tcNotify r')) ∧
      (∃ pc s, X.get i = some ⟨pc, .tc (.commit s)⟩ ∧ A.any (·.commitInOrder pc) = true) ∧
      (∃ s, X.Commit j s) ∧ ∀ k, i.2 < k → k < j.2 → ¬ ∃ s, X.Commit (i.1, k) s
  | _, _ => False

/-- With no site selected by `commitInOrder`, `CommitNext` relates nothing. -/
theorem not_commitNext {A : List Assumption} {X : Execution}
    (h : ∀ a ∈ A, ∀ pc, a.commitInOrder pc = false) (e f : AsyncCopy.Ref) :
    ¬ CommitNext A X e f := by
  unfold CommitNext
  split
  · rintro ⟨-, -, -, -, -, ⟨pc, s, -, hA⟩, -⟩
    obtain ⟨a, ha, hd⟩ := List.any_eq_true.mp hA
    rw [h a ha pc] at hd
    cases hd
  · exact id

/-- An actual tensor store whose instruction site the selector includes. -/
def TensorStore.Selected (select : Nat → Bool) (X : Execution) (i : EvId) : Prop :=
  ∃ pc address spec, X.get i = some ⟨pc, .tensorStore address spec⟩ ∧ select pc = true

/-- Each selected tensor store's shared reads have completed when its issuer exits. -/
def TensorStore.ReadsDrainedBeforeExit (select : Nat → Bool) (X : Execution) : Prop :=
  ∀ ⦃i finish : EvId⦄, TraceBefore X i finish → TensorStore.Selected select X i →
    (∃ pc, X.get finish = some ⟨pc, .exit⟩) → X.AsyncPresent i .readsDone

/-- An assumption selects a tensor store's completed shared reads before its issuer's exit. -/
def StoreReadsBeforeExit (A : List Assumption) (X : Execution) :
    AsyncCopy.Ref → AsyncCopy.Ref → Prop
  | .async i .readsDone, .thread finish =>
    TraceBefore X i finish ∧
    TensorStore.Selected (fun pc => A.any (·.storeReadsBeforeExit pc)) X i ∧
    (∃ pc, X.get finish = some ⟨pc, .exit⟩) ∧ X.AsyncPresent i .readsDone
  | _, _ => False

/-- One step of the dependency order with the order of object `o`: a `DepStep` edge
(DEP-ORDER), an edge of `o`'s order, or an assumed completion followed by an issue. -/
def LifetimeStep (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (o : OrderObject) (c d : AsyncCopy.Ref × Bool) : Prop :=
  DepStep L K X c d ∨ ObjectOrder L X o c d ∨
    (c.2 = true ∧ d.2 = false ∧
      (CommitNext A X c.1 d.1 ∨ StoreReadsBeforeExit A X c.1 d.1))

/-- With no assumption selecting a lifetime edge, a step is a dependency or object-order edge. -/
theorem lifetimeStep_noAssumedOrder {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution} {o : OrderObject}
    (hcommit : ∀ a ∈ A, ∀ pc, a.commitInOrder pc = false)
    (hdrain : ∀ a ∈ A, ∀ pc, a.storeReadsBeforeExit pc = false)
    {c d : AsyncCopy.Ref × Bool} :
    LifetimeStep L K A X o c d ↔ DepStep L K X c d ∨ ObjectOrder L X o c d := by
  unfold LifetimeStep
  have hc := not_commitNext hcommit (X := X) c.1 d.1
  have hd : ¬ StoreReadsBeforeExit A X c.1 d.1 := by
    unfold StoreReadsBeforeExit
    split
    · rintro ⟨-, ⟨pc, -, -, -, h⟩, -, -⟩
      obtain ⟨a, ha, hsel⟩ := List.any_eq_true.mp h
      simp [hdrain a ha pc] at hsel
    · exact id
  tauto

/-- Lifetime order of two nodes: a path of base causality, or a path of the dependency order
together with the order of one object of `OrderObject.Enabling` (`LifetimeStep`). -/
def LifetimeOrder (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (a b : AsyncCopy.Ref × Bool) : Prop :=
  Relation.TransGen (stageCausality L X) a b ∨
  ∃ o, o.Enabling ∧ Relation.TransGen (LifetimeStep L K A X o) a b

/-- The completion of `e` precedes the node `n`: a lifetime-order path from the completion
node of `e`, or, for an asynchronous stage, a dependency path (with one object's order) from
the return of a wait that the stage is a witness of (a group wait covering it, or a successful
poll that observed its notification). -/
def CompletedBefore (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (e : AsyncCopy.Ref) (n : AsyncCopy.Ref × Bool) : Prop :=
  LifetimeOrder L K A X (e, true) n ∨
  ∃ i p w o, e = .async i p ∧ Witness L X e w ∧ o.Enabling ∧
    Relation.TransGen (LifetimeStep L K A X o) (.thread w, true) n

/-- The selected tensor store's completed source reads precede its issuing thread's exit. -/
theorem CompletedBefore.of_storeReadsBeforeExit {L : Launch} {K : Kernel}
    {A : List Assumption} {X : Execution} {i finish : EvId}
    (h : StoreReadsBeforeExit A X (.async i .readsDone) (.thread finish)) :
    CompletedBefore L K A X (.async i .readsDone) (.thread finish, false) :=
  .inl (.inr ⟨.mbar ⟨.shared, 0, 0⟩, trivial,
    .single (.inr (.inr ⟨rfl, rfl, .inr h⟩))⟩)

/-- The completing stage `p` (`AsyncCopy.FinalStage`) of the operation issued by `i` completes
its use of the shared memory of CTA `c` (the table of ERR-SHARED-LIFETIME). -/
def StageUses (X : Execution) (i : EvId) : AsyncCopy.Part → Nat → Prop
  | .notify .copy, c => ∃ s m, X.Copy i s ∧ s.completion = .mbarrier m ∧
      (s.dst.loc.space = .shared ∧ s.dst.loc.cta = c ∨ s.src.loc.space = .shared ∧
        s.src.loc.cta = c ∨ m.cta = c)
  | .write .copy, c => ∃ s, X.Copy i s ∧
      (s.completion = .bulkGroup ∨ s.completion = .asyncGroup) ∧
      (s.dst.loc.space = .shared ∧ s.dst.loc.cta = c ∨
        s.src.loc.space = .shared ∧ s.src.loc.cta = c)
  | .notify (.cta c'), c => c' = c
  | .notify .load, c => ∃ address s, X.TensorIssue i address s ∧ s.mbar.space = .shared ∧
      s.mbar.cta = c
  | .mmaDone, c => (∃ d s accum mask, X.MmaIssue i d s accum mask ∧
      (c = s.lowCta ∨ c = s.highCta)) ∨ ∃ cp, X.CpIssue i cp ∧ c ∈ cp.ctas
  | .tcNotify rank, c => ∃ s m, X.Commit i s ∧ TcCommit.target s rank = some m ∧ m.cta = c
  | _, _ => False

/-- `e` uses the shared memory of CTA `c` (the table of ERR-SHARED-LIFETIME): a thread
instruction or performed stage accessing it or operating on an mbarrier object in it, or,
performed or not, the stage completing an issued operation's use of it. -/
def SharedUse (L : Launch) (X : Execution) (e : AsyncCopy.Ref) (c : Nat) : Prop :=
  (X.RefPresent e ∧
    ((∃ a write, X.Intent e a write ∧ a.loc.space = .shared ∧ a.loc.cta = c) ∨
     ∃ addr action, AsyncCopy.objectAction X X.async ⟨.shared, c, addr⟩ e = some action)) ∨
  (∃ i s, e = .thread i ∧ X.Commit i s ∧ SameCtaGroup L s.group (i.1 / L.block) c) ∨
  (∃ i address s x y k, e = .async i (.write (.load x y k)) ∧ X.TensorIssue i address s ∧
    (TensorTransfer.slotAt s.descriptor x y k).isSome ∧ s.sharedBase.cta = c) ∨
  (∃ i address s, e = .async i .readsDone ∧ X.TensorStoreIssue i address s ∧
    s.sharedBase.cta = c) ∨
  ∃ i p, e = .async i p ∧ AsyncCopy.FinalStage X i p ∧ StageUses X i p c

/-- One owner instruction that completed before the access's issue proves that CTA has
started. This can be established by the startup cluster barrier. -/
def PeerSharedStarted (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (e : AsyncCopy.Ref) (owner : Nat) : Prop :=
  ∃ start ev, start.1 < L.threads ∧ start.1 / L.block = owner ∧ X.get start = some ev ∧
    LifetimeOrder L K A X (.thread start, true) (.thread e.issuer, false)

/-- Every launched thread of CTA `owner` ends its trace with an exit. -/
def CtaExited (L : Launch) (X : Execution) (owner : Nat) : Prop :=
  ∀ g < L.threads, g / L.block = owner → ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩

/-- The use has occurred and completes before an exit of an owner thread, not merely before
the issuer's exit. -/
def SharedFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (e : AsyncCopy.Ref) (owner : Nat) : Prop :=
  X.RefPresent e ∧ ∃ finish pc, finish.1 < L.threads ∧ finish.1 / L.block = owner ∧
    X.get finish = some ⟨pc, .exit⟩ ∧ CompletedBefore L K A X e (.thread finish, false)

/-- The shared-memory lifetime check fails: a use of CTA `owner`'s shared memory issued from
another CTA is not preceded by an instruction of the owner (`PeerSharedStarted`), or the owner
has exited and the use did not complete before an exit of one of its threads
(`SharedFinished`). -/
def SharedLifetimeUnsafe (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) :
    Prop :=
  ∃ e owner, SharedUse L X e owner ∧
    ((owner ≠ e.issuer.1 / L.block ∧ ¬ PeerSharedStarted L K A X e owner) ∨
      (CtaExited L X owner ∧ ¬ SharedFinished L K A X e owner))

end PTX
