-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Memory.Order
public import Core.Assembly.Dependency

@[expose] public section

namespace PTX

noncomputable section

/-! ## ERR-NONUNIFORM-GUARD — warp-uniform control flow

Statement: When two threads of one warp (of one warpgroup for `setmaxnreg`) execute the same guarded
  instruction that requires a uniform guard, namely `bra.uni`, `brx.idx.uni`, `shfl.sync`,
  `vote.sync`, `redux.sync`, `match.sync` or an `.aligned` instruction (`Op.uniform`), and neither
  execution is ordered before the other, the two threads must evaluate the guard identically. Two
  such executions of a `brx.idx.uni` must also read the same index. Otherwise the execution is
  unsafe. A kernel assumption can exempt a `bra.uni` that tests the result of an `mbarrier.try_wait`
  poll.

Defs: Visit, uniIndex, visit, Walk, Visit.events, Visit.Disagree, Visit.disagree_noIndex,
  DepBeforeNode, DepBefore, VisitBefore, PollAgreeExempt, not_pollAgreeExempt,
  Kernel.uniformScopeAt, SameUniformGroup, WarpDivergent, warpDivergent_noPoll, UniformScope,
  Op.uniformScope, Op.uniform

Source:
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

Direction: stricter

Applies: Guarded `bra.uni`, `shfl.sync`, `vote.sync`, `redux.sync`, `match.sync` and `.aligned`
  instructions, and every `brx.idx.uni`

Premises: Two distinct threads of the instruction's uniform scope (`SameUniformGroup`:
  one warp; one warpgroup for `setmaxnreg`, `Op.uniformScope`) execute such an instruction (the same
  position), and neither execution is ordered before the other by the execution-dependency order
  (`VisitBefore`, `DepBefore`, EXT-DEPENDENCY-ORDER): the two executions may coincide.

Effect: Safety rejection (part of Unsafe). The instructions that require a uniform guard are those
  that `Op.uniform` selects, with the `.aligned` and `.uni` qualifiers as decoded, and the threads
  whose guards must agree are those of `Op.uniformScope`, as each instruction's text states: the
  warpgroup for `setmaxnreg`, the warp for `bra.uni`, `brx.idx.uni`, `barrier.cluster` and the
  `tcgen05` forms, and for an aligned `barrier{.cta}` the warp here and the barrier's participants
  in ERR-BARRIER-MISMATCH (EXT-BAR-PARTICIPANTS). Every decoded `tcgen05` resource, load/store and
  wait form and `setmaxnreg` carries `.sync.aligned` in its syntax, and so does every warp-level
  matrix instruction (`Op.matrix`). `bar.warp.sync`, `elect.sync`, `shfl.sync` and the asynchronous
  `tcgen05` operations are not aligned. `bar.arrive` is `barrier.arrive.aligned` and is aligned like
  `bar.sync`. A guarded `shfl.sync` also requires a warp-uniform guard: a lane whose guard is false
  takes part in the instance without a source value (§9.7.10.6), which DEP-WARP-SHUFFLE does not
  represent, so lanes that may execute it together with different guards are unsafe. This is
  stricter than the text, which leaves only the value read from such a lane unpredictable. A guarded
  `vote.sync` requires a warp-uniform guard for the same reason: the text does not say whether a
  lane of the member mask whose guard is false contributes to or waits for the instance
  (DEP-WARP-VOTE does not represent such a lane), so lanes that may execute it together with
  different guards are unsafe (stricter). A guarded `redux.sync` or `match.sync` requires a
  warp-uniform guard for the same reason (DEP-WARP-INSTANCE does not represent a lane of the member
  mask whose guard is false). `activemask` waits for no other lane and has no uniformity
  requirement. The exemption applies at a position that a kernel
  assumption selects with `uniPoll` (ASM-INTERFACE) when its instruction is a `bra.uni` guarded by
  the predicate that the `mbarrier.try_wait` right before it writes, and when the records of both
  lanes right before it are polls of one mbarrier, whatever their parities (`PollAgreeExempt`). The
  kernel's assumption ASM-POLL-AGREE then carries the guarantee. With no site selected, the rule is
  the one without this exemption (`warpDivergent_noPoll`). `Walk` follows one thread through every
  step it takes, local or not, on a prefix of its trace, and records each step (`Visit`): the
  instruction's source position, the guard's value when the instruction is guarded and requires a
  uniform guard, the event the step performs, and for a `brx.idx.uni` the index it reads
  (`uniIndex`). Two records of one position disagree (`Visit.Disagree`) when both have a guard value
  and the values differ, or both have an index and the indices differ. The index is recorded whether
  or not the guard holds, which is stricter than the text when both guards are false; a record whose
  index cannot be read (an index register that was never written) has none, and that read is a fault
  of its own when the branch is taken (THREAD-REG). Where no `brx.idx.uni` is executed, no record
  has an index and the rule compares guards only (`Visit.disagree_noIndex`). Which lanes are
  "currently executing this instruction" together is not fixed by the program: re-convergence points
  are chosen by the code generator (§9.5), and with Independent Thread Scheduling a schedule
  optimizer groups the active threads of a warp at sub-warp granularity (§3.2). A program must
  therefore be safe for every grouping. Two executions of one position by two lanes of a warp may
  coincide unless the execution-dependency order orders them (EXT-DEPENDENCY-ORDER): an event the
  first lane performs at or after its execution precedes, in `DepBefore`, an event the second lane
  performs before its execution (`VisitBefore`), in either direction. `DepBefore` is the dependency
  order of DEP-ORDER (`DepStep`: witnesses before returns, returns before the events that
  depend on them, the stage order) together with program order between issue nodes
  (`DepBeforeNode`). The rule compares every pair that it does not order; any grouping
  the scheduler may form consists of pairs of this kind. Both lanes execute the same position, so a
  `bra.uni` has the same target in both: the guard is the only value to compare. A `brx.idx.uni`
  takes its target from the index, so the index is compared as well. A lane that skips an aligned
  collective altogether is checked by ERR-ALIGNED-MISMATCH or leaves the collective pending. An
  unguarded `bra.uni` or aligned instruction has no guard to disagree on; the `.uni` qualifier does
  not change what a thread does (THREAD-BRANCH).

Review: It is stricter: it flags pairs that no real schedule groups together. The known cases are:
  * a loop on a warp-uniform counter, `setp p, i == 0; @p bra.uni ...` in each of two rounds, with
    no blocking instruction and no synchronization between the rounds: lane 0's first execution
    (guard true) and lane 1's second (guard false) are not ordered and are compared, although lanes
    that never diverged may execute their rounds in step. A warp collective between the rounds
    (`elect.sync`, `shfl.sync`, `bar.warp.sync`) orders them through its rendezvous and removes the
    pair (EXT-DEPENDENCY-ORDER), and so does a blocking barrier;
  * a loop whose first round only lane 0 reaches a `bra.uni` (guard true) and whose second round
    both lanes reach it (guard false), with nothing ordering the rounds: lane 0's first execution
    and lane 1's second may coincide, because lane 0 can be descheduled at the branch while lane 1
    runs on to its second round; a synchronization between the rounds (for example `bar.sync`)
    orders them and removes the pair;
  * `try_wait p, [M]; mov ...; @p bra.uni DONE; @lane0 arrive [M]` where lane 0's poll fails and
    lane 1's succeeds after lane 0's arrival: lane 1's branch follows lane 0's on hardware, but
    the poll is not a canonical spin, so its witness orders no later event of lane 1, and the
    pair is compared (the poll is also rejected by ERR-POLL-SHAPE).

### EXT-DEPENDENCY-ORDER — executions ordered by blocking collectives are not executed together

Statement: Two executions of one position by two threads are not executed together when an event the
  first thread performs at or after its execution precedes, in the execution-dependency order, an
  event the second thread performs before its execution. The execution-dependency order is the
  dependency order of DEP-ORDER (from each witness of a return to the return, and from a
  return to the later events of its thread that depend on it) together with program order between
  issue nodes; base causality (`baseCausality`) is not part of it. In the model: `DepBeforeNode`,
  `DepBefore`, `VisitBefore`.

Source:
- §9.7.14.3: "bra.uni is guaranteed to be non-divergent, i.e. all active threads in a warp that are
    currently executing this instruction have identical values for the guard predicate and branch
    target"
- §9.7.15.15: "The mandatory .sync qualifier indicates that elect causes the executing thread to
    wait until all threads in the membermask execute the elect instruction before resuming
    execution."
- §9.7.10.6: "shfl.sync will cause executing thread to wait until all non-exited threads
    corresponding to membermask have executed shfl.sync with the same qualifiers and same membermask
    value before resuming execution."
- §9.7.15.10
- §9.7.15.11 and §9.7.15.13 (`vote.sync`, `match.sync`, `redux.sync`, as quoted in
    DEP-WARP-INSTANCE)
- §9.7.15.2: "bar.warp.sync will cause executing thread to wait until all threads corresponding to
    membermask have executed a bar.warp.sync with the same membermask value before resuming
    execution."
- §9.7.15.1: "the barrier{.cta}.red and barrier{.cta}.sync instructions causes executing thread to
    wait for non-exited threads of all other warps participating in the barrier to arrive."
- §9.7.15.3: "barrier.cluster.wait instruction causes the executing thread to wait for all
    non-exited threads of the cluster to perform barrier.cluster.arrive"
- §9.7.15.3: "In addition, barrier.cluster instructions cause the executing thread to wait for all
    non-exited threads from its warp."
- §9.7.18.7.1 and §9.7.18.8: "The mandatory .sync qualifier indicates that the instruction causes
    the executing thread to wait until all threads in the warp execute the same instruction before
    resuming execution."
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- §3.2: "A schedule optimizer determines how to group active threads from the same warp together
    into SIMT units"

Why it is not spec text: The blocking sentences order each participant's return after the arrivals
  it waits for, so an execution after a lane's return follows, in time, an execution before another
  lane's arrival. The text defines this waiting; it does not define which executions the hardware
  groups into one SIMT unit (§3.2). That executions ordered by the dependency order are not
  "currently executing this instruction" together (§9.7.14.3) is the reading. The dependency order
  orders no memory access: `DepBefore` enters neither `baseCausality`, `stageCausality` nor any
  memory rule.

Direction: reading

Effect: It is used only in `VisitBefore` (ERR-NONUNIFORM-GUARD). Executions it does not order are
  still compared. A successful poll orders the later events of its thread only when it is a
  canonical spin (`SpinExit`, DEP-CANONICAL-SPIN). Disclosed by every kernel whose statement names
  `Op.bra (uni := true)`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.
-/

/-- The threads that must evaluate a uniform instruction's guard identically. -/
inductive UniformScope where
  | warp | warpgroup
  deriving DecidableEq, Repr

/-- The scope of an instruction's uniform guard: the warpgroup for `setmaxnreg` (§9.7.21.5),
the warp for every other uniform instruction. -/
def Op.uniformScope : Op → UniformScope
  | .setMaxReg .. => .warpgroup
  | _ => .warp

/-- The instruction requires a warp-uniform guard: `bra.uni`, `brx.idx.uni`, `shfl.sync`,
`vote.sync`, `redux.sync`, `match.sync` or an `.aligned` instruction. -/
def Op.uniform : Op → Bool
  | .bra _ uni | .brx _ _ uni => uni
  | .warp w => match w.kind with
    | .shfl _ | .vote .. | .redux .. | .match_ _ => true
    | _ => false
  | op => op.aligned

/-- The record of one step of a thread. -/
structure Visit where
  /-- The position of the instruction the step executes. -/
  pc : Nat
  /-- The guard's value, for a guarded instruction that requires a uniform guard. -/
  guard : Option Bool
  /-- The event the step performs (`none` for a local step). -/
  ev : Option Event
  /-- The index a `brx.idx.uni` reads, when it can be read. -/
  index : Option Nat := none

/-- The index that a `brx.idx.uni` reads in state `t`, as a 32-bit unsigned integer; none for
every other instruction and for an index that cannot be read. -/
def uniIndex (L : Launch) (g : Nat) (t : TState) : Op → Option Nat
  | .brx index _ true => (readBits L g t 32 index).toOption.map BitVec.toNat
  | _ => none

/-- The record of the step from `t` that performs `ev`. -/
def visit (K : Kernel) (L : Launch) (g : Nat) (t : TState) (ev : Option Event) : Visit :=
  ⟨t.pc, match K.code[t.pc]? with
    | some ins =>
      if ins.op.uniform && ins.guard.isSome then (guardHolds t ins.guard).toOption else none
    | none => none, ev, match K.code[t.pc]? with
    | some ins => uniIndex L g t ins.op
    | none => none⟩

/-- Two records disagree: both have a guard value and the values differ, or both have the index
of a `brx.idx.uni` and the indices differ. -/
def Visit.Disagree (vi vj : Visit) : Prop :=
  (∃ b b', vi.guard = some b ∧ vj.guard = some b' ∧ b ≠ b') ∨
  (∃ x y, vi.index = some x ∧ vj.index = some y ∧ x ≠ y)

/-- Records without an index disagree exactly when their guard values differ. -/
theorem Visit.disagree_noIndex {vi vj : Visit} (h : vi.index = none) :
    vi.Disagree vj ↔ ∃ b b', vi.guard = some b ∧ vj.guard = some b' ∧ b ≠ b' := by
  simp [Visit.Disagree, h]

section
variable (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat)

/-- From `t`, the thread performs exactly the events `es` in the steps recorded in `vs`; it
may stop at any state. -/
inductive Walk : TState → List Event → List Visit → Prop
  | stop (t : TState) : Walk t [] []
  | tau {t t' : TState} {es : List Event} {vs : List Visit} :
      Tau K A L g t t' → Walk t' es vs → Walk t es (visit K L g t none :: vs)
  | ev {t t' : TState} {e : Event} {es : List Event} {vs : List Visit} :
      EStep K A L g t e (some t') → Walk t' es vs →
        Walk t (e :: es) (visit K L g t (some e) :: vs)
  | last {t : TState} {e : Event} :
      EStep K A L g t e none → Walk t [e] [visit K L g t (some e)]

end

/-- The number of events of the records before the `i`-th of `vs`: the trace index of the
first event the thread performs at or after that record. -/
def Visit.events (vs : List Visit) (i : Nat) : Nat := ((vs.take i).filterMap Visit.ev).length

/-- The execution-dependency order of EXT-DEPENDENCY-ORDER on nodes: the dependency order of
DEP-ORDER (`DepStep`) together with program order between issue nodes. Program order
continues only from issue nodes, so a path that reached a return through a witness continues only
through `Resumes`. Base causality (`baseCausality`) is not part of it. -/
def DepBeforeNode (L : Launch) (K : Kernel) (X : Execution) :
    AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop :=
  Relation.TransGen fun a c => DepStep L K X a c ∨
    (a.2 = false ∧ c.2 = false ∧ ∃ i j, a.1 = .thread i ∧ c.1 = .thread j ∧ TraceBefore X i j)

/-- Thread event `e` precedes thread event `f` in the execution-dependency order: from the issue
of `e` to the issue of `f` (EXT-DEPENDENCY-ORDER), used only by this rule. -/
def DepBefore (L : Launch) (K : Kernel) (X : Execution) (e f : EvId) : Prop :=
  DepBeforeNode L K X (.thread e, false) (.thread f, false)

/-- The `i`-th record of thread `g`'s walk `vg` is ordered before the `j`-th record of thread
`h`'s walk `vh`: an event `g` performs at or after it precedes, in the execution-dependency
order, an event `h` performs before the other. -/
def VisitBefore (L : Launch) (K : Kernel) (X : Execution) (g : Nat) (vg : List Visit) (i : Nat)
    (h : Nat) (vh : List Visit) (j : Nat) : Prop :=
  ∃ a b, Visit.events vg i ≤ a ∧ b < Visit.events vh j ∧ DepBefore L K X (g, a) (h, b)

/-- A kernel assumption exempts the `i`-th record of `vg` and the `j`-th record of `vh`, at
position `pc` (ASM-POLL-AGREE): it selects `pc` with `uniPoll`, the instruction there is a
`bra.uni` guarded by the predicate that the `mbarrier.try_wait` at `pc - 1` writes, and the record
right before each is that poll's event, on one mbarrier with any parities. -/
def PollAgreeExempt (K : Kernel) (A : List Assumption) (pc : Nat) (vg vh : List Visit)
    (i j : Nat) : Prop :=
  A.any (·.uniPoll pc) = true ∧
  (∃ dst neg tgt prev base off par acq sc,
    K.code[pc]? = some ⟨some (dst, neg), .bra tgt true⟩ ∧ K.code[pc - 1]? = some prev ∧
    prev.op = .mbarWait dst base off par acq sc) ∧
  ∃ vg' vh' m p p' ok ok' acq acq' sc sc', vg[i - 1]? = some vg' ∧ vh[j - 1]? = some vh' ∧
    0 < i ∧ 0 < j ∧ vg'.ev = some ⟨pc - 1, .wait m p ok acq sc⟩ ∧
    vh'.ev = some ⟨pc - 1, .wait m p' ok' acq' sc'⟩

/-- With no site selected by `uniPoll`, no pair is exempt. -/
theorem not_pollAgreeExempt {K : Kernel} {A : List Assumption}
    (hA : ∀ a ∈ A, ∀ pc, a.uniPoll pc = false) {pc : Nat} {vg vh : List Visit} {i j : Nat} :
    ¬ PollAgreeExempt K A pc vg vh i j := by
  rintro ⟨hs, -⟩
  obtain ⟨a, ha, hd⟩ := List.any_eq_true.mp hs
  rw [hA a ha pc] at hd
  cases hd

/-- The scope of the uniform guard of the instruction at `pc`. -/
def Kernel.uniformScopeAt (K : Kernel) (pc : Nat) : UniformScope :=
  match K.code[pc]? with
  | some ins => ins.op.uniformScope
  | none => .warp

/-- Threads `g` and `h` belong to one group of scope `s`. -/
def SameUniformGroup (L : Launch) : UniformScope → Nat → Nat → Prop
  | .warp, g, h => SameWarp L g h
  | .warpgroup, g, h => SameWarpgroup L g h

/-- Two threads of one warp, or of one warpgroup for `setmaxnreg`, execute a guarded instruction
that requires a uniform guard, or a `brx.idx.uni`, in two executions that the
execution-dependency order does not order (they may coincide), and evaluate the guard differently
or read different indices (`Visit.Disagree`), outside the pairs a kernel assumption exempts
(`PollAgreeExempt`). -/
def WarpDivergent (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∃ g h, g < L.threads ∧ h < L.threads ∧ g ≠ h ∧
    ∃ eg eh vg vh, eg <+: X.tr g ∧ eh <+: X.tr h ∧ Walk K A L g {} eg vg ∧ Walk K A L h {} eh vh ∧
      ∃ i j pc vi vj, vg[i]? = some vi ∧ vh[j]? = some vj ∧ vi.pc = pc ∧ vj.pc = pc ∧
        SameUniformGroup L (K.uniformScopeAt pc) g h ∧ vi.Disagree vj ∧
        ¬ VisitBefore L K X g vg i h vh j ∧ ¬ VisitBefore L K X h vh j g vg i ∧
        ¬ PollAgreeExempt K A pc vg vh i j

/-- With no site selected by `uniPoll`, the rule is the one without the exemption. -/
theorem warpDivergent_noPoll {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution} (hA : ∀ a ∈ A, ∀ pc, a.uniPoll pc = false) :
    WarpDivergent L K A X ↔
      ∃ g h, g < L.threads ∧ h < L.threads ∧ g ≠ h ∧
        ∃ eg eh vg vh, eg <+: X.tr g ∧ eh <+: X.tr h ∧ Walk K A L g {} eg vg ∧
          Walk K A L h {} eh vh ∧
          ∃ i j pc vi vj, vg[i]? = some vi ∧ vh[j]? = some vj ∧ vi.pc = pc ∧ vj.pc = pc ∧
            SameUniformGroup L (K.uniformScopeAt pc) g h ∧ vi.Disagree vj ∧
            ¬ VisitBefore L K X g vg i h vh j ∧ ¬ VisitBefore L K X h vh j g vg i := by
  unfold WarpDivergent
  simp only [not_pollAgreeExempt hA, not_false_eq_true, and_true]

end

end PTX
