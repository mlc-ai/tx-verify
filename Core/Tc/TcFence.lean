-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order

@[expose] public section

namespace PTX
noncomputable section

/-! ## DEP-TC-FENCE — tcgen05 fences composed with execution ordering
Statement: A tcgen05 operation is ordered before another tcgen05 operation when it precedes it in
  base causality order (program order, or synchronization between threads under EXT-TCACQUIRE), or
  when a `tcgen05.fence::before_thread_sync` after the first reaches a
  `tcgen05.fence::after_thread_sync` before the second through base causality or through one
  observed mbarrier arrival, relaxed or release. The completion of an MMA is ordered before a later
  operation when a wait observes the arrive-on of a `tcgen05.commit` that tracks the MMA and reaches
  a `tcgen05.fence::after_thread_sync` before that operation through base causality.

Defs: MbarExec, ExecOrder, TcMma.CommitObserved, TcMma.AfterSync, TcMma.FenceOrder, TcMma.TcBefore

Source:
- §9.7.18.6.3: "The standard memory consistency model synchronization mechanisms also apply to the
    tcgen05 family of instructions."
- §9.7.18.6.3: "The tcgen05.fence::before_thread_sync and tcgen05.fence::after_thread_sync composes
    with execution ordering instructions, like morally strong ld / st / atom instructions, mbarrier
    instruction, barrier instructions and so on, to establish an ordering between the tcgen05
    operations across threads. The asynchronous tcgen05 instructions that are ordered across threads
    in the same warp also form a tcgen05 pipeline. An asynchronous tcgen05 operation prior to a
    tcgen05.fence::before_thread_sync is ordered before all subsequent tcgen05 and the execution
    ordering operations. An asynchronous tcgen05 operation subsequent to a
    tcgen05.fence::after_thread_sync is ordered after all the prior tcgen05 and the execution
    ordering operations."
- §9.7.18.6.4 (canonical patterns, quoted below)
- §9.7.18.11.1: "The tcgen05.fence::* instructions compose with execution ordering instructions
    across a thread scope and provide ordering between tcgen05 instructions across the same scope."
- §9.7.18.12.1: "The scope of the arrive-on operation is the cluster scope."
- §9.7.15.16.19 (a successful wait observes the completed phase)
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

Direction: reading

Applies: tcgen05 operations of any thread ordered through `tcgen05.fence::before_thread_sync`,
  `tcgen05.commit` and `tcgen05.fence::after_thread_sync`

Premises: An execution ordering (`ExecOrder`) from a `fence::before_thread_sync` program-ordered
  after the earlier operation (`FenceOrder`) reaches a `fence::after_thread_sync` program-ordered
  before the later operation (`AfterSync`) by base causality (`baseCausality`: program order,
  `bar.sync`, `bar.warp.sync`, release `barrier.cluster.arrive`, release/acquire mbarrier and memory
  synchronization), or by one mbarrier arrival, relaxed or release, program-ordered after the first
  fence and counted in the phase that a successful wait, relaxed or acquire, observes (`MbarExec`,
  each scope including the other thread), followed by base causality. An MMA's completion is ordered
  by a successful wait observing the arrive-on of a `tcgen05.commit` tracking it (`CommitObserved`;
  the commit's implicit before-fence and arrival) followed by base causality to the
  `fence::after_thread_sync` (`AfterSync`). Each ordering contains at most one observation, at its
  head (§8.9.5 causality order).

Effect: Order relations used by the completion, pipeline, source, conflict and access rules of `Tc/`
  and `Tmem/`. A relaxed mbarrier synchronization enters an ordering through `MbarExec` or
  `CommitObserved`; the fenced route needs no acquire wait. The completion of the earlier operation
  is ordered before a later operation only through the completion mechanisms, which are
  `tcgen05.wait::ld`, `tcgen05.wait::st` and a commit whose arrival a wait observes, as
  DEP-TC-COMPLETION and DEP-TMEM-STORE-VALUE use them.

Review: The litmus tests of all five canonical patterns are in `Tests/Tc/TcFence.lean`. §9.7.18.6.4
  lists five canonical patterns; the model reads them as follows:
  - 4.1, pipelined instructions in one thread: no explicit ordering is needed and the pairs execute
    in program order. This is the same-thread pipeline of DEP-TC-PIPELINE (`Pipelined` with
    program order).
  - 4.2, non-pipelined instructions in one thread: completion is awaited explicitly, by
    `tcgen05.wait::st` before a `tcgen05.ld`, or, for a `tcgen05.mma`, by `tcgen05.commit` and a
    successful relaxed mbarrier wait followed by `tcgen05.fence::after_thread_sync` before the
    `tcgen05.ld`; the commit performs the before-fence implicitly, and the MMA and its commit form
    an asynchronous pipeline that establishes execution ordering.
  - 4.3, pipelined instructions in different threads of one warp: no explicit waiting is needed,
    only synchronization between the threads; the example uses `bar.warp.sync`, a relaxed mbarrier
    wait and `tcgen05.fence::after_thread_sync`.
  - 4.4, non-pipelined instructions in different threads: the producer explicitly waits for
    completion before synchronizing with the consumer. Example 1: `tcgen05.ld`, `tcgen05.wait::ld`,
    `tcgen05.fence::before_thread_sync` and a relaxed mbarrier arrival in the producer; a relaxed
    wait and `tcgen05.fence::after_thread_sync` in the consumer. Example 2: `tcgen05.mma` and
    `tcgen05.commit` arriving on the mbarrier in the producer; a relaxed wait and
    `tcgen05.fence::after_thread_sync` in the consumer. The composed example of 4.4 relays through
    an intermediate thread and is not ordered (EXT-TC-EXEC-ORDER).
  - 4.5, register dependencies in one thread: a true register dependency of `tcgen05.ld` is
    respected whatever other synchronization is present, and implies no other ordering. It orders
    no memory access. The thread's own data flow (THREAD-RUN) represents it, and no order
    relation does.

### EXT-TC-EXEC-ORDER — the execution ordering of tcgen05 fences

Statement: The execution ordering from a `tcgen05.fence::before_thread_sync` to a
  `tcgen05.fence::after_thread_sync` is base causality, or one mbarrier arrival after the first
  fence that a successful wait observes followed by base causality, where a relaxed arrival and wait
  count when each scope includes the other thread. A relay through a third thread, a relaxed wait
  followed by a relaxed arrival, orders nothing.

Why it is not spec text: The text names the execution ordering instructions by example ("like
  morally strong ld / st / atom instructions, mbarrier instruction, barrier instructions and so on")
  and does not define their composition. The model reads it with the shape of §8.9.5 ("Causality
  order combines base causality order with some non-transitive relations as follows: An operation X
  precedes an operation Y in causality order if: X precedes Y in proxy-preserved base causality
  order , or For some operation Z, X precedes Z in observation order, and Z precedes Y in
  proxy-preserved base causality order ."): base causality (`baseCausality`), or one mbarrier
  arrival observed by a successful wait followed by base causality. A relaxed arrival and a relaxed
  wait are morally strong when each scope includes the other thread (§8.7: "each operation is strong
  and specifies a scope that includes the thread executing the other operation"). The observed
  arrival is program-ordered after the `fence::before_thread_sync` (the fence orders the earlier
  operation before "all subsequent tcgen05 and the execution ordering operations"); the observing
  wait reaches the `fence::after_thread_sync` by base causality. An ordering holds at most one
  observation, so a relaxed wait followed in program order by a relaxed arrival is not an order
  (§8.10.4 permits load buffering): a relay through an intermediate thread, including the composed
  example of §9.7.18.6.4.4, orders nothing. Relaxed `barrier.cluster.arrive`, `atom` and relaxed
  `ld`/`st` flag protocols are not part of the ordering, since the model does not distinguish
  relaxed from weak generic accesses (MEM-LOCATION).

Evidence: The quoted sentences of §9.7.18.6.3 and §9.7.18.11.1, the canonical patterns 4.3 and 4.4
  (Examples 1 and 2) of §9.7.18.6.4, each with one relaxed mbarrier synchronization, and the
  causality order of §8.9.5.

Direction: reading

Effect: A single relaxed observation between the two fences orders the tcgen05 operations; if the
  hardware does not honour it, operations the model orders may overlap. Excluding relays through
  intermediate threads is stricter than the composed example of §9.7.18.6.4.4 (fewer ordered
  programs). Disclosed by every kernel whose statement names `Op.tcFenceBefore` or
  `Op.tcFenceAfter`: FlashMlaSparseDecodeH64, TcGemm.
-/

/-- A morally strong mbarrier arrival `x`, relaxed or release, counted in the phase that the
successful wait `w`, relaxed or acquire, observed. -/
def MbarExec (L : Launch) (X : Execution) (x w : EvId) : Prop :=
  ∃ m tx count release rs acquire ws,
    X.Arrive x m tx count release rs ∧ AsyncCopy.WaitObserves X (.thread x) w m acquire ws ∧
    ScopesMeet L rs x.1 ws w.1

namespace TcMma

/-- The successful wait `w`, relaxed or acquire, observes the arrive-on of a commit that tracks
`mma`. The arrive-on has cluster scope; the wait's scope includes the committing thread, which
is the MMA's (`TracksMma`). -/
def CommitObserved (L : Launch) (X : Execution) (mma w : EvId) : Prop :=
  ∃ acquire ws, AsyncCopy.AsyncObserved X mma .mmaDone w acquire ws ∧
    ScopesMeet L .cluster mma.1 ws w.1

/-- Base causality from `s` to a `fence::after_thread_sync` program-ordered before `b`. -/
def AfterSync (L : Launch) (X : Execution) (s b : EvId) : Prop :=
  ∃ f, baseCausality L X s f ∧ X.FenceAfter f ∧ po X f b

end TcMma

/-- EXT-TC-EXEC-ORDER: the execution ordering from `fence::before_thread_sync` `s` to
`fence::after_thread_sync` before `b`: base causality, or one mbarrier arrival
program-ordered after `s` observed by a wait followed by base causality. -/
def ExecOrder (L : Launch) (X : Execution) (s b : EvId) : Prop :=
  TcMma.AfterSync L X s b ∨ ∃ x w, po X s x ∧ MbarExec L X x w ∧ TcMma.AfterSync L X w b

namespace TcMma

/-- `a`, a `fence::before_thread_sync` after it, and an execution ordering to `b`. -/
def FenceOrder (L : Launch) (X : Execution) (a b : EvId) : Prop :=
  ∃ fb, po X a fb ∧ X.FenceBefore fb ∧ ExecOrder L X fb b

/-- tcgen05 operation `a` is ordered before tcgen05 operation `b`: by causality (program
order, or EXT-TCACQUIRE across threads) or by a fenced execution ordering. -/
def TcBefore (L : Launch) (X : Execution) (a b : EvId) : Prop :=
  baseCausality L X a b ∨ FenceOrder L X a b

end TcMma

end
end PTX
