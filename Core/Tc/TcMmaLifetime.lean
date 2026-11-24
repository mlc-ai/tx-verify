-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairLifetime
public import Core.Tc.TcFence

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TC-COMPLETION — completion of Tensor Memory accesses
Statement: An MMA or copy has completed before a later event when a wait observes the arrive-on of a
  `tcgen05.commit` tracking it and reaches the event through causality to a
  `tcgen05.fence::after_thread_sync` before it, or, for an acquire wait, through causality alone; a
  load or store has completed before it when a later `tcgen05.wait::ld` or `tcgen05.wait::st` of its
  own thread is ordered before it.

Defs: TcMma.DoneBefore, TcMma.WaitBefore, TcMma.CompletedBefore

Source:
- §9.7.18.6.4 (completion handoff: "the producer threads that issue the asynchronous tcgen05
    instructions must explicitly wait for the instructions’ completion before synchronizing with the
    consumer threads"
- §9.7.18.8.5 (wait::ld)
- §9.7.18.12.1 (commit)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

Direction: reading

Applies: Every MMA, copy, Tensor Memory load and store, of either CTA group

Premises: An MMA completes through a `tcgen05.commit` whose arrive-on a successful wait observes; a
  load (store) completes through a later `tcgen05.wait::ld` (`tcgen05.wait::st`) of its thread;
  `CompletedBefore` selects the mechanism by the access kind. The completion is ordered before
  another tcgen05 operation either by a fenced chain (DEP-TC-FENCE: for an MMA the observing wait
  starts the chain, the commit performing the before-fence; for a load or store a
  `fence::before_thread_sync` after the wait starts it) or, under EXT-TCACQUIRE, by causality from
  an acquire wait observing the commit, or from the `wait::ld`. Allocation coverage of an access is
  OBJ-TMEM-LIFETIME (`Tmem.Pair.Covers`).

Effect: Relations used by the source, conflict, lifetime and access rules. The direction is
  `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the fenced chains
  of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.

### EXT-TCACQUIRE — acquire synchronization orders tcgen05 operations

Statement: An acquire wait or `bar.sync` orders a thread's later asynchronous tcgen05 operations
  after the synchronization, and a release orders the thread's earlier completed tcgen05 operations
  before it, without a `tcgen05.fence`. On this route the completion of an MMA is observed by an
  acquire wait on the commit's mbarrier whose scope and the cluster scope of the arrive-on each
  include the other thread.

Why it is not spec text: The canonical patterns of §9.7.18.6.4 synchronize with `.relaxed` mbarrier
  operations and the tcgen05 fences (DEP-TC-FENCE). §9.7.18.6.3 adds: "The standard memory
  consistency model synchronization mechanisms also apply to the tcgen05 family of instructions."
  The model reads this as a second, separate route: an acquire (a successful acquire `try_wait`, or
  `bar.sync`) orders the thread's later asynchronous tcgen05 operations after the synchronization,
  and a release (an arrival, or `bar.sync`) orders the thread's earlier, completed tcgen05
  operations before it; this route needs no tcgen05 fence. It is the `baseCausality` disjunct of
  `TcMma.TcBefore` and the acquire disjunct of `DoneBefore`, whose observation requires an acquire
  wait (`AsyncCopy.AsyncObserved` with the acquire flag) whose scope meets the cluster scope of the
  commit's arrive-on (`ScopesMeet`, §8.7), as synchronization of the standard memory consistency
  model requires. A `.cta` wait in a peer CTA observes the completion but orders nothing. Completion
  is a separate requirement on both routes: an MMA completes through a `tcgen05.commit` and a
  successful wait on its mbarrier phase, a load through a later `tcgen05.wait::ld` of its thread. A
  relaxed wait reaches a later tcgen05 operation only through a `fence::after_thread_sync`
  (DEP-TC-FENCE). The shared-memory operand reads of an MMA are async-proxy accesses
  (MEM-MODEL-CAUSALITY); their completion is observed only through an acquire wait
  (`AsyncFinished`). The text that points the other way is §9.7.18.5 Table 55, row `.fence::*`: "A
  thread needs to fence all its accesses to the tensor memory that it wants to order with other
  accesses to the tensor memory from other threads. The following example shows that: Before
  attempting to deallocate Tensor Memory, it suffices to ensure that there are no concurrent Tensor
  Memory accesses from the Peer CTA ." Read literally, ordering a thread's tensor memory accesses
  with another thread's accesses needs `tcgen05.fence` (the route of DEP-TC-FENCE). The model reads
  acquire and release synchronization as replacing that fence: an acquire wait or `bar.sync` that
  causally follows the completion of the accesses orders them without a `tcgen05.fence`. This is a
  hardware and CUTLASS-practice assumption. It is not an inference from the text: the row quoted
  above says nothing of the standard synchronization mechanisms, and §9.7.18.6.3 says that they
  "also apply".

Direction: reading

Effect: It accepts fence-free orderings that the Table 55 sentence, read literally, does not give; a
  program that is ordered only by this route is wrongly accepted if hardware needs the fence.
  Disclosed by every kernel whose statement names `Op.tcMma`, `Op.tcLd`, `Op.tcSt`, `Op.tcCp` or
  `Op.tcDealloc`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

Evidence: The sentence of §9.7.18.6.3, and CUTLASS (commit b2f249ac), which reads MMA results after
  an acquire `mbarrier.try_wait` without a fence (`include/cutlass/pipeline/sm100_pipeline.hpp`,
  `include/cutlass/epilogue/collective/sm100_epilogue_tma_warpspecialized.hpp`) and frees Tensor
  Memory after `tcgen05.wait::ld` and mbarrier arrive/wait without tcgen05 fences
  (`include/cutlass/gemm/kernel/sm100_gemm_tma_warpspecialized.hpp`). The ISA gives no example of
  the fence-free form.

Review: The peer `.cta` wait is `PeerScope.cta_not_done` in `Tests/Tc/TcRegression.lean`.
-/

/-- MMA `issue` has completed, and that completion is observed before `e`: by an acquire wait
followed by causality (EXT-TCACQUIRE), or by a wait starting a fenced chain to `e`. -/
def DoneBefore (L : Launch) (X : Execution) (issue e : EvId) : Prop :=
  (∃ wait ws, AsyncCopy.AsyncObserved X issue .mmaDone wait true ws ∧
      ScopesMeet L .cluster issue.1 ws wait.1 ∧ baseCausality L X wait e) ∨
    ∃ wait, CommitObserved L X issue wait ∧ AfterSync L X wait e

/-- Operation `op` has finished, by a later `wait` (`tcgen05.wait::ld` or `tcgen05.wait::st`)
of its thread, before `e`. -/
def WaitBefore (L : Launch) (X : Execution) (wait : TcKind) (op e : EvId) : Prop :=
  ∃ w, (∃ pc, X.get w = some ⟨pc, .tc wait⟩) ∧ w.1 = op.1 ∧ op.2 < w.2 ∧ TcBefore L X w e

/-- Tensor Memory access `e` has completed before `d` by the completion mechanism of its kind:
a load by `wait::ld`, a store by `wait::st`, an MMA or copy by an observed commit. -/
def CompletedBefore (L : Launch) (X : Execution) (e d : EvId) : Prop :=
  ((∃ a vals shape, X.TLd e a vals shape) → WaitBefore L X .waitLd e d) ∧
  ((∃ a vals shape, X.TSt e a vals shape) → WaitBefore L X .waitSt e d) ∧
  (X.TcAsync e → DoneBefore L X e d)

end
end PTX.TcMma
