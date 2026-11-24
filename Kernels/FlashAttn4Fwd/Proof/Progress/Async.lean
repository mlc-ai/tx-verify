-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.CollectiveTmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressAsync
public import Lemmas.Flow.NotThreadFence
public import Lemmas.Flow.NotBulk
public import Lemmas.Step.TensorDrainInOrder
public import Lemmas.Step.StoreDoneInOrder
public import Lemmas.Step.MmaDrainTmemA
public import Lemmas.Order.GuardSnoc

@[expose] public section

/-! # The asynchronous obligations of a maximal execution

An open asynchronous obligation of a maximal execution steps. Every extension below performs no
commit arrive-on, so FA4's assumptions keep their constraints (`asms_wfInOrder`,
`Assumption.WfStep.quiet`), and the drain lemmas of the in-order library apply.

* **Bulk copies.** The kernel issues none (`TmemFacts.no_bulk`, `bulk_steps`).
* **Tensor loads.** A load whose global bytes are fixed (`TensorSources`: each has its launch
  content and no write covers it) is completed by a maximal execution
  (`Maximal.tensor_all_notified_inOrder`, `tensor_steps`).
* **Tensor stores.** A store whose staging bytes have visible source writes (`StoreSources`) is
  completed once synchronization is guarded (`Step.StoreDone.pending_issue_visible_inOrder`,
  `store_steps`). Synchronization is guarded in a safe execution whose polls spin and whose writes
  do not release (`syncGuarded`): a fault of an mbarrier record is unsafe.
* **MMAs.** An MMA whose shared operand bytes have ordered source writes (`OperandSourcesT`),
  that reads no Tensor Memory A cell its accumulator's MMAs write (`TcMma.ATmemApart`), and whose
  output layout is injective (`TcMma.LayoutInjective`) is completed by a maximal execution once
  synchronization is guarded (`Maximal.mma_all_done_tmemA`, `mma_steps`).
* **The paired Tensor Memory requests.** An uncovered operation has a ready step, recorded by a
  counted extension, or a pending lane of warp 12, which ranks below the obligation
  (`tmem_obl_dichotomy`, `tmem_steps`).

The sources of the loads, stores and MMAs are protocol facts (`AsyncSources`), supplied at the top
of the proof tree. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Proof

noncomputable section

/-- Every tensor store is valid, reads no old destination bytes, and each byte it reads has a
visible source write whose byte is defined. -/
def StoreSources (L : Launch) (X : Execution) : Prop :=
  ∀ i a s, X.TensorStoreIssue i a s → TensorStore.Valid (i.1 / L.block) s ∧ s.reduce = none ∧
    Step.StoreDone.VisibleReadSources L X i s

/-- **The sources of the asynchronous operations**, for every maximal execution: the protocols'
facts that fix the inputs of the tensor loads and stores. -/
structure AsyncSources (L : Launch) (mem0 : Mem0) : Prop where
  /-- The tensor loads' global bytes are fixed. -/
  tensor : ∀ X, Maximal L kernel asms mem0 X → TensorSources L mem0 X
  /-- The tensor stores' staging bytes have visible sources. -/
  store : ∀ X, Maximal L kernel asms mem0 X → StoreSources L X
  /-- The MMAs' shared operand bytes have ordered sources, no MMA reads a Tensor Memory A cell
  its accumulator's MMAs write, and the output layouts are injective. -/
  mma : ∀ X, Maximal L kernel asms mem0 X →
    OperandSourcesT L X ∧ TcMma.ATmemApart X ∧ TcMma.LayoutInjective X

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- FA4's code has no thread fence (`fence.sc`, `fence.acq_rel`). -/
theorem kernel_noThreadFence : kernel.code.all (fun ins => !Flow.threadFenceOp ins.op) = true := by
  decide +kernel

/-- **FA4 makes no thread fence.** -/
theorem no_threadFence (hX : Consistent L kernel asms mem0 X) (e : EvId) (sem : FenceSem)
    (s : MbarScope) : ¬ X.ThreadFence e sem s := fun ⟨_, he⟩ =>
  Flow.no_kind_of_code hX Flow.threadFenceOp (fun k => ∃ sem s, k = .fence sem s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => Flow.fires_threadFence_op hf hk)
    kernel_noThreadFence he ⟨_, _, rfl⟩

/-- **Synchronization is guarded** when the successful polls spin, the writes and atomics do not
release and no mbarrier record faults: FA4 makes no thread fence. -/
theorem syncGuarded_of (hX : Consistent L kernel asms mem0 X) (hr : RingFacts L X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false) (htm : TmemFacts L X)
    (hnf : ∀ m r, r ∈ X.objects m → r.fault = none) : SyncGuarded L kernel X where
  spin _ _ _ _ _ _ he := hr.spins (Frame.lt_of_get hX he) he
  noMemSync e f := ⟨noSynchronizesWith_of hnr (fun _ _ _ _ _ he => (htm.no_rmw he).elim) e f,
    not_fenceSync_of_noFence (no_threadFence hX) e f⟩
  noFault m _ _ r _ hr' _ _ _ := hnf m r (List.mem_of_getElem? hr')

/-- **Synchronization is guarded** in a safe execution: a faulting mbarrier record is unsafe. -/
theorem syncGuarded (hX : Consistent L kernel asms mem0 X) (hs : ¬ Unsafe L kernel asms mem0 X)
    (hr : RingFacts L X) (hp : ProgressAsyncFacts L X) (htm : TmemFacts L X) :
    SyncGuarded L kernel X :=
  syncGuarded_of hX hr (fun _ _ _ _ he => hp.no_release he) htm fun m r hrm => by
    cases hf : r.fault with
    | none => rfl
    | some f =>
      refine absurd ?_ hs
      exact .inr (.inr (.inr (.inr (.inr (.inl (.inl ⟨m, r, hrm, by simp [hf]⟩))))))

/-- The kernel issues no bulk copy, so no bulk obligation is open. -/
theorem bulk_steps (htm : TmemFacts L X) (ho : Descent.Obl L X .bulk) :
    Sched.Steps (timed L) mem0 X .bulk :=
  (ho fun _ _ ⟨_, he⟩ => (htm.no_bulk he).elim).elim

/-- The kernel issues no `cp.async.mbarrier.arrive`, so no arrive-on obligation is open. -/
theorem arriveOn_steps (htm : TmemFacts L X) (ho : Descent.Obl L X .arriveOn) :
    Sched.Steps (timed L) mem0 X .arriveOn :=
  (ho fun _ _ _ ⟨_, he⟩ => (htm.no_arriveOn he).elim).elim

/-- **A maximal execution whose tensor loads' sources are fixed has completed every load.** -/
theorem tensor_steps (hmax : Maximal L kernel asms mem0 X) (hts : TensorSources L mem0 X)
    (ho : Descent.Obl L X .tensor) :
    Sched.Steps (timed L) mem0 X .tensor :=
  (ho fun _ _ _ hi => Maximal.tensor_all_notified_inOrder asms_wfStep hmax hts hi).elim

/-- **An open store obligation steps**: an issued tensor store not fully done, whose bytes have
visible sources, extends the execution by a counted step. -/
theorem store_steps (hmax : Maximal L kernel asms mem0 X) (hsg : SyncGuarded L kernel X)
    (hss : StoreSources L X) (ho : Descent.Obl L X .store) :
    Sched.Steps (timed L) mem0 X .store := by
  obtain ⟨i, a, s, hi, hn⟩ : ∃ i a s, X.TensorStoreIssue i a s ∧
      ¬ ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true := by
    by_contra hc
    push Not at hc
    exact ho fun i a s hi => hc i a s hi
  obtain ⟨hv, hred, hsrc⟩ := hss i a s hi
  exact .inl (Step.StoreDone.pending_issue_visible_inOrder asms_wfStep hmax.1 ⟨a, hi⟩ hv hn
    hsrc hsg hred)

/-- **A maximal execution whose MMAs' operands have sources has completed every MMA**; FA4
issues no `tcgen05.cp` or `tcgen05.shift`. -/
theorem mma_steps (hmax : Maximal L kernel asms mem0 X) (hsg : SyncGuarded L kernel X)
    (hos : OperandSourcesT L X) (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    (hsc : ScoreFacts L X) (ho : Descent.Obl L X .mma) :
    Sched.Steps (timed L) mem0 X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_tmemA asms_wfStep hmax hsg hos hap hinj hm
  · exact (hsc.no_cp i c hc).elim
  · exact (hsc.no_shift i s hs).elim

/-- **An open obligation of the paired Tensor Memory requests steps**: a ready step is recorded
by a counted extension; otherwise a pending lane of warp 12 ranks below the obligation. -/
theorem tmem_steps (hpre : Pre P L mem0) (hs : ¬ Unsafe L kernel asms mem0 X)
    (htm : TmemFacts L X) (hmax : Maximal L kernel asms mem0 X) (ho : Descent.Obl L X .tmem) :
    Sched.Steps (timed L) mem0 X .tmem := by
  rcases tmem_obl_dichotomy hpre htm hmax.1 (safe_noAligned hs) ho with hR | ⟨h, hp, -⟩
  · exact tmem_ready_steps hmax hR
  · exact .inr ⟨X, .thread h, hmax, hp, Sched.rank_thread_lt_tmem hp.1⟩

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
