-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WarpColl
public import Lemmas.Step.DrainInOrder
public import Lemmas.Step.MmaDrainTmemA
public import Lemmas.Step.TensorDrainInOrder

@[expose] public section

/-!
# The asynchronous obligations of a maximal execution

An open asynchronous obligation of a maximal execution steps. Every extension below performs no
commit arrive-on, so the kernel's assumptions keep their constraints (`asms_wfStep`), and the
drain lemmas of the in-order library apply.

* **Bulk copies, `cp.async.mbarrier.arrive`, tensor stores, cancellation requests.** The kernel
  issues none, so none is open (`bulk_steps`, `arriveOn_steps`, `store_steps`, `clc_steps`).
* **Tensor loads.** A load whose global bytes are fixed (`TensorSources`: each has its launch
  content and no write covers it) is completed by a maximal execution
  (`Maximal.tensor_all_notified_inOrder`, `tensor_steps`).
* **MMAs.** An MMA whose shared operand bytes have ordered source writes (`OperandSourcesT`), that
  reads no Tensor Memory A cell its accumulator's MMAs write (`TcMma.ATmemApart`), and whose output
  layout is injective (`TcMma.LayoutInjective`) is completed by a maximal execution once
  synchronization is guarded (`Maximal.mma_all_done_tmemA`, `mma_steps`). The kernel issues no
  `tcgen05.cp` and no `tcgen05.shift`.
* **Commits.** A commit's delivery steps when every MMA it tracks has started; otherwise a tracked
  MMA is an open MMA obligation of smaller rank (`commit_steps`). The commits of a thread deliver
  in issue order, as the commit-order assumption's constraint asks: a thread's commits all have
  `commitSpec`, so an earlier commit targets every rank a later one targets (`commit_prev`).

The sources of the loads and the MMAs are protocol facts (`AsyncSources`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW

noncomputable section
set_option maxRecDepth 100000

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The sources of the asynchronous operations**, for every maximal execution: the protocols'
facts that fix the inputs of the tensor loads and the MMAs. -/
structure AsyncSources (L : Launch) (mem0 : Mem0) : Prop where
  /-- The tensor loads' global bytes are fixed. -/
  tensor : ∀ X, Maximal L kernel asms mem0 X → TensorSources L mem0 X
  /-- The MMAs' shared operand bytes have ordered sources, no MMA reads a Tensor Memory A cell its
  accumulator's MMAs write, and the output layouts are injective. -/
  mma : ∀ X, Maximal L kernel asms mem0 X →
    OperandSourcesT L X ∧ TcMma.ATmemApart X ∧ TcMma.LayoutInjective X

/-- **Synchronization is guarded** in a safe execution: the successful polls spin, no write or
atomic releases, the kernel has no fence, and a faulting mbarrier record is unsafe. -/
theorem syncGuarded (hX : Consistent L kernel asms mem0 X) (hs : ¬ Unsafe L kernel asms mem0 X) :
    SyncGuarded L kernel X where
  spin _ _ _ _ _ _ he := Safety.poll_spins hX he
  noMemSync e f :=
    ⟨noSynchronizesWith_of (fun _ _ _ _ => no_release hX) (no_release_rmw hX) e f,
      not_fenceSync_of_noFence (no_threadFence hX) e f⟩
  noFault m _ _ r _ hr' _ _ _ := by
    cases hf : r.fault with
    | none => rfl
    | some f =>
      refine absurd ?_ hs
      exact .inr (.inr (.inr (.inr (.inr (.inl (.inl ⟨m, r, List.mem_of_getElem? hr',
        by simp [hf]⟩))))))

/-- The kernel issues no bulk copy, so no bulk obligation is open. -/
theorem bulk_steps (hX : Consistent L kernel asms mem0 X) (ho : Descent.Obl L X .bulk) :
    Sched.Steps (timed T Q L) mem0 X .bulk :=
  (ho fun _ _ ⟨_, he⟩ => (no_copy hX he).elim).elim

/-- The kernel issues no `cp.async.mbarrier.arrive`, so no arrive-on obligation is open. -/
theorem arriveOn_steps (hX : Consistent L kernel asms mem0 X) (ho : Descent.Obl L X .arriveOn) :
    Sched.Steps (timed T Q L) mem0 X .arriveOn :=
  (ho fun _ _ _ ⟨_, he⟩ => (Safety.no_asyncArrive hX he).elim).elim

/-- The kernel issues no tensor store, so no store obligation is open. -/
theorem store_steps (hX : Consistent L kernel asms mem0 X) (ho : Descent.Obl L X .store) :
    Sched.Steps (timed T Q L) mem0 X .store :=
  (ho fun _ _ _ ⟨_, he⟩ => (no_tensorStore hX he).elim).elim

/-- A maximal execution has notified every target of every CLC request. -/
theorem clc_steps (hmax : Maximal L kernel asms mem0 X) (ho : Descent.Obl L X .clc) :
    Sched.Steps (timed T Q L) mem0 X .clc :=
  (ho fun _ _ _ hi => Maximal.clc_notified_inOrder asms_wfStep hmax hi).elim

/-- **A maximal execution whose tensor loads' sources are fixed has completed every load.** -/
theorem tensor_steps (hmax : Maximal L kernel asms mem0 X) (hts : TensorSources L mem0 X)
    (ho : Descent.Obl L X .tensor) : Sched.Steps (timed T Q L) mem0 X .tensor :=
  (ho fun _ _ _ hi => Maximal.tensor_all_notified_inOrder asms_wfStep hmax hts hi).elim

/-- **A maximal execution whose MMAs' operands have sources has completed every MMA**; the kernel
issues no `tcgen05.cp` or `tcgen05.shift`. -/
theorem mma_steps (hmax : Maximal L kernel asms mem0 X) (hsg : SyncGuarded L kernel X)
    (hos : OperandSourcesT L X) (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    (ho : Descent.Obl L X .mma) : Sched.Steps (timed T Q L) mem0 X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_tmemA asms_wfStep hmax hsg hos hap hinj hm
  · exact (no_tcCp hmax.1 i c hc).elim
  · exact (no_tcShift hmax.1 i s hs).elim

/-- A thread's earlier commit targets every rank a later one targets: every commit of the kernel
has the specification `commitSpec` of its CTA (`Safety.commit_shape`: the MMA warp's), so all
commits of a thread target the same ranks. -/
theorem commit_prev (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) :
    ∀ (g j j' pc pc' : Nat) (sp sp' : TcCommit.Spec) (rank : Fin 16) (m : Loc),
      X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → (fun _ => true : Nat → Bool) pc = true →
      X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ → j < j' →
      TcCommit.target sp' rank = some m → ∃ m', TcCommit.target sp rank = some m' := by
  intro g j j' pc pc' sp sp' rank m he _ he' _ ht
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (.inr ⟨sp, rfl⟩)
  obtain ⟨d', P', -, hsh'⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he'
    (.inr ⟨sp', rfl⟩)
  obtain ⟨a, rfl⟩ := Safety.commit_shape hsh
  obtain ⟨a', rfl⟩ := Safety.commit_shape hsh'
  unfold TcCommit.target at ht ⊢
  simp only [commitSpec] at ht ⊢
  by_cases h0 : rank.val = 0
  · simp [h0]
  · have h1 : ¬ rank.val < 1 := by omega
    simp [h1] at ht

/-- **A commit's delivery steps**: when every MMA it tracks has started, the delivery happened in
a maximal execution, the commits of a thread delivering in issue order (as the commit-order
assumption's constraint asks); otherwise a tracked MMA is an open MMA obligation of smaller
rank. -/
theorem commit_steps (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hmax : Maximal L kernel asms mem0 X) (ho : Descent.Obl L X .commit) :
    Sched.Steps (timed T Q L) mem0 X .commit := by
  by_cases hs : ∀ i, (∃ c, AsyncCopy.TracksMma X i c) → X.async.mmaStarted i = true
  · refine (ho fun i s rank m hi ht => ?_).elim
    exact Maximal.commit_notified_inOrder asms_wfStep hmax (commit_prev hpre hmax.1 hf) hi ht
      fun x hx => hs x ⟨i, hx⟩
  · push Not at hs
    obtain ⟨x, ⟨c, hx⟩, hns⟩ := hs
    obtain ⟨-, -, hta, -⟩ := hx
    refine .inr ⟨X, .mma, hmax, fun hall => ?_, by simp [Sched.rank]⟩
    have hd := hall x hta
    have := hmax.1.tma.2.1.2 x hd
    rw [this] at hns
    exact hns rfl

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
