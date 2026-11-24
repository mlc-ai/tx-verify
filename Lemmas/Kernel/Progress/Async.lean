-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Step.TensorDrainInOrder
public import Lemmas.Step.StoreDoneInOrder
public import Lemmas.Step.MmaDrainTmemA
public import Lemmas.Order.GuardSnoc

@[expose] public section

/-! # The asynchronous obligations of a maximal execution

A proof tool, generic over the kernel (promoted from FA4's `Proof/Progress/Async.lean`). An open
asynchronous obligation of a maximal execution steps, given the protocol facts that fix the
inputs of the asynchronous operations:

* **tensor loads** (`Sched.tensor_steps`): a load whose global bytes are fixed (`TensorSources`)
  is completed by a maximal execution (`Maximal.tensor_all_notified_inOrder`);
* **tensor stores** (`Sched.store_steps`): a store whose staging bytes have visible sources
  (`StoreSources`) is completed once synchronization is guarded
  (`Step.StoreDone.pending_issue_visible_inOrder`);
* **MMAs** (`Sched.mma_steps`): an MMA whose operands have ordered sources (`OperandSourcesT`),
  that reads no Tensor Memory A cell its accumulator's MMAs write and whose layout is injective is
  completed once synchronization is guarded (`Maximal.mma_all_done_tmemA`), for a kernel without
  `tcgen05.cp` and `tcgen05.shift`;
* **bulk copies, arrive-ons** (`Sched.bulk_steps`, `Sched.arriveOn_steps`): none open for a kernel
  that issues none;
* **guarded synchronization** (`Sched.syncGuarded_of`): polls that spin, writes and atomics that
  do not release, no thread fence and fault-free mbarrier records.

A kernel that issues `cp.async` copies with arrive-ons (tml-fa4) proves its `arriveOn` obligation
from the asynchronous arrive-on drain of its copies; that case is not here. -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- Every tensor store is valid, reads no old destination bytes, and each byte it reads has a
visible source write whose byte is defined. -/
def StoreSources (L : Launch) (X : Execution) : Prop :=
  ∀ i a s, X.TensorStoreIssue i a s → TensorStore.Valid (i.1 / L.block) s ∧ s.reduce = none ∧
    Step.StoreDone.VisibleReadSources L X i s

/-- **Synchronization is guarded** when the successful polls spin, the writes and atomics do not
release, the kernel makes no thread fence and no mbarrier record faults. -/
theorem syncGuarded_of
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s)
    (hff : ∀ m r, r ∈ X.objects m → r.fault = none) : SyncGuarded L K X where
  spin := hspin
  noMemSync e f := ⟨noSynchronizesWith_of hnr hnrmw e f, not_fenceSync_of_noFence hnf e f⟩
  noFault m _ _ r _ hr' _ _ _ := hff m r (List.mem_of_getElem? hr')

/-- A kernel that issues no bulk copy has no open bulk obligation. -/
theorem bulk_steps (hno : ∀ i s, ¬ X.Copy i s) (ho : Descent.Obl L X .bulk) :
    Steps M mem0 X .bulk :=
  (ho fun i s h => (hno i s h).elim).elim

/-- A kernel that issues no `cp.async.mbarrier.arrive` has no open arrive-on obligation. -/
theorem arriveOn_steps (hno : ∀ i m noinc, ¬ X.AsyncArrive i m noinc)
    (ho : Descent.Obl L X .arriveOn) : Steps M mem0 X .arriveOn :=
  (ho fun i m n h => (hno i m n h).elim).elim

/-- **A maximal execution whose tensor loads' sources are fixed has completed every load.** -/
theorem tensor_steps {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hts : TensorSources L mem0 X)
    (ho : Descent.Obl L X .tensor) : Steps M mem0 X .tensor :=
  (ho fun _ _ _ hi => Maximal.tensor_all_notified_inOrder hA hmax hts hi).elim

/-- **An open store obligation steps**: an issued tensor store not fully done, whose bytes have
visible sources, extends the execution by a counted step. -/
theorem store_steps {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hss : StoreSources L X)
    (ho : Descent.Obl L X .store) : Steps M mem0 X .store := by
  obtain ⟨i, a, s, hi, hn⟩ : ∃ i a s, X.TensorStoreIssue i a s ∧
      ¬ ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true := by
    by_contra hc
    push Not at hc
    exact ho fun i a s hi => hc i a s hi
  obtain ⟨hv, hred, hsrc⟩ := hss i a s hi
  exact .inl (Step.StoreDone.pending_issue_visible_inOrder hA hmax.1 ⟨a, hi⟩ hv hn hsrc hsg hred)

/-- **A maximal execution whose MMAs' operands have sources has completed every MMA**, for a
kernel without `tcgen05.cp` and `tcgen05.shift`. -/
theorem mma_steps {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    (hcp : ∀ e c, ¬ X.CpIssue e c) (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (ho : Descent.Obl L X .mma) : Steps M mem0 X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_tmemA hA hmax hsg hos hap hinj hm
  · exact (hcp i c hc).elim
  · exact (hsh i s hs).elim

end

end PTX.Sched
