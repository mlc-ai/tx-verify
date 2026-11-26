-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Async
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Step.TensorDrainInOrder
public import Lemmas.Quiet.Step.StoreDoneInOrder
public import Lemmas.Quiet.Step.MmaDrainTmemA

@[expose] public section

/-! # Asynchronous obligations step under quiet extensions

`Lemmas/Kernel/Progress/Async.lean` under `Assumption.WfQuiet`. -/

namespace PTX.Sched
open PTX
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **A maximal execution whose tensor loads' sources are fixed has completed every load.** -/
theorem tensor_stepsQ {sel : Nat → Bool} (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hts : TensorSources L mem0 X)
    (ho : Descent.Obl L X .tensor) : Steps M mem0 X .tensor :=
  (ho fun _ _ _ hi => Maximal.tensor_all_notified_inOrderQ hA hmax hts hi).elim

/-- **An open store obligation steps**: an issued tensor store not fully done, whose bytes have
visible sources, extends the execution by a counted step. -/
theorem store_stepsQ {sel : Nat → Bool} (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hss : StoreSources L X)
    (ho : Descent.Obl L X .store) : Steps M mem0 X .store := by
  obtain ⟨i, a, s, hi, hn⟩ : ∃ i a s, X.TensorStoreIssue i a s ∧
      ¬ ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true := by
    by_contra hc
    push Not at hc
    exact ho fun i a s hi => hc i a s hi
  obtain ⟨hv, hred, hsrc⟩ := hss i a s hi
  exact .inl (Step.StoreDone.pending_issue_visible_inOrderQ hA hmax.1 ⟨a, hi⟩ hv hn hsrc hsg hred)

/-- **A maximal execution whose MMAs' operands have sources has completed every MMA**, for a
kernel without `tcgen05.cp` and `tcgen05.shift`. -/
theorem mma_stepsQ {sel : Nat → Bool} (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    (hcp : ∀ e c, ¬ X.CpIssue e c) (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (ho : Descent.Obl L X .mma) : Steps M mem0 X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_tmemAQ hA hmax hsg hos hap hinj hm
  · exact (hcp i c hc).elim
  · exact (hsh i s hs).elim

end

end PTX.Sched
