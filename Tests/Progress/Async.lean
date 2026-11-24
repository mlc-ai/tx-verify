-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Async

/-! # The asynchronous obligations of a maximal execution, dispatched

For a kernel without bulk copies, arrive-ons, copies or shifts into Tensor Memory, and thread
fences, with spinning polls, non-releasing writes and fault-free mbarrier records, every open
tensor-load, tensor-store, MMA, bulk or arrive-on obligation of a maximal execution steps, given
the protocols' source facts. -/

namespace PTX.Tests.Async
open PTX PTX.Sched

example {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
    {X : Execution} {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s) (hff : ∀ m r, r ∈ X.objects m → r.fault = none)
    (hbulk : ∀ i s, ¬ X.Copy i s) (harr : ∀ i m noinc, ¬ X.AsyncArrive i m noinc)
    (hcp : ∀ e c, ¬ X.CpIssue e c) (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (hts : TensorSources L mem0 X) (hss : StoreSources L X) (hos : OperandSourcesT L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X) {o : Descent.Obligation}
    (hk : o = .tensor ∨ o = .store ∨ o = .mma ∨ o = .bulk ∨ o = .arriveOn)
    (ho : Descent.Obl L X o) : Steps M mem0 X o := by
  have hsg := syncGuarded_of (L := L) hspin hnr hnrmw hnf hff
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact tensor_steps hA hmax hts ho
  · exact store_steps hA hmax hsg hss ho
  · exact mma_steps hA hmax hsg hos hap hinj hcp hsh ho
  · exact bulk_steps hbulk ho
  · exact arriveOn_steps harr ho

end PTX.Tests.Async
