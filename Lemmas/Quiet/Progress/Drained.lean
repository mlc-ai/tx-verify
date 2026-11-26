-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.StoreDrain
public import Lemmas.Quiet.Progress.Async

@[expose] public section

/-! # A maximal execution has drained its tensor stores

The premise of an exit step under a store-drain assumption (`TensorStore.Drained`) holds of every
thread of a maximal execution whose tensor stores' bytes have visible sources: a store whose
reads have not completed has not fully completed (`TensorStore.CopyOk.complete`), and such a store
extends the execution (`Step.StoreDone.pending_issue_visible_inOrderQ`). -/

namespace PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- **Every thread of a maximal execution has drained its tensor stores**, when the stores' bytes
have visible sources. -/
theorem Maximal.drainedQ (hA : Assumption.WfQuiet sel L K mem0 A) (hmax : Maximal L K A mem0 X)
    (hsg : SyncGuarded L K X) (hss : Sched.StoreSources L X) (select : Nat → Bool) (g : Nat) :
    TensorStore.Drained select X g := by
  intro i _ ⟨pc, a, s, hi, _⟩
  by_contra hn
  have hfull : ¬ ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true :=
    fun ⟨o, ho, hf⟩ => hn ⟨o, ho, ((hmax.1.store i o ho).2.2.complete hf).1⟩
  obtain ⟨hv, hred, hsrc⟩ := hss i a s ⟨pc, hi⟩
  exact hmax.not_grows
    (Step.StoreDone.pending_issue_visible_inOrderQ hA hmax.1 ⟨a, pc, hi⟩ hv hfull hsrc hsg hred)

end PTX
