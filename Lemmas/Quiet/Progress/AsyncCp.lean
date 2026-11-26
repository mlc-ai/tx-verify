-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.AsyncCp
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Step.DrainInOrder

@[expose] public section

/-! # Commit obligations step under quiet extensions

`Sched.commit_steps` under `Assumption.WfQuiet`. -/

namespace PTX.Sched
open PTX AsyncCopy

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **A maximal execution has performed every commit's arrive-ons**, when every MMA has its operand
snapshot and a thread's earlier commits at the sites in `sel` target the ranks of its later ones. -/
theorem commit_stepsQ {sel : Nat → Bool} (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hst : ∀ x i, TracksMma X x i → X.async.mmaStarted x = true)
    (hprev : ∀ (g j j' pc pc' : Nat) (sp sp' : TcCommit.Spec) (rank : Fin 16) (m : Loc),
      X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → sel pc = true →
      X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ → j < j' →
      TcCommit.target sp' rank = some m → ∃ m', TcCommit.target sp rank = some m')
    (ho : Descent.Obl L X .commit) : Steps M mem0 X .commit :=
  (ho fun _ _ _ _ hi ht => Maximal.commit_notified_inOrderQ hA hmax hprev hi ht
    fun x hx => hst x _ hx).elim

end PTX.Sched
