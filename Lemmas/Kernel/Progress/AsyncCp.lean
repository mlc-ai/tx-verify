-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Async
public import Lemmas.Protocol.CpAsyncArriveOrder
public import Lemmas.Protocol.CpAsyncCompletionOrder

@[expose] public section

/-! # The `cp.async` and commit obligations of a maximal execution

A proof tool, generic over the kernel, beside `Async.lean`:

* **`cp.async` copies** (`Sched.bulk_steps_cp`): whole copies of initial, unwritten bytes that no
  group wait covers (`CpSources`) are completed by a maximal execution;
* **arrive-ons** (`Sched.arriveOn_steps_cp`): an arrive-on of no pending increment is performed once
  the copies it tracks are written, so a maximal execution with `CpSources` has performed it;
* **commits** (`Sched.commit_steps`): when every MMA has its operand snapshot, a maximal execution
  has performed every commit's arrive-ons. -/

namespace PTX.Sched

open PTX AsyncCopy

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- Every linear copy is a whole `cp.async` copy of initial bytes that no write covers, and no group
wait covers it. -/
def CpSources (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ i spec, X.Copy i spec → spec.completion = .asyncGroup ∧ spec.writes = .whole ∧
    spec.data = none ∧ (∀ k w, ¬ GroupWaitsFor X k i w) ∧ spec.src.size ≤ spec.dst.size ∧
    (∀ k < spec.src.size, mem0 (spec.src.loc.at k) ≠ none) ∧
    ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k)

/-- A maximal execution has written every `cp.async` copy. -/
theorem cp_written {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hcp : CpSources mem0 X) {i : EvId} {spec : AsyncCopy.Spec}
    (hi : X.Copy i spec) : (X.async.copies i).writeBytes.isSome := by
  obtain ⟨hc, hw, hd, hno, hsize, ha, hsrc⟩ := hcp i spec hi
  cases hn : (X.async.copies i).writeBytes with
  | none =>
    exact (hmax.not_grows (pending_cpAsync_extendsInOrder hA hmax.1 hi hc hw hd hn hno hsize ha
      hsrc)).elim
  | some bytes => rfl

/-- **A maximal execution whose copies' sources are fixed has completed every copy.** -/
theorem bulk_steps_cp {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hcp : CpSources mem0 X) (ho : Descent.Obl L X .bulk) :
    Steps M mem0 X .bulk := by
  refine (ho fun i s hi => ?_).elim
  rw [(hcp i s hi).1]
  exact cp_written hA hmax hcp hi

/-- **A maximal execution whose copies' sources are fixed has performed every arrive-on**, when
every arrive-on makes no increment. -/
theorem arriveOn_steps_cp {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hcp : CpSources mem0 X)
    (hno : ∀ i m, ¬ X.AsyncArrive i m false) (ho : Descent.Obl L X .arriveOn) :
    Steps M mem0 X .arriveOn := by
  refine (ho fun i m noinc hi => ?_).elim
  cases noinc with
  | false => exact (hno i m hi).elim
  | true =>
    cases hn : X.async.arrived i with
    | true => rfl
    | false =>
      exact (hmax.not_grows (pending_cpAsyncArrive_extendsInOrder hA hmax.1 hi hn
        fun j ⟨_, _, ⟨s, hs, _⟩, _⟩ => cp_written hA hmax hcp hs)).elim

/-- **A maximal execution has performed every commit's arrive-ons**, when every MMA has its operand
snapshot and a thread's earlier commits at the sites in `sel` target the ranks of its later ones. -/
theorem commit_steps {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hst : ∀ x i, TracksMma X x i → X.async.mmaStarted x = true)
    (hprev : ∀ (g j j' pc pc' : Nat) (sp sp' : TcCommit.Spec) (rank : Fin 16) (m : Loc),
      X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → sel pc = true →
      X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ → j < j' →
      TcCommit.target sp' rank = some m → ∃ m', TcCommit.target sp rank = some m')
    (ho : Descent.Obl L X .commit) : Steps M mem0 X .commit :=
  (ho fun _ _ _ _ hi ht => Maximal.commit_notified_inOrder hA hmax hprev hi ht
    fun x hx => hst x _ hx).elim

end PTX.Sched
