-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # A use with an enabling chain to an exit

`SharedEnabled L K A X c e`: the use `e` is present and its completion has an enabling chain
(`EnabledBefore`) to the issue of an exit of CTA `c`. Such a use is finished
(`SharedEnabled.finished`), and the arrive-on of a commit at a site a kernel assumption selects
with `commitInOrder` is enabled once the arrive-on at the same rank of the thread's next commit is
(`SharedEnabled.of_commit_next`): the assumption's edge, then the next arrive-on's chain. -/

namespace PTX
open AsyncCopy

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- **A present use with an enabling chain to an exit of CTA `c`.** -/
def SharedEnabled (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (c : Nat)
    (e : Ref) : Prop :=
  X.RefPresent e ∧ ∃ finish, OwnerExit L X c finish ∧
    EnabledBefore L K A X e (.thread finish, false)

/-- **An enabled use is finished.** -/
theorem SharedEnabled.finished {c : Nat} {e : Ref} (h : SharedEnabled L K A X c e) :
    SharedFinished L K A X e c := by
  obtain ⟨hp, finish, hExit, hE⟩ := h
  exact SharedFinished.of_completedBefore hp hExit hE.completedBefore

/-- **An enabled next commit's arrive-on enables the earlier one's**, at a site the assumption
selects. -/
theorem SharedEnabled.of_commit_next {c : Nat} {i j : EvId} {r : Fin 16}
    (hn : CommitNext A X (.async i (.tcNotify r)) (.async j (.tcNotify r)))
    (h : SharedEnabled L K A X c (.async j (.tcNotify r))) :
    SharedEnabled L K A X c (.async i (.tcNotify r)) := by
  have hn' := hn
  simp only [CommitNext] at hn'
  obtain ⟨-, -, -, hpi, hpj, -, -, -⟩ := hn'
  obtain ⟨-, finish, hx, hE⟩ := h
  refine ⟨hpi, finish, hx, ?_⟩
  rcases hE with ⟨o, ho, hch⟩ | ⟨j', p, w, o, he, hobs, ho, hch⟩
  · exact .inl ⟨o, ho, .head (Or.inr (Or.inr ⟨rfl, rfl, .inl hn⟩))
      (.head (Or.inl (DepStep.node hpj)) hch)⟩
  · obtain ⟨rfl, rfl⟩ := Ref.async.inj he
    exact .inl ⟨o, ho, .head (Or.inr (Or.inr ⟨rfl, rfl, .inl hn⟩))
      (.head (Or.inl (DepStep.of_witness L hobs)) hch)⟩

end

end PTX
