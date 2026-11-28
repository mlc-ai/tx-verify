-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CountNth
public import Lemmas.Kernel.Progress.NextEv

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Sched

theorem count_of_occurrences {X : Execution} {g n : Nat} {f : Event → Bool}
    (label : Nat → Event → Nat)
    (hits : ∀ i : Fin n, ∃ k e, X.get (g,k)=some e ∧ f e ∧ label k e=i.val) :
    n≤(X.tr g).countP f := by
  classical
  choose idx ev get use tag using hits
  have bound : (Finset.univ (α := Fin n)).card ≤ ((Finset.range (X.tr g).length).filter
      fun k => ((X.tr g)[k]?).any f).card := by
    apply Finset.card_le_card_of_injOn idx
    · intro i _
      have atIdx : (X.tr g)[idx i]?=some (ev i) := get i
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp atIdx).1,
        by simpa only [atIdx,Option.any_some] using use i⟩
    · intro i _ j _ equal
      have a := get i
      rw [equal,get j] at a
      apply Fin.ext
      rw [←tag i,←tag j,equal,Option.some.inj a]
  rw [←MbarRing.Slot.countP_take_card,List.take_length] at bound
  simpa using bound

/-- After the last real slot there are no waiters. Assign this suffix a
time beyond the producer clock so the unconditional early row still holds. -/
theorem producer_lag {K A L} (M : Timed K A L) (X : Execution) (m : Loc)
    (y δ U : Nat) (slot : Nat → Nat) (cons : Nat → Prop) (cnt : Event → Bool)
    (mono : Monotone slot) (wait : ∀ g, cons g →
      let j := okPolls m (X.tr g)
      j<U+δ ∧ slot j≤threadTime M X g)
    (due : ∀ j<U, (∃ k pc, X.get (y,k)=some ⟨pc,.exit⟩) ∨
      slot (j+δ)≤threadTime M X y → j+1≤(X.tr y).countP cnt) :
    ∃ τ, LagN M X m δ (·=y) cons τ U cnt := by
  let late := max (slot (U+δ)) (threadTime M X y)+1
  refine ⟨fun j => if j<U+δ then slot j else late,?_,?_,?_,?_,fun g h => (wait g h).1⟩
  · intro a b ab
    split_ifs <;> first | exact mono ab | omega |
      (apply Nat.le_trans (mono (show a≤U+δ by omega)); dsimp [late]; omega)
  · intro g h
    rw [ite_eq_left (wait g h).1]
    exact (wait g h).2
  · rintro _ rfl _
    split
    · rename_i short
      by_contra! behind
      have := due _ (by omega) (.inr behind)
      omega
    · dsimp [late]; omega
  · rintro _ k pc rfl ex
    by_contra! short
    have := due _ short (.inl ⟨k,pc,ex⟩)
    omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
