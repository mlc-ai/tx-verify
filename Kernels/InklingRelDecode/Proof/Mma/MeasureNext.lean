-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Measure

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

private theorem next_iter {s i v} (lo : i≤D.limit ⟨s,i,v⟩) :
    measure (iterNext ⟨s,i,v⟩)<30*(D.limit ⟨s,i,v⟩+1-i) := by
  by_cases h : i=low v
  · simp [iterNext,D.limit,measure,h]
  · by_cases h' : i+1<low v <;>
      simp only [iterNext,D.limit,h,h',↓reduceIte,measure,Site.position] at * <;> omega

private theorem after_qk {s i v} (lo : i<D.limit ⟨s,i,v⟩) (pos : s.position<14)
    (eq : measure ⟨s,i,v⟩=30*(D.limit ⟨s,i,v⟩+1-i)+(28-s.position)) :
    measure (afterQk ⟨s,i,v⟩)<measure ⟨s,i,v⟩ := by
  unfold afterQk
  split
  · have := next_iter lo.le
    omega
  · rw [eq]
    change 30*(low v+1-i)+(28-14)<30*(low v+1-i)+(28-s.position)
    omega

theorem measure_next {L g d dn ev} (hi : Inv d) (step : next L g d ev=some (some dn)) :
    measure dn+ev.counts.toNat≤measure d := by
  have cnt : ev.counts.toNat≤1 := by cases ev.counts <;> decide
  obtain ⟨s,i,v⟩ := d
  cases s
  case ldNum =>
    simp only [next] at step
    split at step <;> try contradiction
    rename_i bs _
    cases h : (rebuild 3 bs).toOption <;> simp [h] at step
    cases step
    have := low_lt v
    rename_i w
    have := low_lt w
    simp only [measure,D.limit]
    omega
  case' kvWait | pWait =>
    simp only [next] at step
    split at step <;> try contradiction
    rename_i l q ok a sc kind
    split at step
    · cases step
      simp only [measure,Site.position,D.limit]
      omega
    · cases step
      have no : ev.counts=false := by
        cases ev; simp_all [Event.counts]
      simp [no]
  all_goals simp only [next,issueNext,startSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first
    | (apply Nat.le_trans (Nat.add_le_add_left cnt _) (Nat.succ_le_of_lt
        (after_qk hi.1 (by decide) rfl)))
    | (have small := next_iter hi.2.1; simp only [measure,Site.position] at *; omega)
    | (simp only [measure,Site.position,Inv,D.limit] at *; omega)

end PTX.Kernels.InklingRelDecode.Proof.Mma
