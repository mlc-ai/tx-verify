-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Bound

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

/-- A counted event strictly decreases the rank before every later live state.
This permits counting visits to a site without extending the thread ledger. -/
theorem later_rank {Q L m X g j k d s e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,j)=some e) (counts : e.counts=true)
    (first : stateAt (thread Q L) X g j=some (some d)) (before : j<k)
    (len : k≤(X.tr g).length) (last : stateAt (thread Q L) X g k=some (some s)) :
    threadRank s < threadRank d := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    have get := List.getElem?_eq_getElem (l := X.tr g) (i := k) (by omega)
    rw [stateAt_succ get] at last
    rcases hs : stateAt (thread Q L) X g k with _|_|old <;> rw [hs] at last <;>
      try solve | cases last
    have inv := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX get) hs).1
    have le := rank_next hp hX hf words get hs inv last
    by_cases eq : j=k
    · subst k
      rw [first] at hs
      cases hs
      have ev := Option.some.inj (get.symm.trans he)
      rw [ev,counts] at le
      exact le
    · have strict := ih (by omega) (by omega) hs
      omega

/-- At a site of fixed rank, any earlier counted event with that same rank is impossible. -/
theorem no_earlier_at_rank {Q L m X g k e d N} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some e) (live : stateAt (thread Q L) X g k=some (some d))
    (rank : threadRank d=N) (p : Event → Bool)
    (prior : ∀ {j v}, X.get (g,j)=some v → p v → v.counts ∧
      ∃ s, stateAt (thread Q L) X g j=some (some s) ∧ threadRank s=N) :
    ((X.tr g).take k).countP p=0 := by
  apply List.countP_eq_zero.mpr
  intro v hv yes
  obtain ⟨j,get⟩ := List.mem_iff_getElem?.mp hv
  have before := (List.getElem?_eq_some_iff.mp get).1
  rw [List.length_take] at before
  have lt : j<k := by omega
  rw [List.getElem?_take_of_lt lt] at get
  obtain ⟨ct,s,ls,rs⟩ := prior get yes
  have strict := later_rank hp hX hf words get ct ls lt (List.getElem?_eq_some_iff.mp he).1.le live
  omega

end PTX.Kernels.InklingRelDecode.Proof
