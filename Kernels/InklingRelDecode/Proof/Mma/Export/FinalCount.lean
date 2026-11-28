-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.Successor
import Kernels.InklingRelDecode.Proof.Common.RankOrder

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private theorem final_rank {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨2553,.tc (.commit sp)⟩) :
    ∃ d, stateAt (thread Q L) X g k=some (some d) ∧ threadRank d=11 := by
  obtain ⟨_,_,_,d,_,hs,pc⟩ := mma_state hp hX hf get (by simp)
    (by decide : 2422<2553) (by decide : 2553<2557)
  have only (s : Site) : 2553=s.pc → s=.finCommit := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨s,i,v⟩ := d
  obtain rfl := only s pc
  exact ⟨_,hs,rfl⟩

/-- The final commit is issued at most once by each lane on any consistent prefix. -/
public theorem final_first {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (get : X.get (g,k)=some ⟨2553,.tc (.commit sp)⟩) :
    ∀ j<k, ∀ a, X.get (g,j)≠some ⟨2553,.tc (.commit a)⟩ := by
  intro j before a first
  obtain ⟨d,hs,rank⟩ := final_rank hp hX hf get
  obtain ⟨s,ls,rs⟩ := final_rank hp hX hf first
  have strict := later_rank hp hX hf words first rfl ls before
    (List.getElem?_eq_some_iff.mp get).1.le hs
  omega

private theorem issue_site (s : Site) (h : s.pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
      2530,2533,2535,2537,2539,2541,2543,2545]) :
    (∃ j, s = .qk j) ∨ ∃ j, s = .pv j := by
  cases s <;> first | exact .inl ⟨_,rfl⟩ | exact .inr ⟨_,rfl⟩ | exact absurd h (by decide +kernel)

/-- **Every MMA issue of a lane is before its final commit**: the final commit's state has the
least rank, below every issue site. -/
public theorem mma_before_final {Q L m X g k sp k' pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (get : X.get (g,k)=some ⟨2553,.tc (.commit sp)⟩)
    (hx : X.get (g,k')=some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (issue : pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
      2530,2533,2535,2537,2539,2541,2543,2545]) : k' < k := by
  by_contra! le
  rcases Nat.eq_or_lt_of_le le with rfl|lt
  · rw [get] at hx
    cases hx
  obtain ⟨d,hs,rank⟩ := final_rank hp hX hf get
  have range : 2422 < pc ∧ pc < 2557 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at issue
    omega
  obtain ⟨w,x,r,e,n,hs',pcs⟩ := mma_state hp hX hf hx (fun _ => nofun) range.1 range.2
  have lr := later_rank hp hX hf words get rfl hs lt (List.getElem?_eq_some_iff.mp hx).1.le hs'
  have inv : Mma.Inv e := (reached_table hf (lt_of_get hX hx) (noUbBefore_of_get hX hx) hs').1.1
  obtain ⟨st,i,v⟩ := e
  change pc = st.pc at pcs
  rw [rank] at lr
  rcases issue_site st (pcs ▸ issue) with ⟨j,rfl⟩ | ⟨j,rfl⟩ <;>
    simp only [threadRank,workerRank,Mma.measure,Mma.Site.position] at lr <;>
    simp only [Mma.Inv] at inv <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
