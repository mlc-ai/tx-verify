-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- The eight tensor-load sites of the loader's iteration, in issue order. -/
abbrev copyPcs : List Nat := [2389,2391,2394,2396,2404,2406,2410,2412]

/-- The place of a loader copy site among the eight copies of an iteration. -/
def copyIndex (pc : Nat) : Nat := copyPcs.idxOf pc

theorem copyIndex_lt {pc : Nat} (h : pc ∈ copyPcs) : copyIndex pc < 8 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem copyIndex_inj {pc pc' : Nat} (h : pc ∈ copyPcs) (h' : pc' ∈ copyPcs)
    (eq : copyIndex pc = copyIndex pc') : pc = pc' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h h'
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact absurd eq (by decide)

/-- The byte offset of each copy's 8192-byte box from `sharedBase + 32768 * slot`. -/
def copyOff (pc : Nat) : Nat := [0,16384,98304,114688,8192,24576,106496,122880][copyIndex pc]!

theorem copyOff_apart {pc pc' : Nat} (h : pc ∈ copyPcs) (h' : pc' ∈ copyPcs) (ne : pc ≠ pc') :
    copyOff pc + 8192 ≤ copyOff pc' ∨ copyOff pc' + 8192 ≤ copyOff pc := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h h'
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact absurd rfl ne | decide

/-- Visits to ring slot `s` among `n` consecutive iterations starting at iteration `a`. -/
def ringVisits (a n : Nat) (s : Fin 3) : Nat := (a+n+2-s.val)/3 - (a+2-s.val)/3

theorem ringVisits_succ (a n : Nat) (s : Fin 3) :
    ringVisits a (n+1) s = ringVisits a n s + if (a+n)%3 = s.val then 1 else 0 := by
  unfold ringVisits
  have hs := s.isLt
  split <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Iface
