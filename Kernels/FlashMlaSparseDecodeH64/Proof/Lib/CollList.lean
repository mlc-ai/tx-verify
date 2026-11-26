-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-! # The warp collectives of a warp, in order

`collList w`: the pcs of the collectives warp `w` performs, in the order of its code, up to the
index warp's loops (warp 7 lists its straight-line prefix; its loops are `Index/Coll.lean`'s).
Warps 0 and 1 elect in warpgroup 0's four output chunks; warp 0 also in the startup. The number
of collectives a state at pc `pc` has made is `ncW w pc`, the list's entries below the pc. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- **The pcs of warp `w`'s warp collectives**, in order. -/
def collList (w : Nat) : List Nat :=
  if w = 0 then [6, 9, 16, 31, 1350, 1507, 1664, 1822]
  else if w = 1 then [6, 9, 1350, 1507, 1664, 1822]
  else if w = 4 then [6, 9, 1843, 1853]
  else if w = 5 then [6, 9, 1843, 2165]
  else if w = 6 ∨ w = 7 then [6, 9, 1843]
  else [6, 9]

/-- The collectives of warp `w` before pc `pc`. -/
def ncW (w pc : Nat) : Nat := ((collList w).filter (· < pc)).length

theorem collList_sorted (w : Nat) : (collList w).Pairwise (· < ·) := by
  unfold collList
  repeat' split
  all_goals decide

/-- **The entry of the list at the count of a pc is the pc exactly when the list has it.** -/
theorem getElem_ncW {l : List Nat} (hs : l.Pairwise (· < ·)) {pc : Nat} :
    l[(l.filter (· < pc)).length]? = some pc ↔ pc ∈ l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    by_cases ha : a < pc
    · simp only [List.filter_cons, decide_eq_true ha, ite_true, List.length_cons,
        List.getElem?_cons_succ]
      rw [ih hs.2]
      constructor
      · exact List.mem_cons_of_mem a
      · intro h
        rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
    · have hnil : t.filter (· < pc) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        have := hs.1 c hc
        simp only [decide_eq_true_eq]
        omega
      simp only [List.filter_cons, decide_eq_true_eq, ha, ite_false, hnil, List.length_nil,
        List.getElem?_cons_zero, Option.some.injEq, List.mem_cons]
      constructor
      · exact fun h => .inl h.symm
      · rintro (h | h)
        · exact h.symm
        · have := hs.1 pc h
          omega

theorem getElem_ncW_coll (w pc : Nat) : (collList w)[ncW w pc]? = some pc ↔ pc ∈ collList w :=
  getElem_ncW (collList_sorted w)

theorem ncW_nine (w : Nat) : ncW w 9 = 1 := by
  unfold ncW collList
  repeat' split
  all_goals decide

/-- Warp 0 has made four collectives between the startup's elections and its output chunks. -/
theorem ncW_zero_mid {pc : Nat} (h1 : 31 < pc) (h2 : pc ≤ 1350) : ncW 0 pc = 4 := by
  unfold ncW collList
  simp only [ite_true]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  repeat' split
  all_goals simp_all
  all_goals omega

/-- The warps' counts at the barrier after the startup and at their warpgroup's first pc agree. -/
theorem ncW_entry : ∀ w < 12,
    ncW w 97 = ncW w (if w < 4 then 103 else if w < 8 then 1842 else 2606) := by
  decide

theorem ncW_ninetyseven (w : Nat) : ncW w 97 = if w = 0 then 4 else 2 := by
  unfold ncW collList
  repeat' split
  all_goals simp_all (config := {decide := true})

/-- Warpgroup 2's warps' lists are the startup's two shuffles. -/
theorem collList_dq {w : Nat} (h8 : 8 ≤ w) (h12 : w < 12) : collList w = [6, 9] := by
  unfold collList
  repeat' split
  all_goals first | rfl | omega

theorem ncW_dq {w pc : Nat} (h8 : 8 ≤ w) (h12 : w < 12) :
    ncW w pc = (if 6 < pc then 1 else 0) + (if 9 < pc then 1 else 0) := by
  unfold ncW
  rw [collList_dq h8 h12]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  repeat' split
  all_goals simp_all

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
